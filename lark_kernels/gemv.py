"""Full-size FP16 GEMV certificates by counted-loop and grid-fold induction."""

import ast
from dataclasses import replace
import json
from pathlib import Path
import sysconfig

from . import pointwise
from .certificate import LAKEFILE, TOOLCHAIN, digest, lean_binary, model_path, run_lean, write_json
from .frontend import translate
from .ir import Buffer, Refusal, Task, lean_list, lean_node, node
from .spec import read_spec

PROFILE = "gemv-induction-v4"
FILES = pointwise.FILES


def reduction_path():
    repo = Path(__file__).resolve().parent.parent / "lean/Lark/Reduction.lean"
    if repo.exists():
        return repo
    installed = Path(sysconfig.get_path("data")) / "share/lark/lean/Lark/Reduction.lean"
    if installed.exists():
        return installed
    raise Refusal("installation", "pinned reduction proof library is missing")


def parse_task(source):
    d = json.loads(source)
    buffers = d["buffers"]
    if len(buffers) != 3 or [b["role"] for b in buffers] != ["input", "input", "output"]:
        raise Refusal("gemv", "expected two inputs and one output")
    if any(
        b["dtype"] != "float16"
        or not isinstance(b["shape"], list)
        or len(b["shape"]) != 2
        or any(type(x) is not int or x <= 0 for x in b["shape"])
        for b in buffers
    ):
        raise Refusal("gemv", "expected positive rank-two FP16 shapes")
    n, k = buffers[0]["shape"]
    if n * k >= 2147483648 or buffers[1]["shape"] != [k, 1] or buffers[2]["shape"] != [n, 1]:
        raise Refusal("gemv", "expected [M,K] @ [K,1] -> [M,1], M*K < 2^31")
    language = d.get("language", "cuda")
    warp = 32 if language == "cuda" else 64
    if d["launch"] != {"grid": n, "block": 1, "warp": warp} or any(
        type(value) is not int for value in d["launch"].values()
    ):
        raise Refusal("gemv", "expected one thread per row, native warp width")
    fuel = d.get("fuel", [4 * k + 6, 1, 1, 1])
    if fuel != [4 * k + 6, 1, 1, 1] or any(type(value) is not int for value in fuel):
        raise Refusal("gemv", "fuel must be [4*K+6,1,1,1]")
    small = json.loads(source)
    small["launch"]["grid"] = 1
    small["fuel"] = fuel
    for b in small["buffers"]:
        b["shape"] = [1, 1]
    checked = Task.parse(json.dumps(small))
    return replace(
        checked,
        grid=n,
        buffers=tuple(Buffer(b["name"], b["role"], tuple(b["shape"]), b["dtype"]) for b in buffers),
    )


def expected_program(k):
    ix, j = node("ivar", 0), node("ivar", 1)
    product = node(
        "bin",
        "mul",
        node(
            "un",
            "fromHalf",
            node("load", "global", 0, node("add", node("mul", ix, node("const", k)), j)),
        ),
        node("un", "fromHalf", node("load", "global", 1, j)),
    )
    return [
        node("idx", 0, node("bid")),
        node("set", 0, node("lit", 0, 1)),
        node("idx", 1, node("const", 0)),
        node("branch", node("lt", j, node("const", k)), 7),
        node("set", 0, node("bin", "add", node("reg", 0), product)),
        node("idx", 1, node("add", j, node("const", 1))),
        node("jump", 3),
        node("store", "global", 2, ix, node("un", "toHalf", node("reg", 0))),
        node("halt"),
    ]


def prepare(source, reference, task_source):
    task = parse_task(task_source)
    tr = translate(source, task)
    n, k = task.buffers[0].shape
    if tr.shared or tr.program != expected_program(k):
        raise Refusal("gemv", "source differs from the proved counted-loop profile")
    small = replace(task, grid=1, buffers=tuple(replace(b, shape=(1, 1)) for b in task.buffers))
    # Validate imports, binding, dtype, arguments and module syntax using the
    # existing reader, then restrict the body to a shape-independent matmul.
    read_spec(reference, small)
    fn = next(s for s in ast.parse(reference).body if isinstance(s, ast.FunctionDef))
    if (
        len(fn.body) != 1
        or not isinstance(fn.body[0], ast.Return)
        or fn.returns is not None
        or any(a.annotation is not None for a in fn.args.args)
    ):
        raise Refusal("gemv-reference", "expected one pure matrix-vector return")
    a, b = [buffer.name for buffer in task.buffers[:2]]
    canonical = ast.parse(f"({a}.float() @ {b}.float()).half()", mode="eval").body
    if ast.dump(fn.body[0].value) != ast.dump(canonical):
        raise Refusal("gemv-reference", "expected (A.float() @ X.float()).half()")
    return task, tr


def model_hashes():
    return {**pointwise.model_hashes(), "reduction": digest(reduction_path().read_bytes())}


def render(task, tr):
    n, k = task.buffers[0].shape
    base = model_path(True).read_text()
    pw = pointwise.induction_path().read_text().removeprefix("import Lark.Nonlinear\n")
    reduction = reduction_path().read_text()
    if not reduction.startswith("import Lark.Pointwise\n"):
        raise Refusal("installation", "unexpected reduction library import")
    return (
        base
        + "\n"
        + pw
        + "\n"
        + reduction.removeprefix("import Lark.Pointwise\n")
        + f"""
namespace LarkCertificate
open LarkNonlinear
def layout : Layout := LarkReduction.layout {n} {k}
def geometry : Geometry := LarkReduction.geometry {n} {task.warp}
def fuel : Fuel := LarkReduction.fuel {k}
def program : List Instr := {lean_list(lean_node(i) for i in tr.program)}
def spec (ops : Ops α) (input : Nat → Nat → α) : List α :=
  LarkReduction.matrixSpec ops {n} {k} input
def finalState (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) : State α :=
  LarkReduction.partialState ops input outside {n} {k} {n}
theorem segmentation_data : program = LarkReduction.program {k} := by rfl
theorem segmentation (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) :
    runLaunch ops layout geometry fuel program (initial layout input outside) =
      some (finalState ops input outside) := by
  rw [segmentation_data]
  exact LarkReduction.launch_eq ops input outside {n} {k} {task.warp}
    (by decide) (by decide) (by decide) (by decide)
theorem race_free (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) :
    raceFree geometry (finalState ops input outside).trace = true := by
  exact LarkReduction.owned_raceFree geometry _
    (LarkReduction.partialState_owned ops input outside {n} {k} {n})
theorem segment_equivalence (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) :
    extract layout (finalState ops input outside) = some (spec ops input) := by
  have he := LarkReduction.extract_eq ops input outside {n} {k}
  rw [LarkReduction.spec_eq_matrixSpec] at he
  exact he
theorem kernel_eq_spec (ops : Ops α) :
    Correct ops layout geometry fuel program (spec ops) := by
  intro input outside
  exact ⟨finalState ops input outside, segmentation ops input outside,
    race_free ops input outside, segment_equivalence ops input outside⟩
theorem kernel_eq_spec_pre (ops : Ops α) (input : Nat → Nat → α) (s : State α)
    (pre : StdPre layout input s) :
    ∃ final, runLaunch ops layout geometry fuel program s = some final ∧
      raceFree geometry final.trace = true ∧ extract layout final = some (spec ops input) := by
  exact correct_from_pre ops layout geometry fuel program (spec ops)
    (kernel_eq_spec ops) input s pre
#print axioms segmentation_data
#print axioms segmentation
#print axioms race_free
#print axioms segment_equivalence
#print axioms kernel_eq_spec
#print axioms kernel_eq_spec_pre
end LarkCertificate
"""
    )


def verify(kernel, reference, task_path, output, *, lean=None, timeout=120):
    if output.exists() or timeout <= 0:
        raise Refusal("configuration", "fresh output directory and positive timeout required")
    sources = {
        "kernel.cu": kernel.read_bytes(),
        "reference.py": reference.read_bytes(),
        "task.json": task_path.read_bytes(),
    }
    task, tr = prepare(
        *(sources[x].decode("utf-8") for x in ("kernel.cu", "reference.py", "task.json"))
    )
    binary = lean_binary(lean)
    output.mkdir(parents=True)
    for name, data in sources.items():
        (output / name).write_bytes(data)
    (output / "Main.lean").write_text(render(task, tr))
    (output / "lean-toolchain").write_text(TOOLCHAIN)
    (output / "lakefile.toml").write_text(LAKEFILE)
    write_json(output / "translation.json", tr.data())
    ok, log = run_lean(output, binary, timeout)
    (output / "lean-1.log").write_text(log)
    report = {
        "schema": 1,
        "status": "verified" if ok else "unproved",
        "model_profile": PROFILE,
        "model_hashes": model_hashes(),
        "source_readback": True,
        "model_calls": 0,
        "files": {f: digest((output / f).read_bytes()) for f in sorted(FILES)},
        "axiom_audit": log,
        "matrix_shape": list(task.buffers[0].shape),
        "trusted_assumptions": [
            "Lean 4.19.0 kernel and printed standard axioms; pinned Nonlinear machine",
            "Strict CUDA/HIP lowering and the closed matrix-vector Torch AST formalization",
            "Host launch, contiguous FP16 buffers, aligned disjoint named allocations",
            "Abstract scalar/half operations; hardware correspondence and floating-point error outside theorem",
            "External reduction from race-free phases to GPU interleavings",
        ],
        "scope": "Full counted loop and grid in existing runLaunch: completion, race freedom, every output, all inputs and arbitrary outside memory. One thread per row; independent scalar GEMV, not the optimized original paper kernel.",
    }
    write_json(output / "report.json", report)
    return report


def check(directory, *, lean=None, timeout=120):
    report = json.loads((directory / "report.json").read_text())
    if report.get("model_profile") != PROFILE or set(report["files"]) != FILES:
        raise Refusal("integrity", "unexpected GEMV profile or file set")
    for name, expected in report["files"].items():
        if digest((directory / name).read_bytes()) != expected:
            raise Refusal("integrity", f"file changed: {name}")
    if report["model_hashes"] != model_hashes():
        raise Refusal("integrity", "different pinned machine or proof libraries")
    if (directory / "lean-toolchain").read_text() != TOOLCHAIN or (
        directory / "lakefile.toml"
    ).read_text() != LAKEFILE:
        raise Refusal("integrity", "unexpected standalone project configuration")
    task, tr = prepare(
        *((directory / x).read_text() for x in ("kernel.cu", "reference.py", "task.json"))
    )
    shape = report.get("matrix_shape")
    if (
        not isinstance(shape, list)
        or any(type(x) is not int for x in shape)
        or shape != list(task.buffers[0].shape)
    ):
        raise Refusal("integrity", "reported matrix shape differs from the fixed signature")
    if json.loads((directory / "translation.json").read_text()) != json.loads(
        json.dumps(tr.data())
    ):
        raise Refusal("integrity", "translation differs from source")
    if (directory / "Main.lean").read_text() != render(task, tr):
        raise Refusal("integrity", "theorem differs from the fixed source/reference statement")
    ok, log = run_lean(directory, lean_binary(lean), timeout)
    if not ok:
        raise Refusal("proof", log)
    return log
