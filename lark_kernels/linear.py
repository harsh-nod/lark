"""Full-size FP16 Linear with a checked counted loop and bias-reading epilogue."""

import ast
from dataclasses import replace
import json

from . import matrix, pointwise
from .certificate import LAKEFILE, TOOLCHAIN, digest, lean_binary, model_path, run_lean, write_json
from .frontend import translate
from .ir import Buffer, Refusal, Task, lean_list, lean_node, node
from .spec import read_spec

PROFILE = "linear-induction-v6"
FILES = pointwise.FILES


library_path = matrix.library_path


def dimensions(task):
    m, k = task.buffers[0].shape
    return 1, m, k, task.buffers[1].shape[1]


def parse_task(source):
    d = json.loads(source)
    buffers = d["buffers"]
    if len(buffers) != 4 or [b["role"] for b in buffers] != ["input"] * 3 + ["output"]:
        raise Refusal("linear", "expected three inputs and one output")
    if any(
        b["dtype"] != "float16"
        or not isinstance(b["shape"], list)
        or len(b["shape"]) != rank
        or any(type(x) is not int or x <= 0 for x in b["shape"])
        for b, rank in zip(buffers, (2, 2, 1, 2))
    ):
        raise Refusal("linear", "expected positive FP16 matrix/vector shapes")
    a, b, bias, out = [b["shape"] for b in buffers]
    m, k = a
    n = b[1]
    if b != [k, n] or bias != [n] or out != [m, n] or max(m * k, k * n, m * n) >= 2147483648:
        raise Refusal("linear", "expected [M,K]@[K,N]+[N] -> [M,N], all sizes < 2^31")
    warp = 32 if d.get("language", "cuda") == "cuda" else 64
    if d["launch"] != {"grid": m * n, "block": 1, "warp": warp} or any(
        type(v) is not int for v in d["launch"].values()
    ):
        raise Refusal("linear", "expected one scalar thread/block per output, native warp width")
    fuel = d.get("fuel", [4 * k + 6, 1, 1, 1])
    if fuel != [4 * k + 6, 1, 1, 1] or any(type(v) is not int for v in fuel):
        raise Refusal("linear", "fuel must be [4*K+6,1,1,1]")
    small = json.loads(source)
    small["launch"]["grid"] = 1
    small["fuel"] = fuel
    for b in small["buffers"]:
        b["shape"] = [1] * len(b["shape"])
    checked = Task.parse(json.dumps(small))
    return replace(
        checked,
        grid=m * n,
        buffers=tuple(Buffer(b["name"], b["role"], tuple(b["shape"]), b["dtype"]) for b in buffers),
    )


def expected_program(task):
    reduced = replace(task, buffers=task.buffers[:2] + task.buffers[3:])
    program = matrix.expected_program(reduced)
    n = task.buffers[1].shape[1]
    bias = node(
        "un", "fromHalf", node("load", "global", 2, node("mod", node("ivar", 0), node("const", n)))
    )
    program[7] = node(
        "store",
        "global",
        3,
        node("ivar", 0),
        node("un", "toHalf", node("bin", "add", node("reg", 0), bias)),
    )
    return program


def prepare(source, reference, task_source):
    task = parse_task(task_source)
    tr = translate(source, task)
    if tr.shared or tr.program != expected_program(task):
        raise Refusal("matrix", "source differs from the proved counted-loop profile")
    small = replace(
        task, grid=1, buffers=tuple(replace(b, shape=(1,) * len(b.shape)) for b in task.buffers)
    )
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
        raise Refusal("matrix-reference", "expected one pure matmul return")
    a, b, bias = [buffer.name for buffer in task.buffers[:3]]
    canonical = ast.parse(f"({a}.float() @ {b}.float() + {bias}.float()).half()", mode="eval").body
    if ast.dump(fn.body[0].value) != ast.dump(canonical):
        raise Refusal("matrix-reference", "expected (A.float() @ B.float() + bias.float()).half()")
    return task, tr


def model_hashes():
    return {
        **matrix.model_hashes(),
        **{name.lower(): digest(library_path(name).read_bytes()) for name in ("Bias",)},
    }


def render(task, tr):
    batch, m, k, n = dimensions(task)
    parts = [model_path(True).read_text()]
    for name, imported in [
        ("Pointwise", "Nonlinear"),
        ("Reduction", "Pointwise"),
        ("DotLoop", "Reduction"),
        ("Matrix", "DotLoop"),
        ("Bias", "Matrix"),
    ]:
        text = library_path(name).read_text()
        prefix = "import Lark." + imported + "\n"
        if not text.startswith(prefix):
            raise Refusal("installation", "unexpected " + name + " library import")
        parts.append(text.removeprefix(prefix))
    profile = f"LarkBias.linearProfile {m} {n} {k} " + " ".join(["(by decide)"] * 5)
    return (
        "\n".join(parts)
        + f"""
namespace LarkCertificate
open LarkNonlinear
def profile : LarkBias.Profile := {profile}
def layout : Layout := LarkBias.layout profile
def geometry : Geometry := LarkBias.geometry profile {task.warp}
def fuel : Fuel := LarkBias.fuel profile
def program : List Instr := {lean_list(lean_node(i) for i in tr.program)}
def spec (ops : Ops α) (input : Nat → Nat → α) : List α :=
  LarkBias.matrixSpec ops profile input
def finalState (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) : State α :=
  LarkBias.partialState ops input outside profile profile.n
theorem segmentation_data : program = LarkBias.program profile := by rfl
theorem segmentation (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) :
    runLaunch ops layout geometry fuel program (initial layout input outside) =
      some (finalState ops input outside) := by
  rw [segmentation_data]
  exact LarkBias.launch_eq ops input outside profile {task.warp}
    (by decide) (by decide) (by decide) (by decide)
theorem race_free (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) :
    raceFree geometry (finalState ops input outside).trace = true := by
  exact LarkBias.owned_raceFree geometry _
    (LarkBias.partialState_owned ops input outside profile profile.n)
theorem segment_equivalence (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) :
    extract layout (finalState ops input outside) = some (spec ops input) := by
  have he := LarkBias.extract_eq ops input outside profile
  rw [LarkBias.spec_eq_matrixSpec] at he
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
        "matrix_dimensions": list(dimensions(task)),
        "trusted_assumptions": [
            "Lean 4.19.0 kernel and printed standard axioms; pinned Nonlinear machine",
            "Strict CUDA/HIP lowering and the closed matrix-multiplication Torch AST formalization",
            "Host launch, contiguous FP16 buffers, aligned disjoint named allocations",
            "Abstract scalar/half operations; hardware correspondence and floating-point error outside theorem",
            "External reduction from race-free phases to GPU interleavings",
        ],
        "scope": "Full counted loop and grid in existing runLaunch: completion, race freedom, every output, all inputs and arbitrary outside memory. One thread per output; independent scalar Linear, not the optimized original paper kernel.",
    }
    write_json(output / "report.json", report)
    return report


def check(directory, *, lean=None, timeout=120):
    report = json.loads((directory / "report.json").read_text())
    if report.get("model_profile") != PROFILE or set(report["files"]) != FILES:
        raise Refusal("integrity", "unexpected Linear profile or file set")
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
    shape = report.get("matrix_dimensions")
    if (
        not isinstance(shape, list)
        or any(type(x) is not int for x in shape)
        or shape != list(dimensions(task))
    ):
        raise Refusal("integrity", "reported matrix dimensions differs from the fixed signature")
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
