"""Full-length FP16 normalization by checked reduction-loop and grid induction."""

import ast
from dataclasses import replace
import json

from . import gemv, matrix, pointwise
from .certificate import LAKEFILE, TOOLCHAIN, digest, lean_binary, model_path, run_lean, write_json
from .frontend import translate
from .ir import Refusal, lean_list, lean_node, node
from .spec import read_spec

PROFILE = "normalization-induction-v9"
FILES = pointwise.FILES
KINDS = ("rms", "layer", "softmax")
library_path = matrix.library_path


def lane_fuel(kind, n):
    return 5 * (n - (kind == "softmax")) + 5 * (0 if kind == "rms" else n) + 13


def reference_expression(kind, name="x"):
    x = f"{name}.float()"
    if kind == "rms":
        return f"({x}*torch.rsqrt(({x}*{x}).mean()+1e-5)).half()"
    if kind == "layer":
        return f"(({x}-{x}.mean())*torch.rsqrt((({x}-{x}.mean())*({x}-{x}.mean())).mean()+1e-5)).half()"
    if kind == "softmax":
        return f"{x}.softmax(dim=0).half()"
    raise Refusal("normalization", "unknown normalization kind")


def expected_program(kind, n):
    acc, ctx, val = [node("reg", i) for i in range(3)]
    ix, j = node("ivar", 0), node("ivar", 1)

    def binary(op, a, b):
        return node("bin", op, a, b)

    def unary(op, a):
        return node("un", op, a)

    def load(i):
        return unary("fromHalf", node("load", "global", 0, i))

    zero = node("lit", 0, 1)
    norm = binary("div", acc, node("lit", n, 1))
    centered = binary("sub", val, ctx)
    exp = unary("exp", centered)
    first = binary("mul", val, val) if kind == "rms" else val
    second = (
        binary("mul", centered, centered) if kind == "layer" else exp if kind == "softmax" else val
    )
    eps = node("lit", 1, 100000)
    output = (
        binary("div", exp, acc)
        if kind == "softmax"
        else binary(
            "mul",
            centered if kind == "layer" else val,
            unary("rsqrt", binary("add", norm if kind == "layer" else ctx, eps)),
        )
    )
    return [
        node("idx", 0, node("bid")),
        node("set", 0, load(node("const", 0)) if kind == "softmax" else zero),
        node("set", 1, zero),
        node("set", 2, zero),
        node("idx", 1, node("const", 1 if kind == "softmax" else 0)),
        node("branch", node("lt", j, node("const", n)), 10),
        node("set", 2, load(j)),
        node("set", 0, binary("max" if kind == "softmax" else "add", acc, first)),
        node("idx", 1, node("add", j, node("const", 1))),
        node("jump", 5),
        node("set", 1, acc if kind == "softmax" else norm),
        node("set", 0, zero),
        node("idx", 1, node("const", n if kind == "rms" else 0)),
        node("branch", node("lt", j, node("const", n)), 18),
        node("set", 2, load(j)),
        node("set", 0, binary("add", acc, second)),
        node("idx", 1, node("add", j, node("const", 1))),
        node("jump", 13),
        node("set", 2, load(ix)),
        node("store", "global", 1, ix, unary("toHalf", output)),
        node("halt"),
    ]


def prepare(source, reference, task_source):
    raw = json.loads(task_source)
    small = json.loads(task_source)
    small["fuel"] = [4, 1, 1, 1]
    task = pointwise.parse_task(json.dumps(small))
    tree = ast.parse(reference)
    fn = next((s for s in tree.body if isinstance(s, ast.FunctionDef)), None)
    if fn is None or len(fn.body) != 1 or not isinstance(fn.body[0], ast.Return):
        raise Refusal("normalization-reference", "expected one pure normalization return")
    name = task.buffers[0].name
    kinds = [
        k
        for k in KINDS
        if ast.dump(fn.body[0].value)
        == ast.dump(ast.parse(reference_expression(k, name), mode="eval").body)
    ]
    if len(kinds) != 1:
        raise Refusal(
            "normalization-reference", "reference differs from the closed normalization ASTs"
        )
    kind = kinds[0]
    fuel = raw.get("fuel")
    if fuel != [lane_fuel(kind, task.grid), 1, 1, 1] or any(type(x) is not int for x in fuel):
        raise Refusal("normalization", "fuel differs from the checked two-phase schedule")
    task = replace(task, fuel=tuple(fuel))
    tr = translate(source, task)
    if tr.shared or tr.program != expected_program(kind, task.grid):
        raise Refusal("normalization", "source differs from the proved normalization profile")
    # Match the complete operator AST before using a minimal instance to check
    # module safety, binding and dtype rules. Shape-dependent code cannot lift.
    minimal = replace(task, grid=1, buffers=tuple(replace(b, shape=(1,)) for b in task.buffers))
    read_spec(reference, minimal)
    return task, tr, kind


def model_hashes():
    return {
        **gemv.model_hashes(),
        **{
            name.lower(): digest(library_path(name).read_bytes())
            for name in ("UnaryMap", "FoldPhase", "Normalization")
        },
    }


def render(task, tr, kind):
    parts = [model_path(True).read_text()]
    for name, imports in [
        ("Pointwise", ["Nonlinear"]),
        ("Reduction", ["Pointwise"]),
        ("UnaryMap", ["Pointwise"]),
        ("FoldPhase", ["UnaryMap", "Reduction"]),
        ("Normalization", ["FoldPhase"]),
    ]:
        text = library_path(name).read_text()
        prefix = "".join("import Lark." + i + "\n" for i in imports)
        if not text.startswith(prefix):
            raise Refusal("installation", "unexpected " + name + " library imports")
        parts.append(text.removeprefix(prefix))
    n = task.grid
    return (
        "\n".join(parts)
        + f"""
namespace LarkCertificate
open LarkNonlinear
def profile : LarkUnaryMap.Profile := LarkNormalization.profile .{kind} {n}
def layout : Layout := LarkUnaryMap.layout {n}
def geometry : Geometry := LarkUnaryMap.geometry {n} {task.warp}
def fuel : Fuel := LarkUnaryMap.fuel profile
def program : List Instr := {lean_list(lean_node(i) for i in tr.program)}
def spec (ops : Ops α) (input : Nat → Nat → α) : List α := LarkUnaryMap.spec profile ops input
def finalState (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) : State α := LarkUnaryMap.partialState profile ops input outside {n}
theorem segmentation_data : program=LarkNormalization.program .{kind} {n} := by rfl
theorem segmentation (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) :
    runLaunch ops layout geometry fuel program (initial layout input outside)=some (finalState ops input outside) := by
  rw [segmentation_data]
  exact LarkUnaryMap.launch_eq profile ops input outside {task.warp} (by decide) (by decide) (by decide)
theorem race_free (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) :
    raceFree geometry (finalState ops input outside).trace=true := by
  exact LarkUnaryMap.owned_raceFree geometry _ (LarkUnaryMap.partialState_owned profile ops input outside {n})
theorem segment_equivalence (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) :
    extract layout (finalState ops input outside)=some (spec ops input) := by
  exact LarkUnaryMap.extract_eq profile ops input outside
theorem kernel_eq_spec (ops : Ops α) : Correct ops layout geometry fuel program (spec ops) := by
  intro input outside
  exact ⟨finalState ops input outside,segmentation ops input outside,race_free ops input outside,segment_equivalence ops input outside⟩
theorem kernel_eq_spec_pre (ops : Ops α) (input : Nat → Nat → α) (s : State α) (pre : StdPre layout input s) :
    ∃ final,runLaunch ops layout geometry fuel program s=some final ∧ raceFree geometry final.trace=true ∧ extract layout final=some (spec ops input) := by
  exact correct_from_pre ops layout geometry fuel program (spec ops) (kernel_eq_spec ops) input s pre
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
    task, tr, kind = prepare(
        *(sources[x].decode("utf-8") for x in ("kernel.cu", "reference.py", "task.json"))
    )
    binary = lean_binary(lean)
    output.mkdir(parents=True)
    for name, data in sources.items():
        (output / name).write_bytes(data)
    (output / "Main.lean").write_text(render(task, tr, kind))
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
        "normalization_kind": kind,
        "elements": task.grid,
        "trusted_assumptions": [
            "Lean 4.19.0 kernel and printed standard axioms; pinned Nonlinear machine",
            "Strict CUDA/HIP lowering and the closed normalization Torch AST formalization",
            "Host launch, contiguous FP16 buffers, aligned disjoint named allocations",
            "Abstract scalar/half operations; hardware correspondence and floating-point error outside theorem",
            "External reduction from race-free phases to GPU interleavings",
        ],
        "scope": "Full reduction loops and grid in existing runLaunch: completion, race freedom, every output, all inputs and arbitrary outside memory. One thread per output; independent scalar normalization, not the optimized original paper kernel.",
    }
    write_json(output / "report.json", report)
    return report


def check(directory, *, lean=None, timeout=120):
    report = json.loads((directory / "report.json").read_text())
    if report.get("model_profile") != PROFILE or set(report["files"]) != FILES:
        raise Refusal("integrity", "unexpected normalization profile or file set")
    for name, expected in report["files"].items():
        if digest((directory / name).read_bytes()) != expected:
            raise Refusal("integrity", f"file changed: {name}")
    if report["model_hashes"] != model_hashes():
        raise Refusal("integrity", "different pinned machine or proof libraries")
    if (directory / "lean-toolchain").read_text() != TOOLCHAIN or (
        directory / "lakefile.toml"
    ).read_text() != LAKEFILE:
        raise Refusal("integrity", "unexpected standalone project configuration")
    task, tr, kind = prepare(
        *((directory / x).read_text() for x in ("kernel.cu", "reference.py", "task.json"))
    )
    if (
        report.get("normalization_kind") != kind
        or type(report.get("elements")) is not int
        or report["elements"] != task.grid
    ):
        raise Refusal("integrity", "reported normalization kind/length differs from signature")
    if json.loads((directory / "translation.json").read_text()) != json.loads(
        json.dumps(tr.data())
    ):
        raise Refusal("integrity", "translation differs from source")
    if (directory / "Main.lean").read_text() != render(task, tr, kind):
        raise Refusal("integrity", "theorem differs from the fixed source/reference statement")
    ok, log = run_lean(directory, lean_binary(lean), timeout)
    if not ok:
        raise Refusal("proof", log)
    return log
