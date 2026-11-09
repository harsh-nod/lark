"""Scalable pointwise certificates using induction in the existing GPU machine.

This separate profile accepts exactly two FP16 buffers, a one-thread block,
and a four-instruction program. The bounded verifier's limits are unchanged.
"""

import ast
from dataclasses import replace
import json
from pathlib import Path
import sysconfig

from .certificate import LAKEFILE, TOOLCHAIN, digest, lean_binary, model_path, run_lean, write_json
from .frontend import translate
from .ir import Buffer, Node, Refusal, Task, lean_list, lean_node, node
from .spec import read_spec


PROFILE = "pointwise-induction-v3"
FILES = {
    "Main.lean",
    "kernel.cu",
    "reference.py",
    "task.json",
    "translation.json",
    "lean-toolchain",
    "lakefile.toml",
}


def induction_path():
    repo = Path(__file__).resolve().parent.parent / "lean/Lark/Pointwise.lean"
    if repo.exists():
        return repo
    installed = Path(sysconfig.get_path("data")) / "share/lark/lean/Lark/Pointwise.lean"
    if installed.exists():
        return installed
    raise Refusal("installation", "pinned pointwise induction library is missing")


def parse_task(source):
    d = json.loads(source)
    buffers = d["buffers"]
    if len(buffers) != 2 or [b["role"] for b in buffers] != ["input", "output"]:
        raise Refusal("pointwise", "exactly one input followed by one output is required")
    shape = buffers[0]["shape"]
    if (
        not isinstance(shape, list)
        or len(shape) != 1
        or type(shape[0]) is not int
        or not 1 <= shape[0] < 2147483648
        or not isinstance(buffers[1]["shape"], list)
        or any(type(dimension) is not int for dimension in buffers[1]["shape"])
        or buffers[1]["shape"] != shape
        or any(b["dtype"] != "float16" for b in buffers)
    ):
        raise Refusal("pointwise", "equal one-dimensional FP16 buffers, length 1..2^31-1")
    n = shape[0]
    language = d.get("language", "cuda")
    warp = 32 if language == "cuda" else 64
    if any(type(value) is not int for value in d["launch"].values()) or d["launch"] != {
        "grid": n,
        "block": 1,
        "warp": warp,
    }:
        raise Refusal("pointwise", "launch must have grid=length, block=1, native warp width")
    requested_fuel = d.get("fuel", [4, 1, 1, 1])
    if requested_fuel != [4, 1, 1, 1] or any(type(value) is not int for value in requested_fuel):
        raise Refusal("pointwise", "fuel must be [4,1,1,1]")
    # Reuse all ordinary signature/name/language checks on a small signature;
    # only the capacity and the precisely checked launch differ in this profile.
    small = json.loads(source)
    small["launch"]["grid"] = 1
    small["fuel"] = [4, 1, 1, 1]
    for b in small["buffers"]:
        b["shape"] = [1]
    checked = Task.parse(json.dumps(small))
    return replace(
        checked,
        grid=n,
        buffers=tuple(Buffer(b.name, b.role, (n,), b.dtype) for b in checked.buffers),
    )


def scalar(n):
    if n.op == "reg" and n.args == (0,):
        return ".input"
    if n.op == "lit":
        return f"(.lit ({n.args[0]}) {n.args[1]})"
    if n.op == "bin":
        op, a, b = n.args
        return f"(.bin .{op} {scalar(a)} {scalar(b)})"
    if n.op == "un":
        op, a = n.args
        return f"(.un .{op} {scalar(a)})"
    raise Refusal("pointwise", "the scalar body may use only register zero and scalar operations")


def reference_body(source, task):
    # This closed AST grammar excludes indexing, reshaping, reductions,
    # dimensions, branching, helpers and every other shape-dependent operation.
    # Thus the reference has the same scalar expression at EVERY cell.
    tree = ast.parse(source)
    allowed = (
        ast.Module,
        ast.Import,
        ast.alias,
        ast.FunctionDef,
        ast.arguments,
        ast.arg,
        ast.Return,
        ast.Name,
        ast.Load,
        ast.Attribute,
        ast.Call,
        ast.keyword,
        ast.Constant,
        ast.BinOp,
        ast.UnaryOp,
        ast.Add,
        ast.Sub,
        ast.Mult,
        ast.Div,
        ast.USub,
    )
    attributes = {
        "float",
        "half",
        "relu",
        "silu",
        "gelu",
        "exp",
        "tanh",
        "rsqrt",
        "sigmoid",
        "square",
        "maximum",
        "nn",
        "functional",
    }
    for item in ast.walk(tree):
        if not isinstance(item, allowed) or (
            isinstance(item, ast.Attribute) and item.attr not in attributes
        ):
            raise Refusal("pointwise-reference", "only pure elementwise expressions are supported")
    small = replace(task, grid=1, buffers=tuple(replace(b, shape=(1,)) for b in task.buffers))
    spec = read_spec(source, small)
    if len(spec) != 1 or spec[0].op != "un" or spec[0].args[0] != "toHalf":
        raise Refusal("pointwise-reference", "reference must explicitly round output to half")

    def convert(n):
        if n == node("un", "fromHalf", node("input", 0, 0)):
            return node("reg", 0)
        if n.op in {"lit", "bin", "un"}:
            return Node(n.op, tuple(convert(a) if isinstance(a, Node) else a for a in n.args))
        raise Refusal("pointwise-reference", "input must be explicitly promoted from half")

    return convert(spec[0].args[1])


def prepare(source, reference, task_source):
    task = parse_task(task_source)
    tr = translate(source, task)
    if len(tr.program) != 4 or tr.shared:
        raise Refusal("pointwise", "expected index, half load, scalar store, halt")
    store = tr.program[2]
    if store.op != "store" or store.args[:3] != ("global", 1, node("ivar", 0)):
        raise Refusal("pointwise", "output must be cell i in the second buffer")
    output = store.args[3]
    if output.op != "un" or output.args[0] != "toHalf":
        raise Refusal("pointwise", "store must explicitly convert to half")
    body = output.args[1]
    scalar(body)
    expected = [
        node("idx", 0, node("bid")),
        node("set", 0, node("un", "fromHalf", node("load", "global", 0, node("ivar", 0)))),
        node("store", "global", 1, node("ivar", 0), node("un", "toHalf", body)),
        node("halt"),
    ]
    if tr.program != expected:
        raise Refusal("pointwise", "source does not match the proved four-instruction profile")
    ref_body = reference_body(reference, task)
    scalar(ref_body)
    return task, tr, body, ref_body


def render(task, tr, body, ref_body):
    n = task.buffers[0].size
    base = model_path(True).read_text()
    induction = induction_path().read_text()
    if not induction.startswith("import Lark.Nonlinear\n"):
        raise Refusal("installation", "unexpected induction library import")
    return (
        base
        + "\n"
        + induction.removeprefix("import Lark.Nonlinear\n")
        + f"""
namespace LarkCertificate
open LarkNonlinear
open LarkPointwise (Scalar)
def body : Scalar := {scalar(body)}
def referenceBody : Scalar := {scalar(ref_body)}
def layout : Layout := LarkPointwise.layout {n}
def geometry : Geometry := LarkPointwise.geometry {n} {task.warp}
def fuel : Fuel := LarkPointwise.fuel
def program : List Instr := {lean_list(lean_node(i) for i in tr.program)}
def spec (ops : Ops α) (input : Nat → Nat → α) : List α :=
  LarkPointwise.spec ops referenceBody {n} input
def finalState (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) : State α :=
  LarkPointwise.partialState ops body {n} input outside {n}

theorem segmentation_data : program = LarkPointwise.program body := by rfl
theorem segmentation (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) :
    runLaunch ops layout geometry fuel program (initial layout input outside) =
      some (finalState ops input outside) := by
  rw [segmentation_data]
  exact LarkPointwise.launch_eq ops body {n} {task.warp} input outside
    (by simp [LarkPointwise.Valid, body]) (by decide) (by decide) (by decide)
theorem race_free (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) :
    raceFree geometry (finalState ops input outside).trace = true := by
  exact LarkPointwise.owned_raceFree geometry _
    (LarkPointwise.partialState_owned ops body {n} input outside {n})
theorem segment_equivalence (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) :
    extract layout (finalState ops input outside) = some (spec ops input) := by
  exact LarkPointwise.partialState_extract ops body {n} input outside
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


def model_hashes():
    return {
        "nonlinear": digest(model_path(True).read_bytes()),
        "pointwise": digest(induction_path().read_bytes()),
    }


def verify(kernel, reference, task_path, output, *, lean=None, timeout=120):
    if output.exists() or timeout <= 0:
        raise Refusal("configuration", "a fresh output directory and positive timeout are required")
    sources = {
        "kernel.cu": kernel.read_bytes(),
        "reference.py": reference.read_bytes(),
        "task.json": task_path.read_bytes(),
    }
    task, tr, body, ref_body = prepare(
        *(sources[x].decode("utf-8") for x in ("kernel.cu", "reference.py", "task.json"))
    )
    binary = lean_binary(lean)
    output.mkdir(parents=True)
    for name, data in sources.items():
        (output / name).write_bytes(data)
    (output / "Main.lean").write_text(render(task, tr, body, ref_body))
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
        "files": {f: digest((output / f).read_bytes()) for f in sorted(FILES)},
        "axiom_audit": log,
        "elements": task.buffers[0].size,
        "model_calls": 0,
        "trusted_assumptions": [
            "Lean 4.19.0 kernel and printed standard axioms",
            "Existing pinned Nonlinear GPU machine; source lowering and elementwise Torch AST formalization",
            "Host launch and contiguous, aligned, disjoint input/output FP16 buffers",
            "Abstract scalar and half operations; hardware correspondence and numerical error outside theorem",
            "Race-free sequential phase reduction to GPU interleavings remains external metatheory",
        ],
        "scope": "All inputs and arbitrary outside memory; full runLaunch completion, race freedom, all output cells. One thread per block; no optimized-launch or original paper result claim.",
    }
    write_json(output / "report.json", report)
    return report


def check(directory, *, lean=None, timeout=120):
    report = json.loads((directory / "report.json").read_text())
    if report.get("model_profile") != PROFILE or set(report["files"]) != FILES:
        raise Refusal("integrity", "unexpected pointwise certificate profile or file set")
    for name, expected in report["files"].items():
        if digest((directory / name).read_bytes()) != expected:
            raise Refusal("integrity", f"file changed: {name}")
    if report["model_hashes"] != model_hashes():
        raise Refusal("integrity", "different pinned machine or induction library")
    if (directory / "lean-toolchain").read_text() != TOOLCHAIN or (
        directory / "lakefile.toml"
    ).read_text() != LAKEFILE:
        raise Refusal("integrity", "unexpected standalone project configuration")
    task, tr, body, ref_body = prepare(
        *((directory / x).read_text() for x in ("kernel.cu", "reference.py", "task.json"))
    )
    if json.loads((directory / "translation.json").read_text()) != json.loads(
        json.dumps(tr.data())
    ):
        raise Refusal("integrity", "translation differs from source")
    if (directory / "Main.lean").read_text() != render(task, tr, body, ref_body):
        raise Refusal("integrity", "theorem differs from the fixed source/reference statement")
    ok, log = run_lean(directory, lean_binary(lean), timeout)
    if not ok:
        raise Refusal("proof", log)
    return log
