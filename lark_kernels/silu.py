"""Inductive certificates for the upstream-style scalar FP16 SiLU-and-mul loop.

The closed reference AST fixes the packed-row contract and both half boundaries.
The ordinary reader still binds every source instruction; Lean checks all lanes,
strided iterations, outputs and race freedom in the unchanged nonlinear machine.
"""

import ast
from dataclasses import replace
import json
import keyword
from pathlib import Path
import re
import sysconfig

from .certificate import LAKEFILE, TOOLCHAIN, digest, lean_binary, run_lean, write_json
from .frontend import translate
from .ir import Buffer, Refusal, Task, lean_list, lean_node, node
from .spec import read_spec

PROFILE = "silu-multiwave-v15"
LIBRARIES = (
    "Nonlinear.lean",
    "Pointwise.lean",
    "Reduction.lean",
    "DotLoop.lean",
    "Matrix.lean",
    "ScalarLaunch.lean",
    "Silu.lean",
)
FILES = {
    "Main.lean",
    "kernel.cu",
    "reference.py",
    "task.json",
    "translation.json",
    "lean-toolchain",
    "lakefile.toml",
}


def library(name):
    p = Path(__file__).resolve().parents[1] / "lean/Lark" / name
    if not p.exists():
        p = Path(sysconfig.get_path("data")) / "share/lark/lean/Lark" / name
    if not p.is_file():
        raise Refusal("installation", "pinned SiLU proof library is missing: " + name)
    return p


def parse_task(source):
    d = json.loads(source)
    buffers = d["buffers"]
    if len(buffers) != 2 or [b["role"] for b in buffers] != ["output", "input"]:
        raise Refusal("silu", "one output followed by one packed input is required")
    shape = buffers[0]["shape"]
    if (
        not isinstance(shape, list)
        or len(shape) != 2
        or any(type(x) is not int or x <= 0 for x in shape)
    ):
        raise Refusal("silu", "output must be [tokens, hidden], with positive integer dimensions")
    rows, width = shape
    if (
        rows * 2 * width >= 2147483648
        or buffers[1]["shape"] != [rows, 2 * width]
        or any(type(x) is not int for x in buffers[1]["shape"])
        or any(b["dtype"] != "float16" for b in buffers)
    ):
        raise Refusal(
            "silu", "contiguous FP16 [tokens, hidden] / [tokens, 2*hidden], total input <2^31"
        )
    if width % 8 == 0:
        raise Refusal("silu", "this scalar-fallback profile requires hidden not divisible by eight")
    language = d.get("language", "cuda")
    if language not in {"cuda", "hip"}:
        raise Refusal("silu", "CUDA/HIP scalar source only")
    block, warp = min(width, 1024), 64 if language == "hip" else 32
    launch = d["launch"]
    if any(type(x) is not int for x in launch.values()) or launch != {
        "grid": rows,
        "block": block,
        "warp": warp,
    }:
        raise Refusal(
            "silu",
            "launch must match the scalar upstream host: grid=tokens, block=min(hidden,1024), native warp",
        )
    fuel = [7 * width + 4, 1, 1, 1]
    requested = d.get("fuel", fuel)
    if requested != fuel or any(type(x) is not int for x in requested):
        raise Refusal("silu", "fuel must be [7*hidden+4,1,1,1]")
    for b in buffers:
        if (
            not isinstance(b["name"], str)
            or not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*", b["name"])
            or keyword.iskeyword(b["name"])
        ):
            raise Refusal("silu", "ordinary non-keyword buffer identifiers required")
    proxy = json.loads(source)
    proxy["launch"] = {"grid": 1, "block": 1, "warp": warp}
    proxy["fuel"] = [4, 1, 1, 1]
    for b in proxy["buffers"]:
        b["shape"] = [1]
    checked = Task.parse(json.dumps(proxy))
    return replace(
        checked,
        grid=rows,
        block=block,
        fuel=tuple(fuel),
        buffers=tuple(
            Buffer(b.name, b.role, tuple(raw["shape"]), b.dtype)
            for b, raw in zip(checked.buffers, buffers)
        ),
    )


def canonical_reference(rows, width, argument="input"):
    return f"""import torch

def reference({argument}):
    packed = {argument}.reshape({rows}, 2, {width})
    gate = packed.select(1, 0).float()
    up = packed.select(1, 1).float()
    activated = (gate / (1.0 + torch.exp((0.0 - gate) * 1.0))).half()
    return (activated.float() * (up + 0.0)).half()
"""


def reference_body(source, task):
    rows, width = task.buffers[0].shape
    parsed = ast.parse(source)
    expected = ast.parse(canonical_reference(rows, width, task.buffers[1].name))
    if ast.dump(parsed) != ast.dump(expected):
        raise Refusal(
            "silu-reference",
            "expected the closed packed-row reshape/select reference with intermediate half rounding",
        )
    # The accepted AST has only this row/half selection and pure elementwise
    # arithmetic. Normalize the two declared dimensions; no expression is lost.
    parsed.body[1].body[0].value.args = [ast.Constant(1), ast.Constant(2), ast.Constant(1)]
    small = replace(
        task,
        grid=1,
        block=1,
        buffers=(replace(task.buffers[0], shape=(1, 1)), replace(task.buffers[1], shape=(1, 2))),
    )
    spec = read_spec(ast.unparse(ast.fix_missing_locations(parsed)), small)
    if len(spec) != 1:
        raise Refusal("silu-reference", "unexpected scalar template result")
    return spec[0]


def expected_program(width):
    a = node(
        "add",
        node("mul", node("mul", node("ivar", 0), node("const", 2)), node("const", width)),
        node("ivar", 1),
    )
    b = node("add", a, node("const", width))
    o = node("add", node("mul", node("ivar", 0), node("const", width)), node("ivar", 1))
    activation = node(
        "un",
        "fromHalf",
        node(
            "un",
            "toHalf",
            node(
                "bin",
                "div",
                node("reg", 0),
                node(
                    "bin",
                    "add",
                    node("lit", 1, 1),
                    node(
                        "un",
                        "exp",
                        node(
                            "bin",
                            "mul",
                            node("bin", "sub", node("lit", 0, 1), node("reg", 0)),
                            node("lit", 1, 1),
                        ),
                    ),
                ),
            ),
        ),
    )
    output = node(
        "un",
        "toHalf",
        node("bin", "mul", node("reg", 2), node("bin", "add", node("reg", 1), node("lit", 0, 1))),
    )
    return [
        node("idx", 0, node("bid")),
        node("idx", 1, node("tid")),
        node("branch", node("lt", node("ivar", 1), node("const", width)), 9),
        node("set", 0, node("un", "fromHalf", node("load", "global", 1, a))),
        node("set", 1, node("un", "fromHalf", node("load", "global", 1, b))),
        node("set", 2, activation),
        node("store", "global", 0, o, output),
        node("idx", 1, node("add", node("ivar", 1), node("bdim"))),
        node("jump", 2),
        node("halt"),
    ]


def prepare(source, reference, task_source):
    task = parse_task(task_source)
    tr = translate(source, task)
    if tr.shared or tr.program != expected_program(task.buffers[0].shape[1]):
        raise Refusal(
            "silu", "source differs from the proved ten-instruction scalar strided-loop profile"
        )
    return task, tr, reference_body(reference, task)


def reference_lean(expr):
    if expr.op == "input" and expr.args in {(1, 0), (1, 1)}:
        which = "aAddress" if expr.args[1] == 0 else "bAddress"
        return f"(input 1 (LarkSilu.{which} shape row col))"
    if expr.op == "lit":
        return f"(ops.literal ({expr.args[0]}) {expr.args[1]})"
    if expr.op == "bin":
        op, a, b = expr.args
        return f"(ops.{op} {reference_lean(a)} {reference_lean(b)})"
    if expr.op == "un":
        return f"(ops.{expr.args[0]} {reference_lean(expr.args[1])})"
    raise Refusal("silu-reference", "unexpected scalar template node")


def render(task, tr, reference):
    rows, width = task.buffers[0].shape
    modules = []
    for name in LIBRARIES:
        modules.append(
            re.sub(r"^import Lark\.[A-Za-z_0-9]+\n", "", library(name).read_text(), flags=re.M)
        )
    return (
        "\n".join(modules)
        + f"""
namespace LarkCertificate
open LarkNonlinear
def shape : LarkSilu.Shape := {{
  rows := {rows}, width := {width}, block := {task.block}, warp := {task.warp},
  rowsPos := by decide, widthPos := by decide, blockPos := by decide,
  warpPos := by decide, blockLe := by decide, dataBound := by decide }}
def layout : Layout := LarkSilu.layout shape
def geometry : Geometry := LarkSilu.geometry shape
def fuel : Fuel := LarkSilu.fuel shape
def program : List Instr := {lean_list(lean_node(i) for i in tr.program)}
def referenceResult (ops : Ops α) (input : Nat → Nat → α) (row col : Nat) : α :=
  {reference_lean(reference)}
def spec (ops : Ops α) (input : Nat → Nat → α) : List α :=
  (List.range (shape.rows * shape.width)).map fun i =>
    referenceResult ops input (i / shape.width) (i % shape.width)
def finalState (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) : State α :=
  LarkSilu.finalState shape ops input outside
theorem reference_data (ops : Ops α) (input : Nat → Nat → α) (row col : Nat) :
    referenceResult ops input row col = LarkSilu.result shape ops input row col := by rfl
theorem reference_spec (ops : Ops α) (input : Nat → Nat → α) :
    spec ops input = LarkSilu.spec shape ops input := by
  have he : (fun i => referenceResult ops input (i / shape.width) (i % shape.width)) =
      (fun i => LarkSilu.result shape ops input (i / shape.width) (i % shape.width)) := by
    funext i
    exact reference_data ops input _ _
  exact congrArg (fun f => (List.range (shape.rows * shape.width)).map f) he
theorem segmentation_data : program = LarkSilu.program shape := by rfl
theorem segmentation (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) :
    runLaunch ops layout geometry fuel program (initial layout input outside) =
      some (finalState ops input outside) := by
  rewrite [segmentation_data]
  exact (LarkSilu.launch_eq shape ops input outside).1
theorem race_free (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) :
    raceFree geometry (finalState ops input outside).trace = true := by
  exact LarkSilu.owned_raceFree shape geometry _ (LarkSilu.launch_eq shape ops input outside).2.1.2.1
theorem segment_equivalence (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) :
    extract layout (finalState ops input outside) = some (spec ops input) := by
  rewrite [reference_spec]
  exact LarkSilu.extract_final shape ops input outside
theorem kernel_eq_spec (ops : Ops α) : Correct ops layout geometry fuel program (spec ops) := by
  intro input outside
  exact ⟨finalState ops input outside, segmentation ops input outside,
    race_free ops input outside, segment_equivalence ops input outside⟩
theorem kernel_eq_spec_pre (ops : Ops α) (input : Nat → Nat → α) (s : State α)
    (pre : StdPre layout input s) :
    ∃ final, runLaunch ops layout geometry fuel program s = some final ∧
      raceFree geometry final.trace = true ∧ extract layout final = some (spec ops input) := by
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


def model_hashes():
    return {name: digest(library(name).read_bytes()) for name in LIBRARIES}


def verify(kernel, reference, task_path, output, *, lean=None, timeout=150):
    if output.exists() or timeout <= 0:
        raise Refusal("configuration", "fresh output and positive Lean timeout required")
    sources = {
        "kernel.cu": kernel.read_bytes(),
        "reference.py": reference.read_bytes(),
        "task.json": task_path.read_bytes(),
    }
    task, tr, ref = prepare(
        *(sources[n].decode("utf-8") for n in ("kernel.cu", "reference.py", "task.json"))
    )
    output.mkdir(parents=True)
    for name, data in sources.items():
        (output / name).write_bytes(data)
    (output / "Main.lean").write_text(render(task, tr, ref))
    (output / "lean-toolchain").write_text(TOOLCHAIN)
    (output / "lakefile.toml").write_text(LAKEFILE)
    write_json(output / "translation.json", tr.data())
    ok, log = run_lean(output, lean_binary(lean), timeout)
    (output / "lean-1.log").write_text(log)
    rows, width = task.buffers[0].shape
    report = {
        "schema": 1,
        "status": "verified" if ok else "unproved",
        "model_profile": PROFILE,
        "model_hashes": model_hashes(),
        "source_readback": True,
        "files": {f: digest((output / f).read_bytes()) for f in sorted(FILES)},
        "rows": rows,
        "hidden": width,
        "output_elements": rows * width,
        "input_elements": rows * width * 2,
        "block": task.block,
        "warp": task.warp,
        "axiom_audit": log,
        "model_calls": 0,
        "original_paper_fully_reproduced": False,
        "trusted_assumptions": [
            "Lean 4.19.0 and the printed standard axioms",
            "Pinned nonlinear machine and operation-to-hardware correspondence",
            "CUDA/HIP reader, lowering, lossless read-back and closed reference AST interpretation",
            "Host honors the declared native scalar launch and separated contiguous FP16 regions",
            "Abstract operations and half conversions; no IEEE theorem or numerical error bound",
            "Race-free phase reduction to hardware interleavings remains external metatheory",
        ],
        "scope": "Independent scalar SiLU-and-mul adaptation: every actual lane, warp, block, strided iteration and output in the declared launch. Supports the pinned upstream scalar branch and a closed packed-row reference AST. Not original paper sources/runs, packed vector kernels, IEEE behavior or NVIDIA execution.",
    }
    write_json(output / "report.json", report)
    return report


def check(directory, *, lean=None, timeout=150):
    report = json.loads((directory / "report.json").read_bytes().decode("utf-8"))
    if report.get("model_profile") != PROFILE or set(report["files"]) != FILES:
        raise Refusal("integrity", "unexpected multiwave SiLU profile or files")
    for name, expected in report["files"].items():
        if digest((directory / name).read_bytes()) != expected:
            raise Refusal("integrity", "changed certificate file: " + name)
    if report["model_hashes"] != model_hashes():
        raise Refusal("integrity", "different pinned machine or SiLU proof library")
    if (directory / "lean-toolchain").read_text() != TOOLCHAIN or (
        directory / "lakefile.toml"
    ).read_text() != LAKEFILE:
        raise Refusal("integrity", "unexpected standalone toolchain/project")
    task, tr, ref = prepare(
        *(
            (directory / n).read_bytes().decode("utf-8")
            for n in ("kernel.cu", "reference.py", "task.json")
        )
    )
    rows, width = task.buffers[0].shape
    expected = {
        "rows": rows,
        "hidden": width,
        "output_elements": rows * width,
        "input_elements": rows * width * 2,
        "block": task.block,
        "warp": task.warp,
    }
    if any(type(report.get(k)) is not int or report[k] != v for k, v in expected.items()):
        raise Refusal("integrity", "reported shape/launch differs from the signature")
    if json.loads((directory / "translation.json").read_text()) != json.loads(
        json.dumps(tr.data())
    ):
        raise Refusal("integrity", "translation differs from exact source")
    if (directory / "Main.lean").read_text() != render(task, tr, ref):
        raise Refusal("integrity", "theorem differs from fixed source/reference statement")
    ok, log = run_lean(directory, lean_binary(lean), timeout)
    if not ok:
        raise Refusal("proof", log)
    return log
