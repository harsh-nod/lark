"""Source-bound full-wave64 butterfly reduction against an independent real sum."""

import ast
import json
from pathlib import Path
import tempfile

from . import collective, real_backend
from .certificate import digest, lean_binary, run_lean, write_json
from .ir import Refusal, Task, lean_list, lean_spec, node
from .spec import read_spec

PROFILE = "wave-sum-real-v16"
CORE = (
    "Nonlinear",
    "Pointwise",
    "Reduction",
    "DotLoop",
    "Matrix",
    "ScalarLaunch",
    "Silu",
    "Collective",
    "ShuffleTransfer",
    "CollectiveGather",
    "RegisterPhase",
    "WaveReduce",
    "WaveReduceArithmetic",
    "WaveReduceStore",
    "WaveSum",
)
BASE_FILES = {"Main.lean", "kernel.hip", "reference.py", "task.json", "translation.json"}


def libraries():
    result = {
        "Lark/" + name + ".lean": real_backend.resource("lean/Lark/" + name + ".lean").read_bytes()
        for name in CORE
    }
    for name in ("Ops", "WaveSum"):
        result["LarkReal/" + name + ".lean"] = real_backend.resource(
            "lean-real/LarkReal/" + name + ".lean"
        ).read_bytes()
    return result


def expected_program():
    result = [
        node("idx", 0, node("tid")),
        node("set", 0, node("load", "global", 0, node("ivar", 0))),
    ]
    for mask in (32, 16, 8, 4, 2, 1):
        result += [
            node("shuffle", "xor", 1, 0, node("const", mask), 64),
            node("set", 0, node("bin", "add", node("reg", 0), node("reg", 1))),
        ]
    return result + [node("store", "global", 1, node("ivar", 0), node("reg", 0)), node("halt")]


def canonical_reference(argument):
    return f"""import torch
def reference({argument}):
    return {argument}.sum(dim=0, keepdim=True).repeat_interleave(64, dim=0)
"""


def prepare(source, reference, task_source):
    raw = json.loads(task_source)
    task = Task.parse(task_source)
    if (
        task.language != "hip"
        or len(task.buffers) != 2
        or [b.role for b in task.buffers] != ["input", "output"]
        or any(b.dtype != "float32" or b.shape != (64,) for b in task.buffers)
        or any(type(x) is not int for b in raw["buffers"] for x in b["shape"])
        or raw["launch"] != {"grid": 1, "block": 64, "warp": 64}
        or any(type(x) is not int for x in raw["launch"].values())
        or raw.get("fuel") != [4, 7, 1, 1]
        or any(type(x) is not int for x in raw["fuel"])
    ):
        raise Refusal(
            "wave-sum",
            "HIP float32 input/output[64], grid1/block64/warp64 and fuel[4,7,1,1] required",
        )
    tr = collective.translate(source, task)
    if tr.shared or tr.program != expected_program():
        raise Refusal("wave-sum", "source differs from the proved sixteen-instruction butterfly")
    wanted = ast.parse(canonical_reference(task.buffers[0].name))
    if ast.dump(ast.parse(reference)) != ast.dump(wanted):
        raise Refusal(
            "wave-sum-reference",
            "closed sum(dim=0,keepdim=True).repeat_interleave(64,dim=0) reference required",
        )
    refs = read_spec(reference, task)
    if len(refs) != 64:
        raise Refusal("wave-sum-reference", "all 64 independent reference cells are required")
    return task, tr, refs


def render(task, tr, refs):
    declarations = "\n".join(
        f"def reference_{i} (ops : Ops α) (input : Nat → Nat → α) : α := {lean_spec(expr)}"
        for i, expr in enumerate(refs)
    )
    equalities = "\n".join(
        f"theorem reference_data_{i} (ops : Ops α) (input : Nat → Nat → α) :\n"
        f"    reference_{i} ops input = reference_0 ops input := by rfl"
        for i in range(1, 64)
    )
    proof_names = ", ".join(f"reference_data_{i}" for i in range(1, 64))
    return f"""import LarkReal.WaveSum
namespace LarkCertificate
open LarkNonlinear
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
def layout : Layout := ⟨{lean_list(f"⟨.{b.role}, {b.size}⟩" for b in task.buffers)}, [], []⟩
def geometry : Geometry := ⟨{task.grid}, {task.block}, {task.warp}⟩
def fuel : Fuel := ⟨{", ".join(map(str, task.fuel))}⟩
def program : List LarkCollective.Instr := {lean_list(collective.emit(i) for i in tr.program)}
{declarations}
def spec (ops : Ops α) (input : Nat → Nat → α) : List α :=
  {lean_list(f"reference_{i} ops input" for i in range(len(refs)))}
{equalities}
theorem reference_canonical (input : Nat → Nat → ℝ) :
    reference_0 LarkReal.ops input = ((List.range 64).map (input 0)).sum := by
  have hf := LarkReal.fold_add (List.range 64) (input 0) 0
  have hr : reference_0 LarkReal.ops input =
      (List.range 64).foldl (fun acc i => acc + input 0 i) 0 := by
    norm_num [reference_0, LarkReal.ops, List.range_succ, List.foldl_cons]
  rewrite [hr, hf, zero_add]
  rfl
theorem reference_spec (input : Nat → Nat → ℝ) :
    spec LarkReal.ops input = LarkReal.WaveSum.spec input := by
  simp only [spec, {proof_names}, reference_canonical]
  rfl
theorem layout_data : layout = LarkCollective.WaveSum.layout := by rfl
theorem geometry_data : geometry = LarkCollective.WaveSum.geometry := by rfl
theorem fuel_data : fuel = LarkCollective.WaveSum.fuel := by rfl
theorem segmentation_data : program = LarkCollective.WaveSum.program := by rfl
theorem segmentation (input : Nat → Nat → ℝ) (outside : Location → Option ℝ) :
    LarkCollective.runLaunch LarkReal.ops layout geometry fuel program (initial layout input outside) =
      some (LarkCollective.WaveSum.finalPartial LarkReal.ops input outside 64) := by
  rewrite [segmentation_data, layout_data, geometry_data, fuel_data]
  exact LarkCollective.WaveSum.launch_eq LarkReal.ops input outside
theorem race_free (input : Nat → Nat → ℝ) (outside : Location → Option ℝ) :
    raceFree geometry (LarkCollective.WaveSum.finalPartial LarkReal.ops input outside 64).trace = true := by
  exact LarkCollective.owned_raceFree geometry _
    (LarkCollective.WaveSum.final_owned LarkReal.ops input outside 64)
theorem segment_equivalence (input : Nat → Nat → ℝ) (outside : Location → Option ℝ) :
    extract layout (LarkCollective.WaveSum.finalPartial LarkReal.ops input outside 64) =
      some (spec LarkReal.ops input) := by
  have hs : LarkCollective.WaveSum.spec LarkReal.ops input = spec LarkReal.ops input :=
    (LarkReal.WaveSum.spec_eq input).trans (reference_spec input).symm
  rewrite [layout_data]
  exact (LarkCollective.WaveSum.final_extract LarkReal.ops input outside).trans (congrArg some hs)
theorem kernel_eq_spec :
    LarkCollective.Correct LarkReal.ops layout geometry fuel program (spec LarkReal.ops) := by
  intro input outside
  exact ⟨LarkCollective.WaveSum.finalPartial LarkReal.ops input outside 64,
    segmentation input outside, race_free input outside, segment_equivalence input outside⟩
theorem kernel_eq_spec_pre (input : Nat → Nat → ℝ) (s : State ℝ) (pre : StdPre layout input s) :
    ∃ final, LarkCollective.runLaunch LarkReal.ops layout geometry fuel program s = some final ∧
      raceFree geometry final.trace = true ∧ extract layout final = some (spec LarkReal.ops input) := by
  exact LarkCollective.correct_from_pre LarkReal.ops layout geometry fuel program
    (spec LarkReal.ops) kernel_eq_spec input s pre
#print axioms segmentation_data
#print axioms segmentation
#print axioms race_free
#print axioms segment_equivalence
#print axioms kernel_eq_spec
#print axioms kernel_eq_spec_pre
end LarkCertificate
"""


def validate_main(main, lean, timeout):
    _, task_env = real_backend.prepare(libraries(), lean, timeout)
    with tempfile.TemporaryDirectory(prefix="lark-wave-sum-check-") as temporary:
        directory = Path(temporary)
        (directory / "Main.lean").write_bytes(main)
        (directory / "lean-toolchain").write_bytes(real_backend.configuration()["lean-toolchain"])
        return run_lean(directory, lean, timeout, env=task_env)


def verify(kernel, reference, task_path, output, *, lean=None, timeout=300):
    if output.exists() or timeout <= 0:
        raise Refusal("configuration", "fresh output and positive timeout required")
    sources = {
        "kernel.hip": kernel.read_bytes(),
        "reference.py": reference.read_bytes(),
        "task.json": task_path.read_bytes(),
    }
    task, tr, refs = prepare(
        *(sources[n].decode("utf-8") for n in ("kernel.hip", "reference.py", "task.json"))
    )
    files = {**sources, **libraries(), **real_backend.configuration()}
    files["Main.lean"] = render(task, tr, refs).encode()
    files["translation.json"] = (json.dumps(tr.data(), indent=2) + "\n").encode()
    output.mkdir(parents=True)
    for name, content in files.items():
        path = output / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(content)
    accepted, log = validate_main(files["Main.lean"], lean_binary(lean), timeout)
    (output / "lean-1.log").write_text(log)
    report = {
        "schema": 1,
        "status": "verified" if accepted else "unproved",
        "model_profile": PROFILE,
        "files": {name: digest(content) for name, content in sorted(files.items())},
        "model_hashes": {name: digest(content) for name, content in libraries().items()},
        "mathlib_commit": real_backend.MATHLIB,
        "source_readback": True,
        "output_elements": 64,
        "input_elements": 64,
        "instructions": 16,
        "axiom_audit": log,
        "model_calls": 0,
        "original_paper_fully_reproduced": False,
        "trusted_assumptions": [
            "Lean 4.19.0 and the printed standard axioms",
            "Pinned unchanged nonlinear/collective machines and opcode-to-hardware correspondence",
            "Pinned Mathlib sources, dependencies and compiled import cache",
            "HIP reader/lowering and closed independent Torch AST interpretation",
            "Host uses aligned disjoint contiguous float32[64] buffers and one native wave64 block",
            "Exact-real arithmetic; no IEEE equality or numerical-error theorem",
            "Race-free phase reduction to hardware interleavings remains external metatheory",
        ],
        "scope": "Independent full-wave64 six-stage XOR butterfly. Actual complete launch, RF and all 64 independent-reference outputs for every real input and initial outside memory. No original production-kernel result, packed/tiled kernel, other subgroup shape or floating-point error bound.",
    }
    write_json(output / "report.json", report)
    return report


def check(directory, *, lean=None, timeout=300):
    report = json.loads((directory / "report.json").read_bytes().decode("utf-8"))
    expected_files = BASE_FILES | set(libraries()) | set(real_backend.configuration())
    if report.get("model_profile") != PROFILE or set(report["files"]) != expected_files:
        raise Refusal("integrity", "unexpected real wave-sum profile/files")
    for name, h in report["files"].items():
        path = directory / name
        if path.is_symlink() or digest(path.read_bytes()) != h:
            raise Refusal("integrity", "certificate file differs: " + name)
    for name, content in {**libraries(), **real_backend.configuration()}.items():
        if (directory / name).read_bytes() != content:
            raise Refusal("integrity", "pinned proof source/configuration differs: " + name)
    if (
        report["model_hashes"] != {name: digest(content) for name, content in libraries().items()}
        or report["mathlib_commit"] != real_backend.MATHLIB
    ):
        raise Refusal("integrity", "different pinned proof libraries/Mathlib")
    task, tr, refs = prepare(
        *(
            (directory / name).read_bytes().decode("utf-8")
            for name in ("kernel.hip", "reference.py", "task.json")
        )
    )
    if json.loads((directory / "translation.json").read_text()) != json.loads(
        json.dumps(tr.data())
    ):
        raise Refusal("integrity", "translation differs from exact source")
    expected = render(task, tr, refs).encode()
    if (directory / "Main.lean").read_bytes() != expected:
        raise Refusal("integrity", "theorem differs from fixed source/reference statement")
    if any(
        type(report.get(name)) is not int or report[name] != value
        for name, value in {"output_elements": 64, "input_elements": 64, "instructions": 16}.items()
    ):
        raise Refusal("integrity", "reported dimensions/instructions differ")
    accepted, log = validate_main(expected, lean_binary(lean), timeout)
    if not accepted:
        raise Refusal("proof", log)
    return log
