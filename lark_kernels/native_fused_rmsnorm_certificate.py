"""Source-bound native fused add RMSNorm with whole-launch canonical-real proofs."""

import json
from pathlib import Path
import tempfile

from . import collective, native_fused_rmsnorm, real_backend
from .certificate import digest, lean_binary, run_lean, write_json
from .ir import Refusal, lean_list

PROFILE = "native-fused-rmsnorm-real-v18"
TARGET = "LarkReal.NativeFusedRmsNorm"
BASE_FILES = {"Main.lean", "kernel.hip", "reference.py", "task.json", "translation.json"}
SCOPE = (
    "Independent in-place FP16 fused add RMSNorm adaptation at width 16384, 1<=rows<256, "
    "native block1024/wave64, vector8, epsilon1e-5 and fuel[512,8,3,1]. "
    "Actual complete launch, actual-trace race freedom and every canonical-real "
    "reference output and residual for every real input and initial outside memory. "
    "No IEEE equivalence/error bound, full upstream API or original-paper result."
)
ASSUMPTIONS = [
    "Lean 4.19.0 and the printed standard axioms",
    "Pinned nonlinear/partition-collective machines and opcode-to-hardware correspondence",
    "Pinned Mathlib sources, dependencies and compiled import cache",
    "HIP reader/lowering and the closed two-output Torch fused RMSNorm AST interpretation",
    "Host uses aligned disjoint contiguous FP16 rows and initialized mutable input/residual buffers and one read-only weight vector",
    "Explicit guarded logical32 XOR reduction; no original-library floating-point equivalence theorem",
    "Exact-real arithmetic; no IEEE equality or numerical-error theorem",
    "Race-free phase reduction to hardware interleavings remains external metatheory",
]


def libraries():
    """Read the transitive bundled proof imports of the fixed profile target."""
    pending = {TARGET}
    result = {}
    while pending:
        module = pending.pop()
        relative = module.replace(".", "/") + ".lean"
        if relative in result:
            continue
        prefix = "lean-real/" if module.startswith("LarkReal.") else "lean/"
        content = real_backend.resource(prefix + relative).read_bytes()
        result[relative] = content
        for line in content.decode("utf-8").splitlines():
            if line.startswith("import "):
                pending.update(
                    name for name in line.split()[1:] if name.startswith(("Lark.", "LarkReal."))
                )
    return dict(sorted(result.items()))


def prepare(source, reference, task_source):
    contract = native_fused_rmsnorm.parse_task(task_source)
    native_fused_rmsnorm.check_reference(reference)
    tr = native_fused_rmsnorm.translate(source, contract)
    if [size for _, size in tr.shared] != [32, 16384]:
        raise Refusal("native-fused-rmsnorm", "fixed partial[32]/unrounded[16384] shared layout required")
    return contract, tr


def render(contract, tr):
    task = contract.task
    rows = task.grid
    return f"""import LarkReal.NativeFusedRmsNorm
namespace LarkCertificate
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
def shape : LarkNativeFusedRmsNorm.Shape := ⟨{rows}, by decide, by decide⟩
def layout : Layout := ⟨{lean_list(f"⟨.{b.role}, {b.size}⟩" for b in task.buffers)},
  {lean_list(str(size) for _, size in tr.shared)}, []⟩
def mutableBuffers : List Nat := {list(contract.inout)}
def geometry : Geometry := ⟨{task.grid}, {task.block}, {task.warp}⟩
def fuel : Fuel := ⟨{", ".join(map(str, task.fuel))}⟩
def program : List LarkCollective.Instr := {lean_list(collective.emit(i) for i in tr.program)}
-- The closed two-output reference AST is checked before this interpretation.
-- Half/float conversions are identities only in this exact-real model.
def referenceSquare (input : Nat → Nat → ℝ) (row col : Nat) : ℝ :=
  let x := input 0 (row * 16384 + col) + input 1 (row * 16384 + col)
  x * x
noncomputable def reference (input : Nat → Nat → ℝ) (row col : Nat) : ℝ :=
  (input 0 (row * 16384 + col) + input 1 (row * 16384 + col)) *
    (1 / Real.sqrt ((((List.range 16384).map (referenceSquare input row)).sum) / 16384 + 1 / 100000)) *
    input 2 col
def referenceResidual (input : Nat → Nat → ℝ) (row col : Nat) : ℝ :=
  input 0 (row * 16384 + col) + input 1 (row * 16384 + col)
noncomputable def spec (input : Nat → Nat → ℝ) : List ℝ :=
  (List.range ({rows} * 16384)).map (fun i => reference input (i / 16384) (i % 16384)) ++
  (List.range ({rows} * 16384)).map (fun i => referenceResidual input (i / 16384) (i % 16384))
theorem reference_data (input : Nat → Nat → ℝ) :
    spec input = LarkReal.NativeFusedRmsNorm.canonical_spec shape input := by rfl
theorem layout_data : layout = LarkNativeFusedRmsNorm.layout shape := by rfl
theorem mutable_data : mutableBuffers = LarkNativeFusedRmsNorm.mutableBuffers := by decide
theorem geometry_data : geometry = LarkNativeFusedRmsNorm.geometry shape := by rfl
theorem fuel_data : fuel = LarkNativeFusedRmsNorm.fuel := by rfl
theorem program_data : program = LarkNativeFusedRmsNorm.program := by decide
theorem interface_data : LarkInOut.Valid layout mutableBuffers := by
  rewrite [layout_data,mutable_data]
  exact LarkNativeFusedRmsNorm.interface_valid shape
theorem segmentation_data : program = LarkNativeFusedRmsNorm.program := program_data
theorem segmentation (input : Nat → Nat → ℝ) (outside : Location → Option ℝ) :
    LarkPartitionCollective.runLaunch LarkReal.ops layout geometry fuel program
      (LarkInOut.initial layout mutableBuffers input outside) =
      some (LarkNativeFusedRmsNorm.finalState shape LarkReal.ops input outside) := by
  rewrite [segmentation_data,layout_data,mutable_data,geometry_data,fuel_data]
  exact (LarkNativeFusedRmsNorm.final_exec shape LarkReal.ops input outside).1
theorem race_free (input : Nat → Nat → ℝ) (outside : Location → Option ℝ) :
    raceFree geometry (LarkNativeFusedRmsNorm.finalState shape LarkReal.ops input outside).trace = true := by
  rewrite [geometry_data]
  exact (LarkNativeFusedRmsNorm.final_exec shape LarkReal.ops input outside).2
theorem segment_equivalence (input : Nat → Nat → ℝ) (outside : Location → Option ℝ) :
    extract layout (LarkNativeFusedRmsNorm.finalState shape LarkReal.ops input outside) = some (spec input) := by
  have hs : LarkNativeFusedRmsNorm.spec shape LarkReal.ops input = spec input :=
    (LarkReal.NativeFusedRmsNorm.spec_eq shape input).trans (reference_data input).symm
  rewrite [layout_data]
  exact (LarkNativeFusedRmsNorm.final_extract shape LarkReal.ops input outside).trans (congrArg some hs)
theorem kernel_eq_spec :
    LarkInOutPartition.Correct LarkReal.ops layout mutableBuffers geometry fuel program spec := by
  refine ⟨interface_data,?_⟩
  intro input outside
  exact ⟨LarkNativeFusedRmsNorm.finalState shape LarkReal.ops input outside,
    segmentation input outside,race_free input outside,segment_equivalence input outside⟩
theorem kernel_eq_spec_pre (input : Nat → Nat → ℝ) (s : State ℝ)
    (pre : LarkInOut.StdPre layout mutableBuffers input s) :
    ∃ final, LarkPartitionCollective.runLaunch LarkReal.ops layout geometry fuel program s = some final ∧
      raceFree geometry final.trace = true ∧ extract layout final = some (spec input) :=
  LarkInOutPartition.correct_from_pre LarkReal.ops layout mutableBuffers geometry fuel program spec
    kernel_eq_spec input s pre
#print axioms reference_data
#print axioms mutable_data
#print axioms program_data
#print axioms interface_data
#print axioms segmentation_data
#print axioms segmentation
#print axioms race_free
#print axioms segment_equivalence
#print axioms kernel_eq_spec
#print axioms kernel_eq_spec_pre
end LarkCertificate
"""


def validate_main(main, proof_sources, lean, timeout):
    _, task_env = real_backend.prepare(proof_sources, lean, timeout, target=TARGET)
    with tempfile.TemporaryDirectory(prefix="lark-native-fused-rmsnorm-check-") as temporary:
        directory = Path(temporary)
        (directory / "Main.lean").write_bytes(main)
        (directory / "lean-toolchain").write_bytes(real_backend.configuration()["lean-toolchain"])
        return run_lean(directory, lean, timeout, env=task_env)


def dimensions(contract, tr):
    rows = contract.task.grid
    return {
        "rows": rows,
        "output_elements": 2 * rows * 16384,
        "normalized_elements": rows * 16384,
        "residual_elements": rows * 16384,
        "input_elements": (2 * rows + 1) * 16384,
        "instructions": len(tr.program),
    }


def verify(kernel, reference, task_path, output, *, lean=None, timeout=600):
    if output.exists() or timeout <= 0:
        raise Refusal("configuration", "fresh output and positive timeout required")
    sources = {
        "kernel.hip": kernel.read_bytes(),
        "reference.py": reference.read_bytes(),
        "task.json": task_path.read_bytes(),
    }
    task, tr = prepare(*(sources[n].decode("utf-8") for n in ("kernel.hip", "reference.py", "task.json")))
    proof_sources = libraries()
    files = {**sources, **proof_sources, **real_backend.configuration()}
    files["Main.lean"] = render(task, tr).encode()
    files["translation.json"] = (json.dumps(tr.data(), indent=2) + "\n").encode()
    output.mkdir(parents=True)
    for name, content in files.items():
        path = output / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(content)
    accepted, log = validate_main(files["Main.lean"], proof_sources, lean_binary(lean), timeout)
    (output / "lean-1.log").write_text(log)
    report = {
        "schema": 1,
        "status": "verified" if accepted else "unproved",
        "model_profile": PROFILE,
        "files": {name: digest(content) for name, content in sorted(files.items())},
        "model_hashes": {name: digest(content) for name, content in proof_sources.items()},
        "mathlib_commit": real_backend.MATHLIB,
        "source_readback": True,
        "whole_launch_proved": accepted,
        "seeded_inout_proved": accepted,
        "both_output_buffers_extracted": accepted,
        "source_reference_equality_proved": accepted,
        "ieee_equivalence_proved": False,
        "floating_point_error_bound_proved": False,
        **dimensions(task, tr),
        "axiom_audit": log,
        "model_calls": 0,
        "original_paper_fully_reproduced": False,
        "trusted_assumptions": ASSUMPTIONS,
        "scope": SCOPE,
    }
    write_json(output / "report.json", report)
    return report


def check(directory, *, lean=None, timeout=600):
    report = json.loads((directory / "report.json").read_text())
    proof_sources = libraries()
    configuration = real_backend.configuration()
    expected_files = BASE_FILES | set(proof_sources) | set(configuration)
    if report.get("model_profile") != PROFILE or set(report["files"]) != expected_files:
        raise Refusal("integrity", "unexpected native fused RMSNorm profile/files")
    for name, h in report["files"].items():
        path = directory / name
        if path.is_symlink() or digest(path.read_bytes()) != h:
            raise Refusal("integrity", "certificate file differs: " + name)
    for name, content in {**proof_sources, **configuration}.items():
        if (directory / name).read_bytes() != content:
            raise Refusal("integrity", "pinned proof source/configuration differs: " + name)
    if report["model_hashes"] != {name: digest(content) for name, content in proof_sources.items()} or report["mathlib_commit"] != real_backend.MATHLIB:
        raise Refusal("integrity", "different pinned proof libraries/Mathlib")
    task, tr = prepare(*((directory / name).read_text() for name in ("kernel.hip", "reference.py", "task.json")))
    if json.loads((directory / "translation.json").read_text()) != json.loads(json.dumps(tr.data())):
        raise Refusal("integrity", "translation differs from exact source")
    expected = render(task, tr).encode()
    if (directory / "Main.lean").read_bytes() != expected:
        raise Refusal("integrity", "theorem differs from fixed source/reference statement")
    if any(type(report.get(name)) is not int or report[name] != value for name, value in dimensions(task, tr).items()):
        raise Refusal("integrity", "reported dimensions/instructions differ")
    if (
        report.get("schema") != 1 or report.get("status") != "verified"
        or report.get("source_readback") is not True or report.get("whole_launch_proved") is not True
        or any(report.get(name) is not True for name in (
            "seeded_inout_proved", "both_output_buffers_extracted", "source_reference_equality_proved"))
        or any(report.get(name) is not False for name in (
            "ieee_equivalence_proved", "floating_point_error_bound_proved", "original_paper_fully_reproduced"))
        or type(report.get("model_calls")) is not int or report["model_calls"] != 0
        or report.get("scope") != SCOPE or report.get("trusted_assumptions") != ASSUMPTIONS
    ):
        raise Refusal("integrity", "reported proof scope differs from this independent native profile")
    accepted, log = validate_main(expected, proof_sources, lean_binary(lean), timeout)
    if not accepted:
        raise Refusal("proof", log)
    return log
