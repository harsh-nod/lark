"""Source-bound native weighted RMSNorm with whole-launch canonical-real proofs."""

import json
from pathlib import Path
import tempfile

from . import collective, native_rmsnorm, partition_collective, real_backend
from .certificate import digest, lean_binary, run_lean, write_json
from .ir import Refusal, lean_list

PROFILE = "native-rmsnorm-real-v17"
TARGET = "LarkReal.NativeRmsNorm"
BASE_FILES = {"Main.lean", "kernel.hip", "reference.py", "task.json", "translation.json"}
SCOPE = (
    "Independent weighted FP16 RMSNorm adaptation at width 16384, 1<=rows<256, "
    "native block1024/wave64, vector8, epsilon1e-5 and fuel[256,8,3,1]. "
    "Actual complete launch, actual-trace race freedom and every canonical-real "
    "reference output for every real input and initial outside memory. "
    "No IEEE equivalence/error bound, full upstream API or original-paper result."
)
ASSUMPTIONS = [
    "Lean 4.19.0 and the printed standard axioms",
    "Pinned nonlinear/partition-collective machines and opcode-to-hardware correspondence",
    "Pinned Mathlib sources, dependencies and compiled import cache",
    "HIP reader/lowering and the closed weighted Torch RMSNorm AST interpretation",
    "Host uses aligned disjoint contiguous FP16 rows and one shared weight vector",
    "Explicit guarded reduction rewrite; no CUB/rocPRIM floating-point equivalence theorem",
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
    task = native_rmsnorm.parse_task(task_source)
    native_rmsnorm.check_reference(reference, task)
    tr = partition_collective.translate(source, task)
    if [size for _, size in tr.shared] != [16, 1]:
        raise Refusal("native-rmsnorm", "the fixed shared partial[16] and scale[1] layout is required")
    return task, tr


def render(task, tr):
    rows = task.buffers[0].shape[0]
    return f"""import LarkReal.NativeRmsNorm
namespace LarkCertificate
open LarkNonlinear
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
def shape : LarkNativeRmsNorm.Shape := ⟨{rows}, by decide, by decide⟩
def layout : Layout := ⟨{lean_list(f"⟨.{b.role}, {b.size}⟩" for b in task.buffers)},
  {lean_list(str(size) for _, size in tr.shared)}, []⟩
def geometry : Geometry := ⟨{task.grid}, {task.block}, {task.warp}⟩
def fuel : Fuel := ⟨{", ".join(map(str, task.fuel))}⟩
def program : List LarkCollective.Instr := {lean_list(collective.emit(i) for i in tr.program)}
-- The closed reference AST is checked before this fixed mathematical interpretation
-- is emitted. Half/float conversions are identities in the exact-real model.
noncomputable def reference (input : Nat → Nat → ℝ) (row col : Nat) : ℝ :=
  input 1 (row * 16384 + col) *
    (1 / Real.sqrt ((((List.range 16384).map fun j =>
      input 1 (row * 16384 + j) * input 1 (row * 16384 + j)).sum) / 16384 + 1 / 100000)) * input 2 col
noncomputable def spec (input : Nat → Nat → ℝ) : List ℝ :=
  (List.range ({rows} * 16384)).map fun i => reference input (i / 16384) (i % 16384)
theorem reference_data (input : Nat → Nat → ℝ) :
    spec input = LarkReal.NativeRmsNorm.canonical_spec shape input := by rfl
theorem layout_data : layout = LarkNativeRmsNorm.layout shape := by rfl
theorem geometry_data : geometry = LarkNativeRmsNorm.geometry shape := by rfl
theorem fuel_data : fuel = LarkNativeRmsNorm.fuel := by rfl
theorem program_data : program = LarkNativeRmsNorm.program := by decide
theorem segmentation_data : program = LarkNativeRmsNorm.program := program_data
theorem segmentation (input : Nat → Nat → ℝ) (outside : Location → Option ℝ) :
    LarkPartitionCollective.runLaunch LarkReal.ops layout geometry fuel program (initial layout input outside) =
      some (LarkNativeRmsNorm.finalState shape LarkReal.ops input outside) := by
  rewrite [segmentation_data, layout_data, geometry_data, fuel_data]
  exact (LarkNativeRmsNorm.final_exec shape LarkReal.ops input outside).1
theorem race_free (input : Nat → Nat → ℝ) (outside : Location → Option ℝ) :
    raceFree geometry (LarkNativeRmsNorm.finalState shape LarkReal.ops input outside).trace = true := by
  rewrite [geometry_data]
  exact (LarkNativeRmsNorm.final_exec shape LarkReal.ops input outside).2
theorem segment_equivalence (input : Nat → Nat → ℝ) (outside : Location → Option ℝ) :
    extract layout (LarkNativeRmsNorm.finalState shape LarkReal.ops input outside) = some (spec input) := by
  have hs : LarkNativeRmsNorm.spec shape LarkReal.ops input = spec input :=
    (LarkReal.NativeRmsNorm.spec_eq shape input).trans (reference_data input).symm
  rewrite [layout_data]
  exact (LarkNativeRmsNorm.final_extract shape LarkReal.ops input outside).trans (congrArg some hs)
theorem kernel_eq_spec :
    LarkPartitionCollective.Correct LarkReal.ops layout geometry fuel program spec := by
  intro input outside
  exact ⟨LarkNativeRmsNorm.finalState shape LarkReal.ops input outside,
    segmentation input outside, race_free input outside, segment_equivalence input outside⟩
theorem kernel_eq_spec_pre (input : Nat → Nat → ℝ) (s : State ℝ) (pre : StdPre layout input s) :
    ∃ final, LarkPartitionCollective.runLaunch LarkReal.ops layout geometry fuel program s = some final ∧
      raceFree geometry final.trace = true ∧ extract layout final = some (spec input) := by
  obtain ⟨outside, rfl⟩ := pre
  exact kernel_eq_spec input outside
#print axioms reference_data
#print axioms program_data
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
    with tempfile.TemporaryDirectory(prefix="lark-native-rmsnorm-check-") as temporary:
        directory = Path(temporary)
        (directory / "Main.lean").write_bytes(main)
        (directory / "lean-toolchain").write_bytes(real_backend.configuration()["lean-toolchain"])
        return run_lean(directory, lean, timeout, env=task_env)


def dimensions(task, tr):
    rows = task.buffers[0].shape[0]
    return {
        "rows": rows,
        "output_elements": rows * 16384,
        "input_elements": (rows + 1) * 16384,
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
        raise Refusal("integrity", "unexpected native RMSNorm profile/files")
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
        or report.get("original_paper_fully_reproduced") is not False
        or type(report.get("model_calls")) is not int or report["model_calls"] != 0
        or report.get("scope") != SCOPE or report.get("trusted_assumptions") != ASSUMPTIONS
    ):
        raise Refusal("integrity", "reported proof scope differs from this independent native profile")
    accepted, log = validate_main(expected, proof_sources, lean_binary(lean), timeout)
    if not accepted:
        raise Refusal("proof", log)
    return log
