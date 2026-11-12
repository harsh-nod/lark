"""Source-bound complete split-half Q/K RMSNorm + RoPE exact-real certificates."""

import json
from pathlib import Path
import tempfile

from . import collective, native_qknorm_rope as native, real_backend
from .certificate import digest, lean_binary, run_lean, write_json
from .ir import Refusal, lean_list

PROFILE = "native-qknorm-rope-split-half-real-v21"
TARGET = "LarkReal.NativeQKNormRopeSplit"
BASE_FILES = {"Main.lean", "kernel.hip", "reference.py", "task.json", "translation.json"}
SCOPE = (
    "Independent FP16 fused Q/K RMSNorm and split-half RoPE adaptation: 1..65535 rows, "
    "Q32/K8/V8 heads of width128, separate Q/K output, Q/K weights and gathered cache, "
    "native block256/wave64, logical32 XOR reduction, epsilon1e-5 and fuel[256,16,1,1]. "
    "Complete actual launch, actual-trace race freedom, read-only inputs and all outputs "
    "equal the independent dense exact-real reference for every input and outside memory. "
    "No IEEE/error guarantee, complete upstream API, original-paper "
    "result or NVIDIA execution."
)
ASSUMPTIONS = [
    "Lean4.19.0 and the printed standard axioms",
    "Pinned nonlinear/partition-collective machines and opcode-to-hardware correspondence",
    "Pinned Mathlib sources, dependencies and compiled import cache",
    "HIP reader/lowering, lossless read-back and the closed fused normalization/rotary Torch AST interpretation",
    "Host honors disjoint contiguous FP16 output/QKV/Q-weight/K-weight/gathered-cache regions",
    "Fixed Q32/K8/V8 heads and width128; gathered cache rows and split-half rotation",
    "Exact-real arithmetic with identity storage conversions; no IEEE equality/error theorem",
    "Race-free phase reduction to hardware interleavings remains external metatheory",
]
TRUE_CLAIMS = (
    "source_readback", "whole_launch_proved", "actual_trace_race_freedom_proved",
    "readonly_inputs_proved", "all_output_elements_extracted", "source_reference_equality_proved", "split_half_proved",
)
FALSE_CLAIMS = (
    "ieee_equivalence_proved", "floating_point_error_bound_proved",
    "original_paper_fully_reproduced",
)
REPORT_FIELDS = {
    "schema", "status", "model_profile", "files", "model_hashes", "mathlib_commit",
    "rows", "query_heads", "key_heads", "value_heads", "head_size", "block", "warp",
    "output_elements", "input_elements", "instructions", "rotary_layout", "axiom_audit",
    "model_calls", "trusted_assumptions", "scope", *TRUE_CLAIMS, *FALSE_CLAIMS,
}


def libraries():
    """Transitive owned source closure; only pinned external Mathlib imports are seeded."""
    pending, result = {TARGET}, {}
    while pending:
        module = pending.pop()
        relative = module.replace(".", "/") + ".lean"
        if relative in result:
            continue
        prefix = "lean-real/" if module.startswith("LarkReal.") else "lean/"
        content = real_backend.resource(prefix + relative).read_bytes()
        result[relative] = content
        for line in content.decode().splitlines():
            if line.startswith("import "):
                pending.update(name for name in line.split()[1:]
                               if name.startswith(("Lark.", "LarkReal.")))
    return dict(sorted(result.items()))


def prepare(source, reference, task_source):
    contract = native.parse_task(task_source)
    if contract.rotary_layout != "split-half":
        raise Refusal("native-qknorm-rope-proof", "complete exact-real split-half certificate requires split-half layout")
    native.check_reference(reference, contract.rotary_layout)
    tr = native.translate(source, contract)
    if tr.shared:
        raise Refusal("native-qknorm-rope-proof", "closed profile has no shared allocation")
    return contract, tr


def render(contract, tr):
    task, rows = contract.task, contract.rows
    return f'''import {TARGET}
namespace LarkCertificate
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
def shape : LarkNativeQKNormRope.Shape := ⟨{rows}, by decide, by decide⟩
def layout : Layout := ⟨{lean_list(f"⟨.{b.role}, {b.size}⟩" for b in task.buffers)}, [], []⟩
def geometry : Geometry := ⟨{task.grid}, {task.block}, {task.warp}⟩
def fuel : Fuel := ⟨{", ".join(map(str, task.fuel))}⟩
def program : List LarkCollective.Instr := {lean_list(collective.emit(i) for i in tr.program)}
-- The closed reference AST is checked before this independent dense interpretation.
-- Half/float conversions are identities in the exact-real operation model.
def referenceSquare (input : Nat → Nat → ℝ) (row head col : Nat) : ℝ :=
  let x := input 1 (row * 6144 + head * 128 + col)
  x * x
noncomputable def referenceScale (input : Nat → Nat → ℝ) (row head : Nat) : ℝ :=
  1 / Real.sqrt ((((List.range 128).map (referenceSquare input row head)).sum) / 128 + 1 / 100000)
noncomputable def referenceNormalized (input : Nat → Nat → ℝ) (row head col : Nat) : ℝ :=
  input 1 (row * 6144 + head * 128 + col) *
    (referenceScale input row head * input (if head < 32 then 2 else 3) col)
noncomputable def reference (input : Nat → Nat → ℝ) (row head col : Nat) : ℝ :=
  let halfColumn := col % 64
  let x := referenceNormalized input row head halfColumn
  let y := referenceNormalized input row head (halfColumn + 64)
  let cosine := input 4 (row * 128 + halfColumn)
  let sine := input 4 (row * 128 + halfColumn + 64)
  if col < 64 then x * cosine + (-y) * sine else y * cosine + x * sine
noncomputable def spec (input : Nat → Nat → ℝ) : List ℝ :=
  (List.range ({rows} * 5120)).map (fun i => reference input (i / 5120) (i % 5120 / 128) (i % 128))
theorem reference_data (input : Nat → Nat → ℝ) :
    spec input = LarkReal.NativeQKNormRope.Split.denseSpec shape input := by rfl
theorem layout_data : layout = LarkNativeQKNormRope.layout shape := by rfl
theorem geometry_data : geometry = LarkNativeQKNormRope.geometry shape := by rfl
theorem fuel_data : fuel = LarkNativeQKNormRope.fuel := by rfl
theorem program_data : program = LarkNativeQKNormRope.program true := by decide
theorem segmentation_data : program = LarkNativeQKNormRope.program true := program_data
theorem segmentation (input : Nat → Nat → ℝ) (outside : Location → Option ℝ) :
    LarkPartitionCollective.runLaunch LarkReal.ops layout geometry fuel program
      (initial layout input outside) =
      some (LarkNativeQKNormRope.splitFinalState shape LarkReal.ops input outside) := by
  rw [segmentation_data, layout_data, geometry_data, fuel_data]
  exact LarkNativeQKNormRope.split_final_launch shape LarkReal.ops input outside
theorem race_free (input : Nat → Nat → ℝ) (outside : Location → Option ℝ) :
    raceFree geometry (LarkNativeQKNormRope.splitFinalState shape LarkReal.ops input outside).trace = true := by
  rw [geometry_data]
  exact LarkNativeQKNormRope.split_final_race_free shape LarkReal.ops input outside
theorem readonly_inputs (input : Nat → Nat → ℝ) (outside : Location → Option ℝ) :
    LarkNativeQKNormRope.Reads shape input
      (LarkNativeQKNormRope.splitFinalState shape LarkReal.ops input outside) :=
  LarkNativeQKNormRope.split_final_readonly shape LarkReal.ops input outside
theorem segment_equivalence (input : Nat → Nat → ℝ) (outside : Location → Option ℝ) :
    extract layout (LarkNativeQKNormRope.splitFinalState shape LarkReal.ops input outside) = some (spec input) := by
  rw [layout_data]
  exact (LarkReal.NativeQKNormRope.Split.final_extract shape input outside).trans
    (congrArg some (reference_data input).symm)
theorem kernel_eq_spec :
    LarkPartitionCollective.Correct LarkReal.ops layout geometry fuel program spec := by
  intro input outside
  exact ⟨LarkNativeQKNormRope.splitFinalState shape LarkReal.ops input outside,
    segmentation input outside, race_free input outside, segment_equivalence input outside⟩
theorem kernel_eq_spec_pre (input : Nat → Nat → ℝ) (s : State ℝ) (pre : StdPre layout input s) :
    ∃ final, LarkPartitionCollective.runLaunch LarkReal.ops layout geometry fuel program s = some final ∧
      raceFree geometry final.trace = true ∧ extract layout final = some (spec input) := by
  obtain ⟨outside, rfl⟩ := pre
  exact kernel_eq_spec input outside
#print axioms reference_data
#print axioms layout_data
#print axioms geometry_data
#print axioms fuel_data
#print axioms program_data
#print axioms segmentation_data
#print axioms segmentation
#print axioms race_free
#print axioms readonly_inputs
#print axioms segment_equivalence
#print axioms kernel_eq_spec
#print axioms kernel_eq_spec_pre
end LarkCertificate
'''


def validate_main(main, proof_sources, lean, timeout):
    _, task_env = real_backend.prepare(proof_sources, lean, timeout, target=TARGET)
    with tempfile.TemporaryDirectory(prefix="lark-native-qknorm-rope-split-check-") as temporary:
        directory = Path(temporary)
        (directory / "Main.lean").write_bytes(main)
        (directory / "lean-toolchain").write_bytes(real_backend.configuration()["lean-toolchain"])
        return run_lean(directory, lean, timeout, env=task_env)


def dimensions(contract, tr):
    return {
        "rows": contract.rows, "query_heads": 32, "key_heads": 8, "value_heads": 8,
        "head_size": 128, "block": contract.task.block, "warp": contract.task.warp,
        "output_elements": contract.rows * 5120,
        "input_elements": contract.rows * (6144 + 128) + 256,
        "instructions": len(tr.program),
    }


def verify(kernel, reference, task_path, output, *, lean=None, timeout=600):
    if output.exists() or timeout <= 0:
        raise Refusal("configuration", "fresh output and positive timeout required")
    sources = {"kernel.hip": kernel.read_bytes(), "reference.py": reference.read_bytes(),
               "task.json": task_path.read_bytes()}
    contract, tr = prepare(*(sources[n].decode() for n in ("kernel.hip", "reference.py", "task.json")))
    proof_sources = libraries()
    files = {**sources, **proof_sources, **real_backend.configuration(),
             "Main.lean": render(contract, tr).encode(),
             "translation.json": (json.dumps(tr.data(), indent=2) + "\n").encode()}
    output.mkdir(parents=True)
    for name, content in files.items():
        path = output / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(content)
    accepted, log = validate_main(files["Main.lean"], proof_sources, lean_binary(lean), timeout)
    (output / "lean-1.log").write_text(log)
    report = {
        "schema": 1, "status": "verified" if accepted else "unproved", "model_profile": PROFILE,
        "files": {name: digest(content) for name, content in sorted(files.items())},
        "model_hashes": {name: digest(content) for name, content in proof_sources.items()},
        "mathlib_commit": real_backend.MATHLIB, "rotary_layout": contract.rotary_layout,
        **{name: accepted for name in TRUE_CLAIMS}, **{name: False for name in FALSE_CLAIMS},
        "source_readback": True,
        **dimensions(contract, tr), "axiom_audit": log, "model_calls": 0,
        "trusted_assumptions": ASSUMPTIONS, "scope": SCOPE,
    }
    write_json(output / "report.json", report)
    return report


def check(directory, *, lean=None, timeout=600):
    if timeout <= 0:
        raise Refusal("configuration", "positive timeout required")
    report = json.loads((directory / "report.json").read_text())
    proof_sources, configuration = libraries(), real_backend.configuration()
    expected_files = BASE_FILES | set(proof_sources) | set(configuration)
    if (set(report) != REPORT_FIELDS or report.get("model_profile") != PROFILE
            or set(report["files"]) != expected_files):
        raise Refusal("integrity", "unexpected native Q/K normalization/rotary profile or files")
    for name, h in report["files"].items():
        path = directory / name
        if path.is_symlink() or any((directory / p).is_symlink() for p in Path(name).parents):
            raise Refusal("integrity", "certificate file must not traverse symlinks: " + name)
        if digest(path.read_bytes()) != h:
            raise Refusal("integrity", "certificate file differs: " + name)
    for name, content in {**proof_sources, **configuration}.items():
        if (directory / name).read_bytes() != content:
            raise Refusal("integrity", "pinned proof source/configuration differs: " + name)
    if (report["model_hashes"] != {name: digest(content) for name, content in proof_sources.items()}
            or report["mathlib_commit"] != real_backend.MATHLIB):
        raise Refusal("integrity", "different pinned proof libraries/Mathlib")
    contract, tr = prepare(*((directory / name).read_text() for name in ("kernel.hip", "reference.py", "task.json")))
    if json.loads((directory / "translation.json").read_text()) != json.loads(json.dumps(tr.data())):
        raise Refusal("integrity", "translation differs from exact source")
    expected = render(contract, tr).encode()
    if (directory / "Main.lean").read_bytes() != expected:
        raise Refusal("integrity", "theorem differs from fixed source/reference statement")
    if any(type(report.get(name)) is not int or report[name] != value
           for name, value in dimensions(contract, tr).items()):
        raise Refusal("integrity", "reported dimensions/instructions differ")
    if (type(report["schema"]) is not int or report["schema"] != 1 or report["status"] != "verified"
            or report["rotary_layout"] != "split-half"
            or any(report[name] is not True for name in TRUE_CLAIMS)
            or any(report[name] is not False for name in FALSE_CLAIMS)
            or type(report["model_calls"]) is not int or report["model_calls"] != 0
            or report["scope"] != SCOPE or report["trusted_assumptions"] != ASSUMPTIONS):
        raise Refusal("integrity", "reported proof scope differs from this independent native profile")
    accepted, log = validate_main(expected, proof_sources, lean_binary(lean), timeout)
    if not accepted:
        raise Refusal("proof", log)
    return log
