"""Source-bound whole-launch native in-place rotary certificates (Std only)."""

import json
from pathlib import Path
import sysconfig
import tempfile

from . import collective, native_rope, native_rope_backend as backend
from .certificate import TOOLCHAIN, digest, lean_binary, run_lean, write_json
from .ir import Refusal, lean_list

PROFILE = "native-rope-whole-v19"
TARGET = "Lark.NativeRopeCorrect"
BASE_FILES = {"Main.lean", "kernel.hip", "reference.py", "task.json", "translation.json", "lean-toolchain", "lakefile.toml"}
REPORT_FIELDS = {
    "schema", "status", "model_profile", "files", "model_hashes", "rows", "query_heads", "key_heads", "head_size",
    "block", "warp", "output_elements", "input_elements", "instructions", "rotary_layout", "source_readback",
    "whole_launch_proved", "actual_trace_race_freedom_proved", "seeded_inout_proved", "both_output_buffers_extracted",
    "source_reference_equality_proved", "ieee_equivalence_proved", "floating_point_error_bound_proved",
    "original_paper_fully_reproduced", "model_calls", "axiom_audit", "trusted_assumptions", "scope",
}
SCOPE = (
    "Independent native in-place vLLM RoPE adaptation: 1..65535 token rows, Q32/K8 heads, "
    "full128 rotation, FP16 query/key/gathered-cache storage, both fixed rotary layouts, "
    "block512/wave64 and fuel[256,1,1,1]. Complete actual launch, actual-trace race freedom "
    "and source-ordered extraction of both buffers against the dense reference for every "
    "input/outside memory under arbitrary scalar operations and explicit half conversions. "
    "No IEEE/error guarantee, complete upstream API, original-paper result or NVIDIA execution."
)
ASSUMPTIONS = [
    "Lean4.19.0 and the printed standard axioms",
    "Pinned nonlinear scalar machine and operation-to-hardware correspondence",
    "HIP reader/lowering, lossless read-back and the closed two-output Torch rotary AST interpretation",
    "Host honors disjoint contiguous FP16 Q/K/cache regions and initialized mutable Q/K buffers",
    "Already-gathered cache rows, fixed head/rotary sizes, inverse=false and zero rotary offset",
    "Universally quantified scalar operations and half conversions; no IEEE equality/error theorem",
    "Race-free phase reduction to hardware interleavings remains external metatheory",
]


def libraries():
    """Ordered transitive Std proof closure from source or installed resources."""
    result, active = {}, set()

    def visit(module):
        name = module.replace(".", "/") + ".lean"
        if name in result:
            return
        if name in active:
            raise Refusal("installation", "cyclic native RoPE proof imports")
        active.add(name)
        path = Path(__file__).resolve().parents[1] / "lean" / name
        if not path.is_file():
            path = Path(sysconfig.get_path("data")) / "share/lark/lean" / name
        if not path.is_file():
            raise Refusal("installation", "pinned native RoPE proof resource missing: " + name)
        content = path.read_bytes()
        for line in content.decode().splitlines():
            if line.startswith("import "):
                for imported in line.split()[1:]:
                    if imported.startswith("Lark."):
                        visit(imported)
                    elif imported != "Std":
                        raise Refusal("installation", "unexpected native RoPE external import")
        result[name] = content
        active.remove(name)

    visit(TARGET)
    return result


def prepare(source, reference, task_source):
    contract = native_rope.parse_task(task_source)
    native_rope.check_reference(reference, contract.rotary_layout)
    tr = native_rope.translate(source, contract)
    if tr.shared or any(i.op == "shuffle" for i in tr.program):
        raise Refusal("native-rope", "closed scalar native loop with no shared layout/shuffles required")
    return contract, tr


def render(contract, tr):
    task = contract.task
    rows = task.grid
    neox = str(contract.rotary_layout == "split-half").lower()
    return f'''import {TARGET}
namespace LarkCertificate
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
def shape : LarkNativeRope.Shape := ⟨{rows}, by decide, by decide⟩
def neox : Bool := {neox}
def layout : Layout := ⟨{lean_list(f"⟨.{b.role}, {b.size}⟩" for b in task.buffers)}, [], []⟩
def mutableBuffers : List Nat := {list(contract.inout)}
def geometry : Geometry := ⟨{task.grid}, {task.block}, {task.warp}⟩
def fuel : Fuel := ⟨{", ".join(map(str, task.fuel))}⟩
def program : List Instr := {lean_list(collective.emit(i)[len("(.scalar "):-1] for i in tr.program)}
-- The complete closed two-output reference AST is checked before interpretation.
def reference (ops : Ops α) (input : Nat → Nat → α) (buffer row col : Nat) : α :=
  let rowWidth := if buffer = 0 then 4096 else 1024
  let head := col / 128
  let j := if neox then col % 64 else col % 128 / 2
  let a := head * 128 + if neox then j else 2 * j
  let b := head * 128 + if neox then j + 64 else 2 * j + 1
  let x := ops.fromHalf (input buffer (row * rowWidth + a))
  let y := ops.fromHalf (input buffer (row * rowWidth + b))
  let c := ops.fromHalf (input 2 (row * 128 + j))
  let sn := ops.fromHalf (input 2 (row * 128 + j + 64))
  let imaginary := if neox then decide (64 ≤ col % 128) else decide (col % 2 = 1)
  ops.toHalf (if imaginary then ops.add (ops.mul y c) (ops.mul x sn) else ops.sub (ops.mul x c) (ops.mul y sn))
def spec (ops : Ops α) (input : Nat → Nat → α) : List α :=
  (List.range ({rows} * 4096)).map (fun i => reference ops input 0 (i / 4096) (i % 4096)) ++
  (List.range ({rows} * 1024)).map (fun i => reference ops input 1 (i / 1024) (i % 1024))
theorem reference_data (ops : Ops α) (input : Nat → Nat → α) :
    spec ops input = LarkNativeRope.spec shape neox ops input := by rfl
theorem layout_data : layout = LarkNativeRope.layout shape := by rfl
theorem mutable_data : mutableBuffers = LarkNativeRope.mutableBuffers := by decide
theorem geometry_data : geometry = LarkNativeRope.geometry shape := by rfl
theorem fuel_data : fuel = LarkNativeRope.fuel := by rfl
theorem program_data : program = LarkNativeRope.program neox := by decide
theorem interface_data : LarkInOut.Valid layout mutableBuffers := by
  rw [layout_data, mutable_data]
  exact LarkNativeRope.interface_valid shape
theorem segmentation_data : program = LarkNativeRope.program neox := program_data
theorem segmentation (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) :
    runLaunch ops layout geometry fuel program (LarkInOut.initial layout mutableBuffers input outside) =
      some (LarkNativeRope.finalState shape neox ops input outside) := by
  rw [segmentation_data, layout_data, mutable_data, geometry_data, fuel_data]
  exact (LarkNativeRope.final_launch shape neox ops input outside).1
theorem race_free (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) :
    raceFree geometry (LarkNativeRope.finalState shape neox ops input outside).trace = true := by
  rw [geometry_data]
  exact LarkNativeRope.final_race_free shape neox ops input outside
theorem segment_equivalence (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) :
    extract layout (LarkNativeRope.finalState shape neox ops input outside) = some (spec ops input) := by
  rw [layout_data]
  exact (LarkNativeRope.final_extract shape neox ops input outside).trans (congrArg some (reference_data ops input).symm)
theorem kernel_eq_spec (ops : Ops α) :
    LarkInOutScalar.Correct ops layout mutableBuffers geometry fuel program (spec ops) := by
  refine ⟨interface_data, ?_⟩
  intro input outside
  exact ⟨LarkNativeRope.finalState shape neox ops input outside,
    segmentation ops input outside, race_free ops input outside, segment_equivalence ops input outside⟩
theorem kernel_eq_spec_pre (ops : Ops α) (input : Nat → Nat → α) (s : State α)
    (pre : LarkInOut.StdPre layout mutableBuffers input s) :
    ∃ final, runLaunch ops layout geometry fuel program s = some final ∧
      raceFree geometry final.trace = true ∧ extract layout final = some (spec ops input) :=
  LarkInOutScalar.correct_from_pre ops layout mutableBuffers geometry fuel program (spec ops)
    (kernel_eq_spec ops) input s pre
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
'''


def validate_main(main, proof_sources, lean, timeout):
    # Compile the exact generated Main in a fresh directory, with no owned
    # import path and no certificate-provided build instructions.
    _, env = backend.prepare(proof_sources, lean, timeout)
    with tempfile.TemporaryDirectory(prefix="lark-native-rope-check-") as temporary:
        directory = Path(temporary)
        (directory / "Main.lean").write_bytes(main)
        (directory / "lean-toolchain").write_text(TOOLCHAIN)
        return run_lean(directory, lean, timeout, env=env)


def dimensions(contract, tr):
    rows = contract.task.grid
    return {"rows": rows, "query_heads": 32, "key_heads": 8, "head_size": 128,
            "block": 512, "warp": 64, "output_elements": rows * 5120,
            "input_elements": rows * 5248, "instructions": len(tr.program)}


def verify(kernel, reference, task_path, output, *, lean=None, timeout=600):
    if output.exists() or timeout <= 0:
        raise Refusal("configuration", "fresh output and positive timeout required")
    sources = {"kernel.hip": kernel.read_bytes(), "reference.py": reference.read_bytes(), "task.json": task_path.read_bytes()}
    contract, tr = prepare(*(sources[n].decode() for n in ("kernel.hip", "reference.py", "task.json")))
    proofs = libraries()
    files = {**sources, **proofs, **backend.configuration(),
             "Main.lean": render(contract, tr).encode(),
             "translation.json": (json.dumps(tr.data(), indent=2) + "\n").encode()}
    output.mkdir(parents=True)
    for name, content in files.items():
        path = output / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(content)
    accepted, log = validate_main(files["Main.lean"], proofs, lean_binary(lean), timeout)
    (output / "lean-1.log").write_text(log)
    report = {"schema": 1, "status": "verified" if accepted else "unproved", "model_profile": PROFILE,
              "files": {n: digest(v) for n, v in sorted(files.items())},
              "model_hashes": {n: digest(v) for n, v in sorted(proofs.items())},
              **dimensions(contract, tr), "rotary_layout": contract.rotary_layout,
              "source_readback": True, "whole_launch_proved": accepted,
              "actual_trace_race_freedom_proved": accepted,
              "seeded_inout_proved": accepted, "both_output_buffers_extracted": accepted,
              "source_reference_equality_proved": accepted, "ieee_equivalence_proved": False,
              "floating_point_error_bound_proved": False, "original_paper_fully_reproduced": False,
              "model_calls": 0, "axiom_audit": log, "trusted_assumptions": ASSUMPTIONS, "scope": SCOPE}
    write_json(output / "report.json", report)
    return report


def check(directory, *, lean=None, timeout=600):
    report = json.loads((directory / "report.json").read_text())
    if set(report) != REPORT_FIELDS:
        raise Refusal("integrity", "unexpected native RoPE report fields")
    proofs = libraries()
    configuration = backend.configuration()
    if report.get("model_profile") != PROFILE or set(report["files"]) != BASE_FILES | set(proofs):
        raise Refusal("integrity", "unexpected native RoPE profile/files")
    for name, expected in report["files"].items():
        path = directory / name
        if path.is_symlink() or digest(path.read_bytes()) != expected:
            raise Refusal("integrity", "certificate bytes differ: " + name)
    for name, content in {**proofs, **configuration}.items():
        if (directory / name).read_bytes() != content:
            raise Refusal("integrity", "pinned native proof source/configuration differs: " + name)
    if report["model_hashes"] != {n: digest(v) for n, v in sorted(proofs.items())}:
        raise Refusal("integrity", "different pinned native proof libraries")
    contract, tr = prepare(*((directory / n).read_text() for n in ("kernel.hip", "reference.py", "task.json")))
    if json.loads((directory / "translation.json").read_text()) != json.loads(json.dumps(tr.data())):
        raise Refusal("integrity", "translation differs from source")
    expected = render(contract, tr).encode()
    if (directory / "Main.lean").read_bytes() != expected:
        raise Refusal("integrity", "theorem differs from fixed source/reference statement")
    if any(type(report.get(k)) is not int or report[k] != v for k, v in dimensions(contract, tr).items()):
        raise Refusal("integrity", "reported dimensions/instructions differ")
    if (type(report.get("schema")) is not int or report["schema"] != 1 or report.get("status") != "verified"
            or report.get("rotary_layout") != contract.rotary_layout
            or any(report.get(k) is not True for k in ("source_readback", "whole_launch_proved", "actual_trace_race_freedom_proved", "seeded_inout_proved",
                                                       "both_output_buffers_extracted", "source_reference_equality_proved"))
            or any(report.get(k) is not False for k in ("ieee_equivalence_proved", "floating_point_error_bound_proved",
                                                        "original_paper_fully_reproduced"))
            or type(report.get("model_calls")) is not int or report["model_calls"] != 0
            or report.get("scope") != SCOPE or report.get("trusted_assumptions") != ASSUMPTIONS):
        raise Refusal("integrity", "reported proof scope differs")
    accepted, log = validate_main(expected, proofs, lean_binary(lean), timeout)
    if not accepted:
        raise Refusal("proof", log)
    if report["axiom_audit"] != log:
        raise Refusal("integrity", "reported native RoPE axiom audit differs from fresh check")
    return log
