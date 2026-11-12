"""Source-bound native FP16 AWQ departure with complete dense exact-real proofs."""

import json
from pathlib import Path
import tempfile

from . import mfma, native_awq_gemm, real_backend
from .certificate import digest, lean_binary, run_lean, write_json
from .ir import Refusal, lean_list

PROFILE = "native-awq-gemm-real-v24"
TARGET = "LarkReal.NativeAwqGemm"
BASE_FILES = {"Main.lean", "kernel.hip", "reference.py", "task.json", "translation.json"}
REPORT_FIELDS = {
    "schema", "status", "model_profile", "files", "model_hashes", "mathlib_commit",
    "source_readback", "whole_launch_proved", "actual_whole_trace_race_freedom_proved",
    "source_reference_equality_proved", "ieee_equivalence_proved", "floating_point_error_bound_proved",
    "m", "k", "n", "tile_n", "blocks", "input_elements", "output_elements", "instructions",
    "native_matrix_sites", "shared_half_cells", "axiom_audit", "model_calls",
    "original_paper_fully_reproduced", "trusted_assumptions", "scope",
}
SCOPE = (
    "Independent native wave64 FP16-weight, single-split-K AWQ departure. Positive M,K,N; "
    "K%32=0, N%64=0 and signed matrix-address bounds. Native block64/wave64, padded shared "
    "A16x40 and B32x(tileN+8), both K16 passes, original K loop, row guards, half conversions "
    "and original source-derived lane/warp/block/grid fuel. Complete initialized launch, "
    "actual-trace race freedom and every independent dense canonical-real matrix-product output. "
    "No IEEE equality/error bound, int4 dequantization, general split-K or original-paper result."
)
ASSUMPTIONS = [
    "Lean 4.19.0 and the printed standard axioms",
    "Pinned nonlinear/native MFMA machines and opcode-to-hardware correspondence",
    "Pinned Mathlib sources, dependencies and compiled import cache",
    "Typed FP16 HIP reader/lowering and the closed Torch matrix-product AST interpretation",
    "Aligned disjoint contiguous FP16 A[M,K], B[K,N] and output[M,N] buffers",
    "Native full wave64 f32_16x16x16f16 MFMA with modifiers(0,0,0) and old-register operand snapshot",
    "Exact-real arithmetic with identity storage conversions; no IEEE equality or error theorem",
    "Race-free phase reduction to hardware interleavings remains external metatheory",
]


def libraries():
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
                pending.update(name for name in line.split()[1:] if name.startswith(("Lark.", "LarkReal.")))
    return dict(sorted(result.items()))


def prepare(source, reference, task_source):
    task = native_awq_gemm.parse_task(task_source)
    native_awq_gemm.check_reference(reference)
    return task, native_awq_gemm.translate(source, task)


def render(task, tr):
    p = native_awq_gemm.shape_of(task)
    return f'''import LarkReal.NativeAwqGemm
namespace LarkCertificate
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option autoImplicit false
attribute [local irreducible] LarkNativeAwqGemm.wholeGrid LarkNativeAwqGemm.gridFold LarkNativeAwqGemm.wholeBlock LarkNativeAwqGemm.kLoopState LarkNativeAwqGemm.kAccum
def shape : LarkNativeAwqGemm.Shape := ⟨{p.m},{p.k},{p.n},by decide,by decide,by decide,by decide,by decide,by decide,by decide,by decide⟩
def layout : Layout := ⟨{lean_list(f"⟨.{b.role}, {b.size}⟩" for b in task.buffers)},
  {lean_list(str(size) for _, size in tr.shared)},[]⟩
def geometry : Geometry := ⟨{task.grid},64,64⟩
def fuel : Fuel := ⟨{','.join(map(str,task.fuel))}⟩
def program : List LarkMFMA.Instr := {lean_list(mfma.emit(i) for i in tr.program)}
-- The closed reference AST is interpreted as a dense real matrix product.
-- Half/float conversions are identities in this exact-real interpretation.
noncomputable def reference (input : Nat → Nat → ℝ) (row col : Nat) : ℝ :=
  ((List.range {p.k}).map fun j => input 0 (row*{p.k}+j)*input 1 (j*{p.n}+col)).sum
noncomputable def spec (input : Nat → Nat → ℝ) : List ℝ :=
  (List.range {p.m*p.n}).map fun i => reference input (i/{p.n}) (i%{p.n})
theorem reference_data : spec=LarkReal.NativeAwqGemm.denseSpec shape := by rfl
theorem layout_data : layout=LarkNativeAwqGemm.layout shape := by rfl
theorem geometry_data : geometry=LarkNativeAwqGemm.geometry shape := by rfl
theorem fuel_data : fuel=LarkNativeAwqGemm.fuel shape := by rfl
theorem program_data : program=LarkNativeAwqGemm.program shape := by decide
theorem segmentation_data : program=LarkNativeAwqGemm.program shape := program_data
noncomputable def finalState (input : Nat → Nat → ℝ) (outside : Location → Option ℝ) : State ℝ :=
  LarkNativeAwqGemm.wholeGrid shape LarkReal.ops input (initial (LarkNativeAwqGemm.layout shape) input outside)
theorem segmentation (input : Nat → Nat → ℝ) (outside : Location → Option ℝ) :
    LarkMFMA.runLaunch LarkReal.ops layout geometry fuel program (initial layout input outside)=some (finalState input outside) := by
  rw [layout_data,geometry_data,fuel_data,program_data]
  exact LarkNativeAwqGemm.whole_launch_run shape LarkReal.ops input outside
theorem race_free (input : Nat → Nat → ℝ) (outside : Location → Option ℝ) :
    raceFree geometry (finalState input outside).trace=true := by
  rw [geometry_data]
  exact LarkNativeAwqGemm.initialized_whole_grid_race_free shape LarkReal.ops input outside
theorem segment_equivalence (input : Nat → Nat → ℝ) (outside : Location → Option ℝ) :
    extract layout (finalState input outside)=some (spec input) := by
  have equality : LarkNativeAwqGemm.sourceSpec shape LarkReal.ops input=spec input :=
    (congrFun (LarkReal.NativeAwqGemm.source_spec_real shape) input).trans (congrFun reference_data input).symm
  rw [layout_data]
  exact (LarkNativeAwqGemm.whole_grid_extract shape LarkReal.ops input _).trans (congrArg some equality)
theorem kernel_eq_spec : LarkMFMA.Correct LarkReal.ops layout geometry fuel program spec := by
  intro input outside
  exact ⟨finalState input outside,segmentation input outside,race_free input outside,segment_equivalence input outside⟩
theorem kernel_eq_spec_pre (input : Nat → Nat → ℝ) (s : State ℝ) (pre : StdPre layout input s) :
    ∃ final, LarkMFMA.runLaunch LarkReal.ops layout geometry fuel program s=some final ∧
      raceFree geometry final.trace=true ∧ extract layout final=some (spec input) := by
  obtain ⟨outside,rfl⟩ := pre
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
'''


def validate_main(main, proof_sources, lean, timeout):
    _, task_env = real_backend.prepare(proof_sources, lean, timeout, target=TARGET)
    with tempfile.TemporaryDirectory(prefix="lark-native-awq-gemm-check-") as temporary:
        directory = Path(temporary)
        (directory / "Main.lean").write_bytes(main)
        (directory / "lean-toolchain").write_bytes(real_backend.configuration()["lean-toolchain"])
        return run_lean(directory, lean, timeout, env=task_env)


def dimensions(task, tr):
    p = native_awq_gemm.shape_of(task)
    return {"m": p.m, "k": p.k, "n": p.n, "tile_n": p.tile_n, "blocks": p.grid,
            "input_elements": p.m*p.k+p.k*p.n, "output_elements": p.m*p.n,
            "instructions": len(tr.program),
            "native_matrix_sites": sum(i.op == "mfma" for i in tr.program),
            "shared_half_cells": sum(size for _, size in tr.shared)}


def verify(kernel, reference, task_path, output, *, lean=None, timeout=600):
    if output.exists() or timeout <= 0:
        raise Refusal("configuration", "fresh output and positive timeout required")
    sources = {"kernel.hip": kernel.read_bytes(), "reference.py": reference.read_bytes(), "task.json": task_path.read_bytes()}
    task, tr = prepare(*(sources[n].decode() for n in ("kernel.hip", "reference.py", "task.json")))
    proof_sources = libraries()
    files = {**sources, **proof_sources, **real_backend.configuration(), "Main.lean": render(task, tr).encode(),
             "translation.json": (json.dumps(tr.data(), indent=2)+"\n").encode()}
    output.mkdir(parents=True)
    for name, content in files.items():
        path = output/name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(content)
    accepted, log = validate_main(files["Main.lean"], proof_sources, lean_binary(lean), timeout)
    (output/"lean-1.log").write_text(log)
    report = {"schema": 1, "status": "verified" if accepted else "unproved", "model_profile": PROFILE,
              "files": {name: digest(content) for name, content in sorted(files.items())},
              "model_hashes": {name: digest(content) for name, content in proof_sources.items()},
              "mathlib_commit": real_backend.MATHLIB, "source_readback": True,
              "whole_launch_proved": accepted, "actual_whole_trace_race_freedom_proved": accepted,
              "source_reference_equality_proved": accepted, "ieee_equivalence_proved": False,
              "floating_point_error_bound_proved": False, **dimensions(task, tr), "axiom_audit": log,
              "model_calls": 0, "original_paper_fully_reproduced": False,
              "trusted_assumptions": ASSUMPTIONS, "scope": SCOPE}
    write_json(output/"report.json", report)
    return report


def check(directory, *, lean=None, timeout=600):
    report = json.loads((directory/"report.json").read_text())
    if (type(report) is not dict or set(report) != REPORT_FIELDS or type(report.get("files")) is not dict
            or type(report.get("model_hashes")) is not dict or type(report.get("axiom_audit")) is not str):
        raise Refusal("integrity", "unexpected native AWQ report schema/types")
    proof_sources, configuration = libraries(), real_backend.configuration()
    if report.get("model_profile") != PROFILE or set(report["files"]) != BASE_FILES|set(proof_sources)|set(configuration):
        raise Refusal("integrity", "unexpected native AWQ profile/files")
    for name, h in report["files"].items():
        path = directory/name
        if path.is_symlink() or digest(path.read_bytes()) != h:
            raise Refusal("integrity", "certificate file differs: "+name)
    for name, content in {**proof_sources, **configuration}.items():
        if (directory/name).read_bytes() != content:
            raise Refusal("integrity", "pinned proof source/configuration differs: "+name)
    if report["model_hashes"] != {name: digest(content) for name, content in proof_sources.items()} or report["mathlib_commit"] != real_backend.MATHLIB:
        raise Refusal("integrity", "different pinned proof libraries/Mathlib")
    task, tr = prepare(*((directory/name).read_text() for name in ("kernel.hip", "reference.py", "task.json")))
    if json.loads((directory/"translation.json").read_text()) != json.loads(json.dumps(tr.data())):
        raise Refusal("integrity", "translation differs from exact source")
    expected = render(task, tr).encode()
    if (directory/"Main.lean").read_bytes() != expected:
        raise Refusal("integrity", "theorem differs from fixed source/reference statement")
    if any(type(report.get(name)) is not int or report[name] != value for name, value in dimensions(task, tr).items()):
        raise Refusal("integrity", "reported dimensions/instructions differ")
    if (type(report.get("schema")) is not int or report["schema"] != 1 or report.get("status") != "verified"
            or any(report.get(name) is not True for name in ("source_readback", "whole_launch_proved",
                       "actual_whole_trace_race_freedom_proved", "source_reference_equality_proved"))
            or any(report.get(name) is not False for name in ("ieee_equivalence_proved", "floating_point_error_bound_proved", "original_paper_fully_reproduced"))
            or type(report.get("model_calls")) is not int or report["model_calls"] != 0
            or report.get("scope") != SCOPE or report.get("trusted_assumptions") != ASSUMPTIONS):
        raise Refusal("integrity", "reported proof scope differs from this independent native AWQ profile")
    accepted, log = validate_main(expected, proof_sources, lean_binary(lean), timeout)
    if not accepted:
        raise Refusal("proof", log)
    return log
