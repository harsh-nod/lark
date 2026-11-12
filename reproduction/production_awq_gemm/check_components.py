"""Check full AWQ source identity and address components, not execution."""

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tarfile
import time

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from lark_kernels import mfma, native_awq_gemm as native  # noqa: E402
from lark_kernels.ir import lean_list  # noqa: E402

HERE = Path(__file__).resolve().parent
CASES = ("m17_k32_n64", "m17_k32_n128", "m33_k64_n192", "m33_k64_n256")
MODELS = ("Nonlinear", "MFMA", "NativeAwqGemmAddress", "NativeAwqGemmGlobal", "NativeAwqGemmProgram",
          "NativeAwqGemmGeometry", "NativeAwqGemmState", "NativeAwqGemmPrefix")


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n")


def render(task, tr):
    p = native.shape_of(task)
    return f'''import Lark.NativeAwqGemmPrefix
namespace AwqSource
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option autoImplicit false
def shape : LarkNativeAwqGemm.Shape := ⟨{p.m},{p.k},{p.n},by decide,by decide,by decide,by decide,by decide,by decide,by decide,by decide⟩
def sourceProgram : List LarkMFMA.Instr := {lean_list(mfma.emit(i) for i in tr.program)}
def sourceLayout : Layout := ⟨[⟨.input,{p.m*p.k}⟩,⟨.input,{p.k*p.n}⟩,⟨.output,{p.m*p.n}⟩],{lean_list(str(size) for _,size in tr.shared)},[]⟩
def sourceGeometry : Geometry := ⟨{task.grid},64,64⟩
def sourceFuel : Fuel := ⟨{','.join(map(str,task.fuel))}⟩
theorem source_binding : sourceProgram=LarkNativeAwqGemm.program shape := by decide
theorem layout_binding : sourceLayout=LarkNativeAwqGemm.layout shape := by rfl
theorem geometry_binding : sourceGeometry=LarkNativeAwqGemm.geometry shape := by rfl
theorem fuel_binding : sourceFuel=LarkNativeAwqGemm.fuel shape := by rfl
theorem first_barrier : sourceProgram[LarkNativeAwqGemm.firstBarrier shape]?=some (.scalar (.barrier .block)) := by decide
theorem middle_barrier : sourceProgram[LarkNativeAwqGemm.middleBarrier shape]?=some (.scalar (.barrier .block)) := by decide
theorem halt_site : sourceProgram[LarkNativeAwqGemm.haltPC shape]?=some (.scalar .halt) := by decide
theorem matrix_sites : (sourceProgram.filter (fun inst => match inst with | .mfma .. => true | _ => false)).length={p.tile_n//8} := by decide
theorem source_length : sourceProgram.length={50+22*(p.tile_n//16)} := by decide
#print axioms source_binding
#print axioms layout_binding
#print axioms geometry_binding
#print axioms fuel_binding
#print axioms first_barrier
#print axioms middle_barrier
#print axioms halt_site
#print axioms matrix_sites
#print axioms source_length
end AwqSource
'''


def audits(log):
    entries = re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", log)
    result = dict(entries)
    assert len(entries) == len(result)
    assert all(set(a.strip() for a in ax.split(",") if a.strip()) <=
               {"propext", "Classical.choice", "Quot.sound"} for ax in result.values())
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--lean-bin", type=Path, required=True)
    args = parser.parse_args()
    out, lean_bin = args.output.resolve(), args.lean_bin.resolve()
    assert not any((p/".git").exists() for p in (out, *out.parents))
    assert all((lean_bin/name).is_file() for name in ("lean", "lake"))
    assert shutil.which("git", path=str(lean_bin)) is None
    out.mkdir(parents=True, exist_ok=False)
    project = out/"project"
    (project/"Lark").mkdir(parents=True)
    for model in MODELS:
        shutil.copyfile(ROOT/f"lean/Lark/{model}.lean", project/f"Lark/{model}.lean")
    (project/"lean-toolchain").write_text("leanprover/lean4:v4.19.0\n")
    (project/"lakefile.toml").write_text('name = "lark_awq_components"\nversion = "0.1.0"\n[[lean_lib]]\nname = "Lark"\n')
    assert not (project/".lake").exists()
    env = dict(os.environ)
    env["PATH"] = str(lean_bin)
    env.pop("LEAN_PATH", None)
    checks = []

    def run(name, command, expected):
        before = time.monotonic()
        result = subprocess.run(command, cwd=project, env=env, capture_output=True, text=True, timeout=180)
        log = result.stdout+result.stderr
        (out/(name+".log")).write_text(log)
        accepted = result.returncode == 0 and "error:" not in log and "sorryAx" not in log
        assert accepted is expected, name+"\n"+log
        if not expected:
            assert "is false" in log and "source_binding" in log
            assert not any(s in log for s in ("maximum recursion", "maximum number of heartbeats", "Stack overflow"))
        checks.append({"name": name, "accepted": accepted, "expected_accepted": expected,
                       "exit_code": result.returncode, "seconds": time.monotonic()-before, "timed_out": False})
        return log

    library = audits(run("fresh-library-build", [str(lean_bin/"lake"), "build", "Lark.NativeAwqGemmPrefix"], True))
    assert len(library) == 54
    source_audits = {}
    for name in CASES:
        case = HERE/"cases"/name
        task = native.parse_task((case/"task.json").read_text())
        native.check_reference((case/"reference.py").read_text())
        tr = native.translate((case/"kernel.hip").read_text(), task)
        (project/(name+".lean")).write_text(render(task, tr))
        source_audits[name] = audits(run(name, [str(lean_bin/"lake"), "env", "lean", name+".lean"], True))
        assert len(source_audits[name]) == 9
    case = HERE/"cases/m33_k64_n192"
    source = (case/"kernel.hip").read_text()
    task = native.parse_task((case/"task.json").read_text())
    mutations = {
        "wrong-matrix-operand": source.replace("(left0, right0_0, acc0,", "(left0, left0, acc0,", 1),
        "missing-first-barrier": source.replace("    __syncthreads();\n", "", 1),
        "missing-middle-barrier": "".join(source.rsplit("    __syncthreads();\n", 1)),
        "wrong-shared-a-stride": source.replace("* 40 + inputCol", "* 32 + inputCol", 1),
        "wrong-shared-b-stride": source.replace("tileB[bRow * 72", "tileB[bRow * 64", 1),
        "aliased-output-column": source.replace("+ 0 + lane % 16] = __float2half(acc0[0]);",
                                                "+ 0 + lane % 8] = __float2half(acc0[0]);", 1),
    }
    for name, changed in mutations.items():
        assert changed != source
        tr = native.translate(changed, task)
        (project/(name+".hip")).write_text(changed)
        (project/(name+".lean")).write_text(render(task, tr))
        run(name, [str(lean_bin/"lake"), "env", "lean", name+".lean"], False)
    hashes = {str(p.relative_to(project)): sha(p) for p in sorted(project.rglob("*"))
              if p.is_file() and ".lake" not in p.parts}
    write(out/"source-sha256.json", hashes)
    with tarfile.open(out/"source-project.tar.gz", "w:gz") as archive:
        for name in sorted(hashes):
            archive.add(project/name, arcname=name, recursive=False)
    result = {"schema": 1, "status": "native-awq-complete-source-identity-and-address-components-checked",
              "checked_at_utc": datetime.now(timezone.utc).isoformat(), "owned_lean_modules": len(MODELS),
              "library_axiom_audits": library, "source_axiom_audits": source_audits,
              "axiom_audit_occurrences": len(library)+sum(map(len,source_audits.values())),
              "source_instances": len(CASES), "false_source_identity_claims_rejected": len(mutations),
              "full_source_binding_proved": True, "shared_and_global_bounds_proved": True,
              "shared_ownership_and_matrix_fragment_coordinates_proved": True,
              "universal_launch_and_scalar_parameter_bounds_proved": True,
              "actual_initial_lane_and_block_decode_execution_proved": True,
              "initial_scalar_instructions_executed": 6,
              "whole_kernel_execution_proved": False, "actual_whole_trace_race_freedom_proved": False,
              "source_reference_equality_proved": False, "source_certificates": 0,
              "git_available_on_proof_path": False, "owned_compiled_cache_seeded": False,
              "ieee_equivalence_proved": False, "original_paper_fully_reproduced": False,
              "model_calls": 0, "gpu_trials": 0, "checks": checks}
    shutil.copyfile(Path(__file__), out/"checker.py")
    write(out/"results.json", result)
    write(out/"manifest.json", {p.name: sha(p) for p in sorted(out.iterdir()) if p.is_file()})
    print(json.dumps({k:result[k] for k in ("status", "source_instances", "axiom_audit_occurrences", "false_source_identity_claims_rejected")}))


if __name__ == "__main__":
    main()
