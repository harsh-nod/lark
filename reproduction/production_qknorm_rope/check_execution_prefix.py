"""Rebuild partial native Q/K execution proofs and bind both source layouts.

This development check produces no complete-kernel certificate. The split-half
wave theorem reaches PC59; the interleaved theorem composes scalar
normalization with an arbitrary continuation. Rotary suffixes remain open.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tarfile

import check_program as components

ROOT, HERE = components.ROOT, components.HERE
TARGET = "Lark.NativeQKNormRopeNormalWave"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def source_statement(text, contract):
    body = components.statement(text, contract).replace("import " + components.TARGET, "import " + TARGET)
    body += '''
theorem source_reduction_continuation (ops : Ops α) (input : Nat → Nat → α)
    (block warp : Nat) (s : State α) (hb : block < sourceShape.rows * 5) (hw : warp < 4)
    (hp : ∀ t ∈ cohortThreads block warp 64, s.pc t = 0) (hr : Reads sourceShape input s) :
    LarkPartitionCollective.runWarp ops (layout sourceShape) (geometry sourceShape) fuel sourceProgram
      (warpThreads (geometry sourceShape) block warp) fuel.warp s =
    LarkPartitionCollective.runWarp ops (layout sourceShape) (geometry sourceShape) fuel sourceProgram
      (cohortThreads block warp 64) 11 (fifthSnapshot sourceShape ops input block warp s) := by
  simpa only [source_binding.1] using native_fifth_snapshot sourceShape sourceNeox ops input block warp s hb hw hp hr
theorem source_scalar_normalization (ops : Ops α) (input : Nat → Nat → α)
    (t extra : Nat) (a b : α) (s : State α) (hp : s.pc t = 33)
    (ha : s.regs t 4 = some a) (hb : s.regs t 9 = some b)
    (hv : InputValues ops input t s) (hi : NativeIndices t s) (hr : Reads sourceShape input s) :
    LarkCollective.runLane ops (layout sourceShape) (geometry sourceShape) sourceProgram t (extra + (weightSteps t + 16)) s =
      LarkCollective.runLane ops (layout sourceShape) (geometry sourceShape) sourceProgram t extra (normalLane ops input t a b s) := by
  simpa only [source_binding.1] using normal_lane_eq sourceShape sourceNeox ops input t extra a b s hp ha hb hv hi hr
#print axioms source_reduction_continuation
#print axioms source_scalar_normalization
'''
    if contract.rotary_layout == "split-half":
        body += '''
theorem source_normalization_wave (ops : Ops α) (input : Nat → Nat → α)
    (block warp : Nat) (s : State α) (hb : block < sourceShape.rows * 5) (hw : warp < 4)
    (hp : ∀ t ∈ cohortThreads block warp 64, s.pc t = 0) (hr : Reads sourceShape input s) :
    LarkPartitionCollective.runWarp ops (layout sourceShape) (geometry sourceShape) fuel sourceProgram
      (warpThreads (geometry sourceShape) block warp) fuel.warp s =
    continueCohort sourceShape true ops (cohortThreads block warp 64) 10 (normalWaveState sourceShape ops input block warp s) := by
  simpa only [source_binding.1, sourceNeox] using native_normalization_step sourceShape ops input block warp s hb hw hp hr
theorem source_normalization_wave_value (ops : Ops α) (input : Nat → Nat → α)
    (block warp lane e : Nat) (s : State α) (hl : lane < 64) (he : e < 4) :
    let t := cohortBase block warp + lane
    (normalWaveState sourceShape ops input block warp s).regs t (18 + 2 * e) =
      some (normalizedValue ops input t (weightBuffer t) (normalScale ops (waveValues ops input block warp 5 lane)) e) :=
  normal_wave_value sourceShape ops input block warp lane e s hl he
theorem source_normalization_wave_trace (ops : Ops α) (input : Nat → Nat → α)
    (block warp : Nat) (s : State α) :
    (normalWaveState sourceShape ops input block warp s).trace.length = s.trace.length + 512 :=
  normal_wave_trace_length sourceShape ops input block warp s
theorem source_normalization_prefix_race_free (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (block warp : Nat) :
    raceFree (geometry sourceShape)
      (normalWaveState sourceShape ops input block warp (initial (layout sourceShape) input outside)).trace = true :=
  normal_wave_initial_race_free sourceShape ops input outside block warp
#print axioms source_normalization_wave
#print axioms source_normalization_wave_value
#print axioms source_normalization_wave_trace
#print axioms source_normalization_prefix_race_free
'''
    return body


def run_stage(args, *, target=TARGET, statement_factory=source_statement,
              additional_claims=None, required_principals=(), control_factory=None):
    out, lean_bin = args.output.resolve(), args.lean_bin.resolve()
    if out.is_relative_to(ROOT):
        raise ValueError("Fresh output outside the repository required")
    out.mkdir(parents=True, exist_ok=False)
    lake = str(lean_bin / "lake")
    env = dict(os.environ)
    env.pop("LEAN_PATH", None)
    if "Lean version 4.19.0" not in subprocess.check_output([lake, "--version"], text=True, env=env):
        raise ValueError("Pinned Lean4.19.0 required")
    own = {}
    components.modules(target, own)
    source = out / "source"
    files = ["lean/" + name.replace(".", "/") + ".lean" for name in own]
    files += ["lean/lean-toolchain", "lean/lakefile.toml", "LICENSE", "pyproject.toml"]
    files += [str(path.relative_to(ROOT)) for path in (ROOT / "lark_kernels").glob("*.py")]
    files += [str(path.relative_to(ROOT)) for path in HERE.glob("*.py")]
    files += [str(path.relative_to(ROOT)) for folder in ("cases", "upstream") for path in (HERE / folder).rglob("*") if path.is_file()]
    files += [str((HERE / "provenance.json").relative_to(ROOT))]
    hashes = {}
    for filename in sorted(set(files)):
        dest = source / filename
        dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(ROOT / filename, dest)
        hashes[filename] = sha(dest)
    (out / "source-manifest.json").write_text(json.dumps(hashes, indent=2) + "\n")
    with tarfile.open(out / "source.tar.gz", "w:gz") as archive:
        for filename in hashes:
            archive.add(source / filename, arcname=filename, recursive=False)
    audits, checks = {}, []

    def check(name, command, expected_count, accepted=True):
        run = subprocess.run(command, cwd=source / "lean", env=env, capture_output=True, text=True, timeout=600)
        log = run.stdout + run.stderr
        (out / (name + ".log")).write_text(log)
        entries = re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", log)
        values = {key: [a.strip() for a in value.split(",") if a.strip()] for key, value in entries}
        if (run.returncode == 0) is not accepted:
            raise ValueError("Execution-prefix check failed: " + name + ": " + log[-12000:])
        if accepted:
            if (len(entries) != len(values) or len(values) != expected_count
                    or any(not set(value) <= ALLOWED_AXIOMS for value in values.values())):
                raise ValueError("Execution-prefix axiom closure differs: " + name)
            audits[name] = values
        elif "is false" not in log or re.search(r"maximum recursion|heartbeats|stack overflow|timed out|out of memory", log, re.I):
            raise ValueError("Source mutation did not fail logically: " + name)
        checks.append({"name": name, "exit_code": run.returncode, "axiom_audits": len(values) if accepted else 0})

    count = sum(len(re.findall(r"^#print axioms ", contents, re.M)) for contents in own.values())
    check("fresh-build", [lake, "build", target], count)
    principals = {"LarkNativeQKNormRope.native_fifth_snapshot", "LarkNativeQKNormRope.normal_lane_eq",
                  "LarkNativeQKNormRope.native_normalization_step", "LarkNativeQKNormRope.normal_wave_value",
                  "LarkNativeQKNormRope.normal_wave_initial_race_free"}
    if not (principals | set(required_principals)) <= audits["fresh-build"].keys():
        raise ValueError("Missing execution principals")
    contracts = {}
    for layout in components.native.LAYOUTS:
        case = HERE / "cases" / layout
        text = (case / "kernel.hip").read_text()
        components.native.check_reference((case / "reference.py").read_text(), layout)
        for rows in (1, 3, 256, 65535):
            raw = json.loads((case / "task.json").read_text())
            raw["launch"]["grid"] = rows * 5
            for buffer in raw["buffers"]:
                if len(buffer["shape"]) > 1:
                    buffer["shape"][0] = rows
            contract = components.native.parse_task(json.dumps(raw))
            name = layout.replace("-", "_") + "_" + str(rows)
            statement = statement_factory(text, contract)
            (source / "lean" / (name + ".lean")).write_text(statement)
            check(name, [lake, "env", "lean", name + ".lean"], len(re.findall(r"^#print axioms ", statement, re.M)))
            if rows == 1:
                contracts[layout] = text, contract
    controls = control_factory(contracts) if control_factory else {}
    for name, statement in controls.items():
        filename = "control_" + name.replace("-", "_") + ".lean"
        (source / "lean" / filename).write_text(statement)
        check(name, [lake, "env", "lean", filename], 0, accepted=False)
    report = {"schema": 1, "status": "partial-native-qknorm-rope-normalization-prefix-checked",
              "local_lean_modules": len(own), "library_axiom_audits": count, "source_instances": 8,
              "full_source_binding_proved": True, "five_reduction_snapshot_continuation_both_layouts": True,
              "scalar_normalization_continuation_both_layouts": True,
              "split_half_wave_normalization_to_pc59": True, "split_half_prefix_accesses_per_wave": 512,
              "whole_kernel_execution_proved": False, "complete_actual_trace_classification_proved": False,
              "source_reference_equality_proved": False, "source_certificates": 0,
              "original_paper_fully_reproduced": False, "model_calls": 0, "gpu_trials": 0,
              "axiom_audits": audits, "checks": checks, "source_archive_sha256": sha(out / "source.tar.gz"),
              "source_manifest_sha256": sha(out / "source-manifest.json")}
    if additional_claims:
        report.update(additional_claims)
    if controls:
        report["false_lean_claims_rejected"] = len(controls)
    (out / "results.json").write_text(json.dumps(report, indent=2) + "\n")
    (out / "manifest.json").write_text(json.dumps({p.name: sha(p) for p in sorted(out.iterdir()) if p.is_file()}, indent=2) + "\n")
    print(json.dumps({"status": report["status"], "modules": len(own), "library_audits": count,
                      "source_audits": sum(len(v) for k, v in audits.items() if k != "fresh-build")}))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--lean-bin", type=Path, required=True)
    run_stage(parser.parse_args())


if __name__ == "__main__":
    main()
