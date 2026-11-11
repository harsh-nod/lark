"""Reject fully rehashed attempts to promote exp-prefix evidence to stronger claims."""

import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--packet", type=Path, required=True)
    parser.add_argument("--earlier-packet", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--lean-bin", type=Path, required=True)
    args = parser.parse_args()
    out = args.output.resolve()
    if any((p / ".git").exists() for p in (out, *out.parents)):
        raise ValueError("Choose fresh output outside Git")
    out.mkdir(parents=True, exist_ok=False)
    block = json.loads((args.packet / "results.json").read_text())
    scenarios = [
        ("invented-certificate", args.packet, {"source_certificates": 1}, "Invented source certificate"),
        ("boolean-certificate", args.packet, {"source_certificates": False}, "Invented source certificate"),
        ("invented-whole-launch", args.packet, {"whole_kernel_execution_proved": True}, "Invented whole-source/reference claim"),
        ("invented-reference-bridge", args.packet, {"canonical_source_equivalence_proved": True}, "Invented whole-source/reference claim"),
        ("omitted-exp-run-audit", args.packet, {}, "Principal exp-prefix audits absent"),
        ("earlier-maximum-relabeled", args.earlier_packet, {}, "Principal exp-prefix audits absent"),
        ("invented-block-trace-count", args.packet, {"accesses_per_maximum_pass": 57376}, "Wrong maximum-pass endpoint/accesses/partials/fuel/checksum"),
        ("changed-block-fuel", args.packet, {"original_fuel": {"lane":4096,"warp":8,"block":6,"grid":1}}, "Wrong maximum-pass endpoint/accesses/partials/fuel/checksum"),
        ("omitted-partial-writer", args.packet, {"shared_writes_per_maximum_pass":32}, "Wrong maximum-pass endpoint/accesses/partials/fuel/checksum"),
        ("wrong-row-maximum-checksum", args.packet, {"checksum_row_maximum": 0}, "Wrong maximum-pass endpoint/accesses/partials/fuel/checksum"),
        ("wrong-second-barrier-epoch", args.packet, {"maximum_block_epoch":1}, "Wrong maximum-pass endpoint/accesses/partials/fuel/checksum"),
        ("invented-remaining-fuel", args.packet, {"remaining_block_fuel_after_maximum":4}, "Wrong maximum-pass endpoint/accesses/partials/fuel/checksum"),
        ("missing-second-barrier", args.packet, {"second_barrier_resume_proved":False}, "Missing maximum-pass claims"),
        ("invented-row-bound", args.packet, {"rows":{"min":1,"max":42731}}, "Wrong maximum-pass endpoint/accesses/partials/fuel/checksum"),
        ("invented-exp-wave", args.packet, {"actual_exp_wave_fold_execution_proved":True}, "Invented exp collective/block execution"),
        ("invented-exp-block", args.packet, {"actual_exp_block_phase_execution_proved":True}, "Invented exp collective/block execution"),
        ("wrong-exp-endpoint", args.packet, {"exp_parked_pc":69}, "Wrong exp-prefix endpoint/counts/word model"),
        ("wrong-exp-epoch", args.packet, {"exp_block_epoch":3}, "Wrong exp-prefix endpoint/counts/word model"),
        ("wrong-exp-boundary-cost", args.packet, {"exp_lane_costs":{"tid0_to80":978,"tid81_to1023":982}}, "Wrong exp-prefix endpoint/counts/word model"),
        ("wrong-exp-trace-count", args.packet, {"exp_lane_access_increments":{"tid0_to80":211,"tid81_to1023":213}}, "Wrong exp-prefix endpoint/counts/word model"),
        ("wrong-exp-word-value", args.packet, {}, "Wrong exp-prefix endpoint/counts/word model"),
        ("omitted-exp-output-audit", args.packet, {}, "Principal exp-prefix audits absent"),
        ("omitted-exp-sum-claim", args.packet, {"exp_unrounded_source_ordered_sum_proved":False}, "Missing exp-prefix claims"),
        ("omitted-refusal-check", args.packet, {}, "Wrong exp-prefix replay checks"),
    ]
    records = []
    for name, original, changes, reason in scenarios:
        folder = out / name
        packet = folder / "packet"
        packet.mkdir(parents=True)
        manifest = json.loads((original / "manifest.json").read_text())
        for filename, digest in manifest.items():
            if Path(filename).name != filename or sha(original / filename) != digest:
                raise ValueError("Original packet path/hash differs")
            shutil.copyfile(original / filename, packet / filename)
        report = json.loads((packet / "results.json").read_text())
        report.update(changes)
        if name == "omitted-exp-run-audit":
            del report["axiom_audits"]["source_exp_initial_run"]
        if name == "omitted-exp-output-audit":
            del report["axiom_audits"]["source_exp_output_run"]
        if name == "wrong-exp-word-value":
            report["exp_word_cases"]["0"]["sum"] += 1
        if name == "omitted-refusal-check":
            report["checks"].pop()
        if name == "earlier-maximum-relabeled":
            for key in ("status", "stage", "source_certificates", "maximum_parked_pc", "maximum_resumed_pc", "maximum_block_epoch",
                        "physical_waves_per_block", "threads_per_block", "logical_partials_per_block",
                        "accesses_per_maximum_pass", "input_reads_per_maximum_pass", "shared_writes_per_maximum_pass",
                        "shared_reads_per_maximum_pass", "checksum_row_maximum",
                        "remaining_block_fuel_after_maximum", "checksum_final_partial", "checksum_max_operation", "original_fuel",
                        "actual_first_block_wave_fold_execution_proved", "starts_at_actual_initializer",
                        "all32_source_ordered_partial_values_proved", "earlier_waves_preserved_proved",
                        "first_barrier_resume_proved", "block_scheduler_decomposition_proved", "maximum_global_memory_frame_proved",
                        "checksum_final_partial_actual_fold_value_proved", "first_block_race_freedom_proved",
                        "actual_serial_block_wave_fold_execution_proved", "all32_serial_partial_reads_proved",
                        "second_barrier_resume_proved", "maximum_pass_race_freedom_proved",
                        "checksum_row_maximum_actual_fold_value_proved",
                        "race_freedom_assumed", "whole_kernel_execution_proved", "conflict_witness_state_reachability_proved",
                        "actual_trace_universal_classification_proved", "canonical_source_equivalence_proved",
                        "ieee_equivalence_proved", "original_paper_fully_reproduced",
                        "actual_exp_scalar_lane_prefix_execution_proved", "exp_starts_at_proved_maximum_state",
                        "exp_parked_pc", "exp_block_epoch", "exp_outer_rounds", "exp_components_per_round",
                        "exp_lane_costs", "exp_lane_access_increments", "exp_valid_stores_per_lane",
                        "exp_converted_outputs_proved", "exp_unrounded_source_ordered_sum_proved",
                        "exp_prefix_race_freedom_proved", "exp_native_indices_preserved_proved",
                        "exp_word_model", "exp_word_maximum", "exp_word_cases", "exp_word_actual_sum_and_output_values_proved",
                        "actual_exp_wave_fold_execution_proved", "actual_exp_block_phase_execution_proved"):
                report[key] = block[key]
        (packet / "results.json").write_text(json.dumps(report, indent=2) + "\n")
        (packet / "manifest.json").write_text(json.dumps({p.name: sha(p) for p in sorted(packet.iterdir())
                                                          if p.name != "manifest.json"}, indent=2) + "\n")
        target = folder / "attempted-replay"
        command = [sys.executable, str(HERE / "replay_exp_prefix.py"), "--packet", str(packet),
                   "--finite-trace-packet", str(HERE / "results/finite-trace-v2"), "--output", str(target),
                   "--lean-bin", str(args.lean_bin)]
        run = subprocess.run(command, capture_output=True, text=True, timeout=30)
        log = run.stdout + run.stderr
        (out / (name + ".log")).write_text(log)
        if run.returncode == 0 or reason not in log or target.exists():
            raise ValueError("Wrong stage rejection: " + name + "\n" + log)
        records.append({"name": name, "exit_code": run.returncode, "expected_reason": reason,
                        "packet_rehashed": True, "rejected_before_extraction": True})
    report = {
        "schema": 1, "status": "twenty-four-rehashed-false-exp-prefix-stage-claims-rejected-before-extraction",
        "checks": records, "exp_prefix_packet_manifest_sha256": sha(args.packet / "manifest.json"),
        "earlier_packet_manifest_sha256": sha(args.earlier_packet / "manifest.json"),
        "replayer_sha256": sha(HERE / "replay_exp_prefix.py"), "source_certificates": 0,
        "whole_kernel_execution_proved": False, "original_paper_fully_reproduced": False,
    }
    (out / "results.json").write_text(json.dumps(report, indent=2) + "\n")
    shutil.copyfile(Path(__file__), out / "checker.py")
    (out / "manifest.json").write_text(json.dumps({p.name: sha(p) for p in sorted(out.iterdir()) if p.is_file()}, indent=2) + "\n")
    print(json.dumps({"status": report["status"], "checks": len(records)}))


if __name__ == "__main__":
    main()
