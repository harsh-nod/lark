"""Reject fully rehashed attempts to promote reduction-prefix evidence to stronger claims."""

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
        ("omitted-exp-run-audit", args.packet, {}, "Principal reduction-prefix audits absent"),
        ("earlier-reduction-relabeled", args.earlier_packet, {}, "Principal reduction-prefix audits absent"),
        ("invented-block-trace-count", args.packet, {"accesses_per_maximum_pass": 57376}, "Wrong maximum-pass endpoint/accesses/partials/fuel/checksum"),
        ("changed-block-fuel", args.packet, {"original_fuel": {"lane":4096,"warp":8,"block":6,"grid":1}}, "Wrong maximum-pass endpoint/accesses/partials/fuel/checksum"),
        ("omitted-partial-writer", args.packet, {"shared_writes_per_maximum_pass":32}, "Wrong maximum-pass endpoint/accesses/partials/fuel/checksum"),
        ("wrong-row-maximum-checksum", args.packet, {"checksum_row_maximum": 0}, "Wrong maximum-pass endpoint/accesses/partials/fuel/checksum"),
        ("wrong-second-barrier-epoch", args.packet, {"maximum_block_epoch":1}, "Wrong maximum-pass endpoint/accesses/partials/fuel/checksum"),
        ("invented-remaining-fuel", args.packet, {"remaining_block_fuel_after_maximum":4}, "Wrong maximum-pass endpoint/accesses/partials/fuel/checksum"),
        ("missing-second-barrier", args.packet, {"second_barrier_resume_proved":False}, "Missing maximum-pass claims"),
        ("invented-row-bound", args.packet, {"rows":{"min":1,"max":42731}}, "Wrong maximum-pass endpoint/accesses/partials/fuel/checksum"),
        ("omitted-reduction-prefix", args.packet, {"actual_exp_wave_fold_execution_proved":False}, "Missing reduction-prefix claims"),
        ("omitted-exp-block", args.packet, {"actual_exp_block_phase_execution_proved":False}, "Missing constructive reduction-prefix claims"),
        ("wrong-exp-endpoint", args.packet, {"exp_parked_pc":69}, "Wrong reduction-prefix endpoint/counts/word model"),
        ("wrong-exp-epoch", args.packet, {"exp_block_epoch":3}, "Wrong reduction-prefix endpoint/counts/word model"),
        ("wrong-exp-boundary-cost", args.packet, {"exp_lane_costs":{"tid0_to80":978,"tid81_to1023":982}}, "Wrong reduction-prefix endpoint/counts/word model"),
        ("wrong-exp-trace-count", args.packet, {"exp_lane_access_increments":{"tid0_to80":211,"tid81_to1023":213}}, "Wrong reduction-prefix endpoint/counts/word model"),
        ("wrong-exp-word-value", args.packet, {}, "Wrong reduction-prefix endpoint/counts/word model"),
        ("omitted-exp-output-audit", args.packet, {}, "Principal reduction-prefix audits absent"),
        ("omitted-exp-sum-claim", args.packet, {"exp_unrounded_source_ordered_sum_proved":False}, "Missing reduction-prefix claims"),
        ("omitted-refusal-check", args.packet, {}, "Wrong reduction-prefix replay checks"),
        ("omitted-third-barrier", args.packet, {"third_barrier_resume_proved":False}, "Missing constructive reduction-prefix claims"),
        ("omitted-serial-sum", args.packet, {"serial_sum_execution_proved":False}, "Missing constructive reduction-prefix claims"),
        ("wrong-reduction-prefix-endpoint", args.packet, {"exp_wave_parked_pc":83}, "Wrong reduction-prefix endpoint/partition/word values"),
        ("wrong-reduction-prefix-epoch", args.packet, {"exp_wave_block_epoch":3}, "Wrong reduction-prefix endpoint/partition/word values"),
        ("wrong-reduction-prefix-width", args.packet, {"exp_wave_logical_width":64}, "Wrong reduction-prefix endpoint/partition/word values"),
        ("wrong-reduction-prefix-kind", args.packet, {"exp_wave_shuffle_kind":"down"}, "Wrong reduction-prefix endpoint/partition/word values"),
        ("wrong-reduction-prefix-word", args.packet, {}, "Wrong reduction-prefix endpoint/partition/word values"),
        ("missing-reduction-prefix-sum-claim", args.packet, {"exp_wave_source_ordered_sum_proved":False}, "Missing reduction-prefix claims"),
        ("omitted-reduction-prefix-run-audit", args.packet, {}, "Principal reduction-prefix audits absent"),
        ("omitted-reduction-prefix-partial-audit", args.packet, {}, "Principal reduction-prefix audits absent"),
        ("omitted-fourth-barrier", args.packet, {"fourth_barrier_resume_proved":False}, "Missing constructive reduction-prefix claims"),
        ("omitted-reduction-Some", args.packet, {"actual_reduction_prefix_some_execution_proved":False}, "Missing constructive reduction-prefix claims"),
        ("integer-reduction-Some", args.packet, {"actual_reduction_prefix_some_execution_proved":1}, "Missing constructive reduction-prefix claims"),
        ("omitted-reduction-continuation", args.packet, {"reduction_prefix_linked_to_runBlock":False}, "Missing constructive reduction-prefix claims"),
        ("wrong-reduction-endpoint", args.packet, {"reduction_resumed_pc":94}, "Wrong reduction-prefix endpoint/counts/fuel"),
        ("wrong-reduction-epoch", args.packet, {"reduction_block_epoch":3}, "Wrong reduction-prefix endpoint/counts/fuel"),
        ("wrong-reduction-accesses", args.packet, {"accesses_after_fourth_barrier":273667}, "Wrong reduction-prefix endpoint/counts/fuel"),
        ("wrong-reduction-phase-count", args.packet, {"reduction_phases":3}, "Wrong reduction-prefix endpoint/counts/fuel"),
        ("wrong-reduction-remaining-fuel", args.packet, {"remaining_block_fuel_after_sum":2}, "Wrong reduction-prefix endpoint/counts/fuel"),
        ("boolean-reduction-remaining-fuel", args.packet, {"remaining_block_fuel_after_sum":True}, "Wrong reduction-prefix endpoint/counts/fuel"),
        ("wrong-serial-sum-reads", args.packet, {"shared_reads_per_serial_sum_phase":31}, "Wrong reduction-prefix endpoint/counts/fuel"),
        ("wrong-reduction-projection-total", args.packet, {}, "Wrong reduction-prefix diagnostic values/scope"),
        ("wrong-serial-checksum", args.packet, {"serial_checksum":0}, "Wrong reduction-prefix diagnostic values/scope"),
        ("wrong-serial-checksum-scope", args.packet, {"serial_checksum_scope":"full prefix"}, "Wrong reduction-prefix diagnostic values/scope"),
        ("omitted-reduction-output-audit", args.packet, {}, "Principal reduction-prefix audits absent"),
        ("omitted-reduction-run-audit", args.packet, {}, "Principal reduction-prefix audits absent"),
        ("omitted-serial-checksum-audit", args.packet, {}, "Principal reduction-prefix audits absent"),
        ("omitted-normalization", args.packet, {"normalization_execution_proved":False}, "Missing normalization execution"),
    ]
    scenarios += [
        ("omitted-whole-Some",args.packet,{"actual_whole_block_some_execution_proved":False},"Missing whole-block execution/value/race claims"),
        ("integer-whole-Some",args.packet,{"actual_whole_block_some_execution_proved":1},"Missing whole-block execution/value/race claims"),
        ("omitted-fifth-phase",args.packet,{"all_five_source_block_phases_proved":False},"Missing whole-block execution/value/race claims"),
        ("omitted-normalized-outputs",args.packet,{"whole_block_source_ordered_outputs_proved":False},"Missing whole-block execution/value/race claims"),
        ("omitted-source-initializer",args.packet,{"whole_block_source_initializer_bound":False},"Missing whole-block execution/value/race claims"),
        ("omitted-repaired-classification",args.packet,{"repaired_whole_block_trace_classification_proved":False},"Missing whole-block execution/value/race claims"),
        ("omitted-repaired-race-proof",args.packet,{"repaired_whole_block_race_freedom_proved":False},"Missing whole-block execution/value/race claims"),
        ("invented-original-race-freedom",args.packet,{"original_whole_block_race_freedom_proved":True},"Invented original race freedom or whole-grid execution"),
        ("invented-whole-grid",args.packet,{"whole_grid_execution_proved":True},"Invented original race freedom or whole-grid execution"),
        ("wrong-whole-halt-PC",args.packet,{"whole_block_halt_pc":{"original":115,"fixed":116}},"Wrong whole-block normalization counts/endpoint/fuel"),
        ("wrong-whole-epoch",args.packet,{"whole_block_epoch":5},"Wrong whole-block normalization counts/endpoint/fuel"),
        ("wrong-normalization-rounds",args.packet,{"normalization_outer_rounds":6},"Wrong whole-block normalization counts/endpoint/fuel"),
        ("wrong-normalization-components",args.packet,{"normalization_components_per_round":7},"Wrong whole-block normalization counts/endpoint/fuel"),
        ("wrong-normalization-lane-cost",args.packet,{},"Wrong whole-block normalization counts/endpoint/fuel"),
        ("wrong-normalization-lane-accesses",args.packet,{},"Wrong whole-block normalization counts/endpoint/fuel"),
        ("wrong-normalization-block-accesses",args.packet,{},"Wrong whole-block normalization counts/endpoint/fuel"),
        ("wrong-whole-block-accesses",args.packet,{},"Wrong whole-block normalization counts/endpoint/fuel"),
        ("wrong-whole-proof-closure",args.packet,{"local_lean_modules":119},"Wrong whole-block proof closure or original fuel"),
        ("boolean-whole-grid-fuel",args.packet,{},"Wrong whole-block proof closure or original fuel"),
        ("wrong-whole-first-output",args.packet,{},"Wrong whole-block converted-output diagnostic"),
        ("wrong-whole-last-output",args.packet,{},"Wrong whole-block converted-output diagnostic"),
        ("wrong-whole-division-model",args.packet,{},"Wrong whole-block converted-output diagnostic"),
        ("omitted-whole-run-audit",args.packet,{},"Principal reduction-prefix audits absent"),
        ("omitted-whole-output-audit",args.packet,{},"Principal reduction-prefix audits absent"),
        ("omitted-norm-component-audit",args.packet,{},"Principal reduction-prefix audits absent"),
        ("omitted-whole-refusal-check",args.packet,{},"Wrong reduction-prefix replay checks"),
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
        if name == "wrong-reduction-prefix-word":
            report["exp_wave_word_cases"]["1:1"] += 1
        if name == "omitted-reduction-prefix-run-audit":
            del report["axiom_audits"]["source_exp_wave_initial_run"]
        if name == "omitted-reduction-prefix-partial-audit":
            del report["axiom_audits"]["source_exp_wave_partial_run"]
        if name == "wrong-reduction-projection-total":
            report["reduction_projection_values"]["total"] += 1
        if name == "omitted-reduction-output-audit":
            del report["axiom_audits"]["source_sum_output_run"]
        if name == "omitted-reduction-run-audit":
            del report["axiom_audits"]["source_reduction_initial_run"]
        if name == "omitted-serial-checksum-audit":
            del report["axiom_audits"]["source_sum_checksum_run"]
        if name == "omitted-refusal-check":
            report["checks"].pop()
        if name == "earlier-reduction-relabeled":
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
                        "actual_exp_wave_fold_execution_proved", "actual_exp_block_phase_execution_proved",
                        "exp_wave_parked_pc", "exp_wave_block_epoch", "exp_wave_logical_partials", "exp_wave_sum_stages",
                        "exp_wave_shuffle_kind", "exp_wave_logical_width", "exp_wave_source_ordered_sum_proved",
                        "exp_wave_snapshot_transport_proved", "exp_wave_partial_values_proved", "exp_wave_race_freedom_proved",
                        "third_barrier_resume_proved", "serial_sum_execution_proved", "exp_wave_word_cases",
                        "exp_wave_word_actual_partial_values_proved", 'actual_reduction_prefix_some_execution_proved', 'reduction_prefix_linked_to_runBlock', 'fourth_barrier_resume_proved', 'reduction_phases', 'reduction_parked_pc', 'reduction_resumed_pc', 'reduction_block_epoch', 'remaining_block_fuel_after_sum', 'accesses_per_exp_block_phase', 'accesses_after_third_barrier', 'shared_reads_per_serial_sum_phase', 'shared_writes_per_serial_sum_phase', 'accesses_after_fourth_barrier', 'all32_exp_partial_values_proved', 'all32_serial_sum_partial_reads_proved', 'source_ordered_row_sum_proved', 'all_exponential_output_values_preserved_proved', 'reduction_prefix_race_freedom_proved', 'reduction_projection_model', 'reduction_projection_values', 'reduction_projection_actual_full_prefix_values_proved', 'serial_checksum_model', 'serial_checksum', 'serial_checksum_isolated_actual_phase_proved', 'serial_checksum_scope', 'normalization_execution_proved'):
                report[key] = block[key]
        if name=="earlier-reduction-relabeled":
            for key in ('actual_whole_block_some_execution_proved', 'all_five_source_block_phases_proved', 'whole_block_source_ordered_outputs_proved', 'whole_block_source_initializer_bound', 'repaired_whole_block_trace_classification_proved', 'repaired_whole_block_race_freedom_proved', 'original_whole_block_race_freedom_proved', 'whole_grid_execution_proved', 'normalization_outer_rounds', 'normalization_components_per_round', 'whole_block_epoch', 'whole_block_halt_pc', 'normalization_lane_costs', 'normalization_lane_accesses', 'normalization_block_accesses', 'whole_block_accesses', 'whole_block_word', 'whole_block_actual_converted_output_values_proved', 'local_lean_modules'):report[key]=block[key]
        if name=="wrong-normalization-lane-cost":report["normalization_lane_costs"]["fixed"]["tid81_to1023"]+=1
        if name=="wrong-normalization-lane-accesses":report["normalization_lane_accesses"]["original"]["tid0_to80"]-=1
        if name=="wrong-normalization-block-accesses":report["normalization_block_accesses"]["fixed"]+=1
        if name=="wrong-whole-block-accesses":report["whole_block_accesses"]["original"]-=1
        if name=="boolean-whole-grid-fuel":report["original_fuel"]["grid"]=True
        if name=="wrong-whole-first-output":report["whole_block_word"]["outputs"]["0"]=15
        if name=="wrong-whole-last-output":report["whole_block_word"]["outputs"]["50256"]=147
        if name=="wrong-whole-division-model":report["whole_block_word"]["model"]["div"]="reversed division"
        if name=="omitted-whole-run-audit":del report["axiom_audits"]["source_whole_block_run"]
        if name=="omitted-whole-output-audit":del report["axiom_audits"]["source_whole_block_output_run"]
        if name=="omitted-norm-component-audit":del report["axiom_audits"]["LarkNativeSoftmax.norm_store_component_eq"]
        if name=="omitted-whole-refusal-check":
            report["checks"]=[c for c in report["checks"] if c["name"]!="whole-output-without-from-half"]
        (packet / "results.json").write_text(json.dumps(report, indent=2) + "\n")
        (packet / "manifest.json").write_text(json.dumps({p.name: sha(p) for p in sorted(packet.iterdir())
                                                          if p.name != "manifest.json"}, indent=2) + "\n")
        target = folder / "attempted-replay"
        command = [sys.executable, str(HERE / "replay_whole_block.py"), "--packet", str(packet),
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
        "schema": 1, "status": "fully-rehashed-false-whole-block-stage-claims-rejected-before-extraction",
        "checks": records, "exp_prefix_packet_manifest_sha256": sha(args.packet / "manifest.json"),
        "earlier_packet_manifest_sha256": sha(args.earlier_packet / "manifest.json"),
        "replayer_sha256": sha(HERE / "replay_whole_block.py"), "source_certificates": 0,
        "whole_kernel_execution_proved": False, "original_paper_fully_reproduced": False,
    }
    (out / "results.json").write_text(json.dumps(report, indent=2) + "\n")
    shutil.copyfile(Path(__file__), out / "checker.py")
    (out / "manifest.json").write_text(json.dumps({p.name: sha(p) for p in sorted(out.iterdir()) if p.is_file()}, indent=2) + "\n")
    print(json.dumps({"status": report["status"], "checks": len(records)}))


if __name__ == "__main__":
    main()
