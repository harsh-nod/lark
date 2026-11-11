"""Replay the source-bound complete repaired native softmax grid archive without Git or own Lean cache."""

import argparse
import gzip
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import shutil
import subprocess
import sys
import tarfile
import time


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def trace_sha(path):
    digest = hashlib.sha256()
    with gzip.open(path, "rb") as stream:
        for part in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(part)
    return digest.hexdigest()


def expected_word(tid):
    total, count = 0, 0
    for linear in range(56):
        column = tid+linear*1024
        if column<50257:
            value = 5*(2*(3*(column+1)+1)+150772)+3
            total, count = 7*total+value, count+1
    first = 5*(2*(3*(tid+1)+1)+150772)+3
    return {"valid":count,"sum":total,"first_unrounded":first,"first_output":7*first+1}


def expected_wave(warp,half):
    def tree(stage,lane):
        if stage==0:
            return expected_word(warp*64+lane)["sum"]
        peer=(lane//32)*32+((lane%32)^(1<<(5-stage)))
        return 7*tree(stage-1,lane)+tree(stage-1,peer)
    return tree(5,half*32)


def expected_projection():
    maximum=3*50257+1
    partials=[]
    for logical in range(32):
        tid=logical*32+31
        last=tid+((50256-tid)//1024)*1024
        partials.append(5*(2*(3*(last+1)+1)+maximum)+3)
    return {"maximum":maximum,"total":partials[-1],
            "outputs":{str(col):7*(5*(2*(3*(col+1)+1)+maximum)+3)+1 for col in (0,50256)}}


def expected_serial_checksum():
    return sum((slot+1)*7**(31-slot) for slot in range(32))



def exact_data(actual,expected):
    if type(expected) is dict:
        return type(actual) is dict and actual.keys()==expected.keys() and all(exact_data(actual[k],v) for k,v in expected.items())
    return type(actual) is type(expected) and actual==expected


def expected_normalization():
    costs,accesses,totals={},{},{}
    for guarded,label in ((False,"original"),(True,"fixed")):
        lanes=[]
        for tid in range(1024):
            steps,events=2,1
            for iteration in range(7):
                steps+=4
                for component in range(8):
                    valid=tid+(8*iteration+component)*1024<50257
                    load=(not guarded) or valid
                    choice=1 if guarded or valid else 2
                    steps+=4+choice+2*load
                    events+=2*load
                for component in range(8):
                    valid=tid+(8*iteration+component)*1024<50257
                    steps+=5+3*valid
                    events+=2*valid
                steps+=3
            lanes.append((steps+1,events))
        assert all(lanes[t]==lanes[0 if t<81 else 81] for t in range(1024))
        costs[label]={"tid0_to80":lanes[0][0],"tid81_to1023":lanes[81][0]}
        accesses[label]={"tid0_to80":lanes[0][1],"tid81_to1023":lanes[81][1]}
        totals[label]=sum(x[1] for x in lanes)
    return {"normalization_lane_costs":costs,"normalization_lane_accesses":accesses,
            "normalization_block_accesses":totals,"whole_block_accesses":{k:273700+v for k,v in totals.items()}}


def expected_whole_word():
    values=expected_projection()
    return {"model":{"max":"right projection","add":"right projection","sub":"2*a+b",
                    "exp":"5*a+3","fromHalf":"3*a+1","toHalf":"7*a+1","div":"Nat floor division"},
            "total":values["total"],"outputs":{col:7*((3*value+1)//values["total"])+1 for col,value in values["outputs"].items()}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--packet", type=Path, required=True)
    parser.add_argument("--finite-trace-packet", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--lean-bin", type=Path, required=True)
    args = parser.parse_args()
    packet, finite, out, lean_bin = (p.resolve() for p in (args.packet, args.finite_trace_packet, args.output, args.lean_bin))
    require(not any((p / ".git").exists() for p in (out, *out.parents)), "Choose output outside Git")
    require(shutil.which("git", path=str(lean_bin)) is None, "Git must be unavailable on replay PATH")
    version = subprocess.check_output([str(lean_bin / "lean"), "--version"], text=True, timeout=30)
    require("version 4.19.0" in version, "Pinned Lean4.19.0 required")
    for folder in (packet, finite):
        for name, digest in json.loads((folder / "manifest.json").read_text()).items():
            require(Path(name).name == name and sha(folder / name) == digest, "Packet path/hash differs: " + name)
    report = json.loads((packet / "results.json").read_text())
    require(report.get("status") == "native-softmax-source-bound-whole-grid-checked"
            and report.get("stage") == "whole-grid", "Wrong proof stage")
    require(type(report.get("source_certificates")) is int and report["source_certificates"] == 0,
            "Invented source certificate")
    require(all(report.get(name) is False for name in (
        "conflict_witness_state_reachability_proved",
        "actual_trace_universal_classification_proved", "canonical_source_equivalence_proved",
        "ieee_equivalence_proved", "original_paper_fully_reproduced", "race_freedom_assumed")),
        "Invented whole-source/reference claim or assumed race freedom")
    require(all(report.get(name) is True for name in (
        "actual_first_block_wave_fold_execution_proved", "starts_at_actual_initializer",
        "all32_source_ordered_partial_values_proved", "earlier_waves_preserved_proved",
        "first_barrier_resume_proved", "block_scheduler_decomposition_proved", "maximum_global_memory_frame_proved",
        "checksum_final_partial_actual_fold_value_proved", "first_block_race_freedom_proved",
        "actual_serial_block_wave_fold_execution_proved", "all32_serial_partial_reads_proved",
        "second_barrier_resume_proved", "maximum_pass_race_freedom_proved",
        "checksum_row_maximum_actual_fold_value_proved")),
        "Missing maximum-pass claims")
    require(report.get("rows") == {"min":1,"max":42730}
            and report.get("maximum_parked_pc") == 42 and report.get("maximum_resumed_pc") == 43
            and report.get("maximum_block_epoch") == 2
            and report.get("physical_waves_per_block") == 16 and report.get("threads_per_block") == 1024
            and report.get("logical_partials_per_block") == 32
            and report.get("accesses_per_maximum_pass") == 57409 and report.get("input_reads_per_maximum_pass") == 57344
            and report.get("shared_writes_per_maximum_pass") == 33
            and report.get("shared_reads_per_maximum_pass") == 32 and report.get("remaining_block_fuel_after_maximum") == 3
            and report.get("checksum_final_partial") == 405347395513415502166905022412032
            and report.get("checksum_row_maximum") == 133254668662643834119504341449835759241818635200
            and report.get("checksum_max_operation") == "3*a+b"
            and report.get("original_fuel") == {"lane":4096,"warp":8,"block":5,"grid":1},
            "Wrong maximum-pass endpoint/accesses/partials/fuel/checksum")
    require(report.get("normalization_execution_proved") is True, "Missing normalization execution")
    require(all(report.get(name) is True for name in (
        "actual_whole_block_some_execution_proved","all_five_source_block_phases_proved",
        "whole_block_source_ordered_outputs_proved","whole_block_source_initializer_bound",
        "repaired_whole_block_trace_classification_proved","repaired_whole_block_race_freedom_proved",
        "whole_block_actual_converted_output_values_proved")),"Missing whole-block execution/value/race claims")
    require(report.get("original_whole_block_race_freedom_proved") is False and report.get("original_whole_grid_execution_proved") is False,
        "Invented original-source grid or race-freedom claim")
    expected={**expected_normalization(),"normalization_outer_rounds":7,"normalization_components_per_round":8,
              "whole_block_epoch":4,"whole_block_halt_pc":{"original":116,"fixed":115}}
    require(all(exact_data(report.get(k),v) for k,v in expected.items()),"Wrong whole-block normalization counts/endpoint/fuel")
    require(exact_data(report.get("original_fuel"),{"lane":4096,"warp":8,"block":5,"grid":1})
            and type(report.get("local_lean_modules")) is int and report["local_lean_modules"]==125,
            "Wrong whole-grid proof closure or original fuel")
    require(exact_data(report.get("whole_block_word"),expected_whole_word()),"Wrong whole-block converted-output diagnostic")

    require(all(report.get(name) is True for name in (
        "whole_kernel_execution_proved", "whole_grid_execution_proved",
        "repaired_whole_grid_some_execution_proved", "repaired_whole_grid_race_freedom_proved",
        "repaired_whole_grid_trace_classification_proved", "repaired_whole_grid_all_outputs_proved",
        "repaired_whole_grid_extract_proved", "repaired_whole_grid_source_order_correct_proved",
        "whole_grid_source_initializer_bound", "foreign_block_control_and_memory_frames_proved",
        "grid_all_supported_rows_proved")), "Missing repaired whole-grid execution/value/race claims")
    require(exact_data(report.get("whole_grid_variants"),["fixed"])
        and all(type(report.get(k)) is int and report[k]==v for k,v in {
            "grid_halt_pc":115,"grid_block_epoch":4,"grid_accesses_per_row":475752,
            "grid_output_cells_per_row":50257,"inherited_block_controls_previously_rejected":129}.items()),
        "Wrong repaired whole-grid endpoint/counts/scope")
    require(report.get("scope")=="Actual repaired complete grid under arbitrary Ops; original source complete block only. No algebraic rearrangement, canonical-real or IEEE bridge asserted here."
        and report.get("inherited_block_evidence")=="results/whole-block-v1 and whole-block-validation-v1; not counted again in this packet's false claims",
        "Wrong repaired whole-grid interpretation or inherited-control scope")

    require(all(report.get(name) is True for name in (
        "actual_exp_block_phase_execution_proved", "third_barrier_resume_proved", "serial_sum_execution_proved",
        "actual_reduction_prefix_some_execution_proved", "reduction_prefix_linked_to_runBlock", "fourth_barrier_resume_proved",
        "all32_exp_partial_values_proved", "all32_serial_sum_partial_reads_proved", "source_ordered_row_sum_proved",
        "all_exponential_output_values_preserved_proved", "reduction_prefix_race_freedom_proved",
        "reduction_projection_actual_full_prefix_values_proved", "serial_checksum_isolated_actual_phase_proved")),
        "Missing constructive reduction-prefix claims")
    expected_counts={"reduction_phases":4,"reduction_parked_pc":92,"reduction_resumed_pc":93,
        "reduction_block_epoch":4,"remaining_block_fuel_after_sum":1,"accesses_per_exp_block_phase":216258,
        "accesses_after_third_barrier":273667,"shared_reads_per_serial_sum_phase":32,
        "shared_writes_per_serial_sum_phase":1,"accesses_after_fourth_barrier":273700}
    require(all(type(report.get(k)) is int and report[k]==v for k,v in expected_counts.items()),
        "Wrong reduction-prefix endpoint/counts/fuel")
    require(report.get("reduction_projection_model")=={"max":"right projection","add":"right projection","sub":"2*a+b",
        "exp":"5*a+3","fromHalf":"3*a+1","toHalf":"7*a+1"}
        and report.get("reduction_projection_values")==expected_projection()
        and report.get("serial_checksum_model")=="7*a+b, slots1..32"
        and report.get("serial_checksum")==expected_serial_checksum()
        and report.get("serial_checksum_scope")=="Synthetic PC83/epoch3 entry for the actual serial phase; separate from the full-prefix projection witness.",
        "Wrong reduction-prefix diagnostic values/scope")
    require(all(report.get(name) is True for name in ("actual_exp_wave_fold_execution_proved",
            "exp_wave_source_ordered_sum_proved", "exp_wave_snapshot_transport_proved",
            "exp_wave_partial_values_proved", "exp_wave_race_freedom_proved",
            "exp_wave_word_actual_partial_values_proved")), "Missing reduction-prefix claims")
    require(report.get("exp_wave_parked_pc")==82 and report.get("exp_wave_block_epoch")==2
            and report.get("exp_wave_logical_partials")==2 and report.get("exp_wave_sum_stages")==5
            and report.get("exp_wave_shuffle_kind")=="xor" and report.get("exp_wave_logical_width")==32
            and report.get("exp_wave_word_cases")=={f"{w}:{h}":expected_wave(w,h) for w,h in ((0,0),(0,1),(1,0),(1,1),(15,0),(15,1))},
            "Wrong reduction-prefix endpoint/partition/word values")
    require(all(report.get(name) is True for name in (
        "actual_exp_scalar_lane_prefix_execution_proved", "exp_starts_at_proved_maximum_state",
        "exp_converted_outputs_proved", "exp_unrounded_source_ordered_sum_proved",
        "exp_prefix_race_freedom_proved", "exp_native_indices_preserved_proved",
        "exp_word_actual_sum_and_output_values_proved")), "Missing reduction-prefix claims")
    require(report.get("exp_parked_pc")==70 and report.get("exp_block_epoch")==2
            and report.get("exp_outer_rounds")==7 and report.get("exp_components_per_round")==8
            and report.get("exp_lane_costs")=={"tid0_to80":982,"tid81_to1023":978}
            and report.get("exp_lane_access_increments")=={"tid0_to80":213,"tid81_to1023":211}
            and report.get("exp_valid_stores_per_lane")=={"tid0_to80":50,"tid81_to1023":49}
            and report.get("exp_word_maximum")==150772
            and report.get("exp_word_model")=={"max":"right projection","add":"7*a+b","sub":"2*a+b",
                "exp":"5*a+3","fromHalf":"3*a+1","toHalf":"7*a+1"}
            and report.get("exp_word_cases")=={str(tid):expected_word(tid) for tid in (0,80,81,1023)},
            "Wrong reduction-prefix endpoint/counts/word model")
    principal = {"source_program_data", "source_block_fold_data", "source_block_data",
                 "source_block_initial_fold_run", "source_block_initial_partial_run", "source_block_initial_good",
                 "source_block_initial_pc", "source_block_initial_partial", "source_block_initial_trace_length",
                 "source_initial_block_barrier", "source_mid_initial_pc", "source_mid_initial_epoch",
                 "source_mid_initial_memory_frame", "source_mid_initial_rf", "source_block_initial_rf",
                 "source_checksum_last_partial", "source_checksum_last_partial_run",
                 "LarkNativeSoftmax.first_block_fold_run", "LarkNativeSoftmax.first_block_partial",
                 "LarkNativeSoftmax.first_block_trace_length", "LarkNativeSoftmax.initial_first_barrier",
                 "LarkNativeSoftmax.mid_ready", "LarkNativeSoftmax.initial_mid_race_free",
                 "source_wave_initial_run", "source_prefix_initial_run", "source_prefix_word_0", "source_prefix_word_81"}
    principal |= {
        'LarkNativeSoftmax.initial_maximum_block',
        'LarkNativeSoftmax.initial_maximum_race_free',
        'LarkNativeSoftmax.initial_maximum_ready',
        'LarkNativeSoftmax.maximum_trace_length',
        'LarkNativeSoftmax.serial_block_fold_run',
        'LarkNativeSoftmax.serial_block_step',
        'source_block_initial_fold_run',
        'source_checksum_last_partial_run',
        'source_checksum_maximum',
        'source_checksum_maximum_run',
        'source_initial_block_barrier',
        'source_initial_maximum_block',
        'source_maximum_initial_epoch',
        'source_maximum_initial_good',
        'source_maximum_initial_memory_frame',
        'source_maximum_initial_pc',
        'source_maximum_initial_ready',
        'source_maximum_initial_rf',
        'source_maximum_initial_trace_length',
        'source_maximum_initial_value',
        'source_serial_initial_fold_run',
        'source_serial_initial_maximum_run',
    }
    principal |= {
        'LarkNativeSoftmax.exp_prefix_cost_exact',
        'LarkNativeSoftmax.exp_prefix_outputs',
        'LarkNativeSoftmax.exp_prefix_run',
        'LarkNativeSoftmax.exp_prefix_trace_exact',
        'LarkNativeSoftmax.initial_exp_prefix_race_free',
        'LarkNativeSoftmax.initial_exp_prefix_run',
        'exp_word_maximum',
        'exp_word_output_0',
        'exp_word_output_1023',
        'exp_word_output_80',
        'exp_word_output_81',
        'exp_word_sum_0',
        'exp_word_sum_1023',
        'exp_word_sum_80',
        'exp_word_sum_81',
        'source_exp_initial_entry',
        'source_exp_initial_epoch',
        'source_exp_initial_good',
        'source_exp_initial_native',
        'source_exp_initial_outputs',
        'source_exp_initial_pc',
        'source_exp_initial_rf',
        'source_exp_initial_run',
        'source_exp_initial_sum',
        'source_exp_initial_trace_length',
        'source_exp_initial_trace_total',
        'source_exp_output_run',
        'source_exp_output_value',
        'source_exp_register_of_run',
        'source_exp_sum_run',
        'source_exp_trace_total_of_start',
        'source_exp_word_output_0',
        'source_exp_word_output_1023',
        'source_exp_word_output_80',
        'source_exp_word_output_81',
        'source_exp_word_output_run',
        'source_exp_word_sum_0',
        'source_exp_word_sum_1023',
        'source_exp_word_sum_80',
        'source_exp_word_sum_81',
        'source_exp_word_sum_run',
    }
    principal |= {'LarkNativeSoftmax.exp_wave_sum', 'source_exp_wave_initial_sum', 'source_exp_wave_initial_epoch', 'LarkNativeSoftmax.initial_exp_wave', 'exp_wave_word_0_1', 'source_exp_wave_word_15_0', 'source_exp_wave_word_1_0', 'LarkNativeSoftmax.exp_wave_run', 'source_exp_wave_initial_good', 'source_exp_wave_initial_partial', 'LarkNativeSoftmax.exp_wave_partial', 'source_exp_wave_word_0_0', 'source_exp_wave_initial_pc', 'LarkNativeSoftmax.sum_xor_peer_partition', 'source_exp_wave_word_15_1', 'source_exp_wave_initial_rf', 'source_exp_wave_sum_run', 'source_exp_wave_word_1_1', 'LarkNativeSoftmax.sum_last_wave_warp', 'exp_wave_word_1_0', 'LarkNativeSoftmax.exp_wave_of_maximum', 'LarkNativeSoftmax.exp_wave_race_free', 'LarkNativeSoftmax.native_sum_first_four_of_cohort', 'source_exp_wave_partial_run', 'exp_wave_word_15_0', 'source_exp_wave_word_0_1', 'exp_wave_word_0_0', 'exp_wave_word_1_1', 'exp_wave_word_15_1', 'source_exp_wave_initial_run', 'LarkNativeSoftmax.cohort_sum_xor_shuffle'}
    principal |= {'source_sum_initial_good', 'source_reduction_projection_output_50256', 'source_sum_initial_trace', 'source_sum_initial_ready', 'source_initial_sum_block', 'sum_checksum_entry', 'reduction_projection_output_0', 'source_sum_checksum_run', 'reduction_projection_total', 'source_sum_initial_pc', 'source_reduction_prefix_data', 'LarkNativeSoftmax.sum_serial_block_value', 'LarkNativeSoftmax.initial_sum_race_free', 'reduction_projection_maximum', 'LarkNativeSoftmax.reduction_prefix_continue', 'source_sum_initial_total', 'LarkNativeSoftmax.sum_state_outputs', 'source_sum_total_run', 'LarkNativeSoftmax.exp_block_partial', 'LarkNativeSoftmax.exp_block_outputs', 'source_reduction_phase_data', 'LarkNativeSoftmax.initial_sum_block', 'LarkNativeSoftmax.initial_after_exp_trace_length', 'source_sum_initial_outputs', 'LarkNativeSoftmax.reduction_phase_continue', 'source_sum_initial_output', 'source_sum_output_run', 'source_reduction_projection_total', 'source_sum_initial_epoch', 'reduction_projection_output_50256', 'LarkNativeSoftmax.initial_sum_ready', 'LarkNativeSoftmax.initial_sum_trace_length', 'source_reduction_projection_output_0', 'LarkNativeSoftmax.reduction_prefix_run', 'LarkNativeSoftmax.initial_reduction_prefix', 'LarkNativeSoftmax.exp_block_fold_run', 'source_reduction_continuation', 'source_reduction_initial_run', 'sum_checksum_closed', 'source_sum_initial_rf', 'LarkNativeSoftmax.initial_exp_barrier', 'LarkNativeSoftmax.sum_serial_block_fold_run', 'source_sum_checksum_fold'}
    principal |= {'LarkNativeSoftmax.norm_block_outputs', 'source_whole_block_outputs', 'LarkNativeSoftmax.norm_wave_fold_run', 'LarkNativeSoftmax.norm_scalar_fold_run', 'source_whole_block_not_none', 'source_normalization_lane_cost', 'LarkNativeSoftmax.whole_block_outputs', 'LarkNativeSoftmax.norm_lane_entry_other', 'source_whole_block_run', 'LarkNativeSoftmax.whole_block_run', 'LarkNativeSoftmax.norm_lane_run', 'LarkNativeSoftmax.initial_whole_block_fixed_race_free', 'whole_projection_value_0', 'source_whole_block_pc', 'source_whole_projection_output_0', 'LarkNativeSoftmax.norm_block_run', 'LarkNativeSoftmax.norm_load_component_eq', 'LarkNativeSoftmax.norm_store_component_eq', 'LarkNativeSoftmax.norm_lane_trace_exact', 'source_whole_block_trace', 'source_whole_projection_output_50256', 'source_whole_block_fixed_rf', 'LarkNativeSoftmax.norm_sample_of_present', 'source_normalization_lane_run', 'LarkNativeSoftmax.norm_block_accesses', 'source_whole_block_output_run', 'LarkNativeSoftmax.norm_lane_cost_exact', 'whole_projection_value_50256', 'LarkNativeSoftmax.initial_whole_block_trace_length', 'source_whole_block_epoch', 'LarkNativeSoftmax.initial_whole_block', 'source_whole_block_output', 'source_whole_block_fixed_good', 'LarkNativeSoftmax.norm_wave_run'}
    principal |= {
        'LarkNativeSoftmax.address_writer_row',
        'LarkNativeSoftmax.after_exp_foreign_epoch',
        'LarkNativeSoftmax.after_exp_foreign_pc',
        'LarkNativeSoftmax.after_maximum_foreign_epoch',
        'LarkNativeSoftmax.after_maximum_foreign_pc',
        'LarkNativeSoftmax.after_sum_foreign_epoch',
        'LarkNativeSoftmax.after_sum_foreign_pc',
        'LarkNativeSoftmax.exp_block_output_foreign',
        'LarkNativeSoftmax.first_block_foreign_pc',
        'LarkNativeSoftmax.fixed_block_fold_epoch_other',
        'LarkNativeSoftmax.fixed_block_fold_good',
        'LarkNativeSoftmax.fixed_block_fold_member_epoch',
        'LarkNativeSoftmax.fixed_block_fold_member_pc',
        'LarkNativeSoftmax.fixed_block_fold_output_member',
        'LarkNativeSoftmax.fixed_block_fold_output_other',
        'LarkNativeSoftmax.fixed_block_fold_pc_other',
        'LarkNativeSoftmax.fixed_block_fold_reads',
        'LarkNativeSoftmax.fixed_block_fold_run',
        'LarkNativeSoftmax.fixed_block_fold_trace_length',
        'LarkNativeSoftmax.fixed_grid_cut',
        'LarkNativeSoftmax.fixed_grid_epoch',
        'LarkNativeSoftmax.fixed_grid_fold_run',
        'LarkNativeSoftmax.fixed_grid_good',
        'LarkNativeSoftmax.fixed_grid_outputs',
        'LarkNativeSoftmax.fixed_grid_pc',
        'LarkNativeSoftmax.fixed_grid_reads',
        'LarkNativeSoftmax.fixed_grid_run',
        'LarkNativeSoftmax.fixed_grid_trace_length',
        'LarkNativeSoftmax.fixed_launch_run',
        'LarkNativeSoftmax.foreign_block_contains_false',
        'LarkNativeSoftmax.foreign_cohort_absent',
        'LarkNativeSoftmax.grid_halt_of_pc',
        'LarkNativeSoftmax.grid_rows_entry_tail',
        'LarkNativeSoftmax.initial_fixed_grid_extract',
        'LarkNativeSoftmax.initial_fixed_grid_flat_output',
        'LarkNativeSoftmax.initial_fixed_grid_output',
        'LarkNativeSoftmax.initial_fixed_grid_race_free',
        'LarkNativeSoftmax.initial_fixed_grid_trace_length',
        'LarkNativeSoftmax.initial_fixed_launch',
        'LarkNativeSoftmax.initial_grid_rows_entry',
        'LarkNativeSoftmax.maximum_foreign_epoch',
        'LarkNativeSoftmax.maximum_foreign_pc',
        'LarkNativeSoftmax.mid_foreign_epoch',
        'LarkNativeSoftmax.mid_foreign_pc',
        'LarkNativeSoftmax.norm_block_foreign_pc',
        'LarkNativeSoftmax.norm_block_output_foreign',
        'LarkNativeSoftmax.norm_block_reads',
        'LarkNativeSoftmax.norm_scalar_fold_input_memory',
        'LarkNativeSoftmax.norm_wave_fold_input_memory',
        'LarkNativeSoftmax.norm_wave_input_memory',
        'LarkNativeSoftmax.resume_foreign_epoch',
        'LarkNativeSoftmax.resume_foreign_pc',
        'LarkNativeSoftmax.source_extract_of_values',
        'LarkNativeSoftmax.source_order_correct',
        'LarkNativeSoftmax.source_ordered_spec_length',
        'LarkNativeSoftmax.sum_state_foreign_epoch',
        'LarkNativeSoftmax.sum_state_foreign_pc',
        'LarkNativeSoftmax.sum_state_output_foreign',
        'LarkNativeSoftmax.whole_block_entry_epoch',
        'LarkNativeSoftmax.whole_block_fixed_entry_other',
        'LarkNativeSoftmax.whole_block_foreign_epoch',
        'LarkNativeSoftmax.whole_block_foreign_pc',
        'LarkNativeSoftmax.whole_block_other_row_output',
        'LarkNativeSoftmax.whole_block_output_foreign',
        'LarkNativeSoftmax.whole_block_reads',
        'source_fixed_grid_correct',
        'source_fixed_grid_epoch',
        'source_fixed_grid_extract',
        'source_fixed_grid_launch',
        'source_fixed_grid_output',
        'source_fixed_grid_pc',
        'source_fixed_grid_rf',
        'source_fixed_grid_trace',
        'source_launch_data',
    }
    require(principal <= report["axiom_audits"].keys(), "Principal whole-grid audits absent")
    required_controls = {
        'denied-grid-output-length',
        'denied-grid-trace-count',
        'grid-fixed-division',
        'grid-fixed-load-guard',
        'grid-fixed-stride',
        'invented-grid-none',
        'invented-grid-race',
        'missing-grid-extraction',
        'missing-grid-output',
        'wrong-grid-epoch',
        'wrong-grid-halt',
    }
    require(type(report.get("false_lean_claims_rejected")) is int
            and report["false_lean_claims_rejected"] == len(required_controls), "Wrong whole-grid refusal count")
    required_checks = required_controls | {"frozen-reader", "fresh-library-build", "fresh-exp-library-build", "fresh-wave-library-build", "fresh-reduction-library-build", "fresh-grid-library-build", "fresh-build"}
    require(len(report["checks"]) == len(required_checks)
            and {c["name"] for c in report["checks"]} == required_checks
            and all(c["expected_accepted"] is (c["name"] in {"frozen-reader", "fresh-library-build", "fresh-exp-library-build", "fresh-wave-library-build", "fresh-reduction-library-build", "fresh-grid-library-build", "fresh-build"})
                    for c in report["checks"]), "Wrong whole-grid replay checks")
    require(sha(packet / "source.tar.gz") == report["source_archive_sha256"], "Source archive differs")
    source_manifest = json.loads((packet / "source-manifest.json").read_text())
    out.mkdir(parents=True, exist_ok=False)
    project = out / "project"
    project.mkdir()
    seen, total = set(), 0
    with tarfile.open(packet / "source.tar.gz") as archive:
        for member in archive:
            rel = PurePosixPath(member.name)
            require(member.isfile() and not rel.is_absolute() and ".." not in rel.parts
                    and ".git" not in rel.parts and ".lake" not in rel.parts
                    and member.name not in seen and member.name in source_manifest, "Unsafe/unexpected source entry")
            total += member.size
            require(member.size < 8_000_000 and total < 50_000_000, "Source archive exceeds bounds")
            content = archive.extractfile(member).read()
            require(hashlib.sha256(content).hexdigest() == source_manifest[member.name], "Source hash differs")
            target = project / rel
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(content)
            seen.add(member.name)
    require(seen == set(source_manifest) and not (project / ".lake").exists()
            and not any(project.rglob("*.olean")), "Unexpected own source/cache")
    require(sum(name.startswith("Lark/") and name.endswith(".lean") for name in source_manifest) ==
            report["local_lean_modules"], "Proof closure module count differs")
    env = dict(os.environ)
    env["PATH"] = str(lean_bin)
    env.pop("PYTHONPATH", None)
    env.pop("LEAN_PATH", None)
    env["PYTHONNOUSERSITE"] = "1"
    checks = []
    for record in report["checks"]:
        name, expected = record["name"], record["expected_accepted"]
        require(re.fullmatch(r"[a-z0-9-]+", name), "Unexpected check name")
        command = ([sys.executable, "validate_source.py"] if name == "frozen-reader"
                   else ["lake", "build", "Lark.NativeSoftmaxMaximum", "Lark.NativeSoftmaxWitness"] if name == "fresh-library-build"
                   else ["lake", "build", "Lark.NativeSoftmaxExpPrefixCounts"] if name == "fresh-exp-library-build"
                   else ["lake", "build", "Lark.NativeSoftmaxExpWave"] if name == "fresh-wave-library-build"
                   else ["lake", "build", "Lark.NativeSoftmaxReductionPrefix"] if name == "fresh-reduction-library-build"
                   else ["lake", "build", "Lark.NativeSoftmaxCorrect"] if name == "fresh-grid-library-build"
                   else ["lake", "build"] if name == "fresh-build"
                   else ["lake", "env", "lean", name + ".lean"])
        before = time.monotonic()
        run = subprocess.run(command, cwd=project, env=env, capture_output=True, text=True, timeout=180)
        log = run.stdout + run.stderr
        (out / (name + ".log")).write_text(log)
        accepted = run.returncode == 0 and "error:" not in log and "sorryAx" not in log
        require(accepted is expected, "Unexpected acceptance: " + name + "\n" + log)
        if not expected:
            require("is false" in log and "maximum recursion depth" not in log
                    and "maximum heartbeats" not in log and "deep recursion detected" not in log,
                    "Wrong rejection gate: " + name)
        if name == "fresh-build":
            audits = dict(re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", log))
            require(audits == report["axiom_audits"], "Fresh axiom audits differ")
            for axioms in audits.values():
                require(set(a.strip() for a in axioms.split(",") if a.strip()) <=
                        {"propext", "Classical.choice", "Quot.sound"}, "Extra axiom")
        checks.append({"name": name, "accepted": accepted, "expected_accepted": expected,
                       "exit_code": run.returncode, "seconds": time.monotonic() - before, "timed_out": False})
    before = time.monotonic()
    run = subprocess.run([sys.executable, "reproduction/production_softmax/trace_full.py", "--output", str(out / "finite-replay")],
                         cwd=project, env=env, capture_output=True, text=True, timeout=180)
    (out / "finite-replay.log").write_text(run.stdout + run.stderr)
    require(run.returncode == 0, "Frozen full finite source replay failed")
    comparisons = []
    for case in ("native_race", "native_fixed"):
        old = json.loads((finite / (case + ".json")).read_text())
        new = json.loads((out / "finite-replay" / (case + ".json")).read_text())
        for key in ("case", "instructions", "accesses", "counts", "footprint_classification_failures",
                    "all_threads_halted", "final_block_epoch", "missing_output_cells", "first_conflict",
                    "canonical_witness", "source_sha256"):
            require(old[key] == new[key], "Finite trace record differs: " + case + ":" + key)
        digest = trace_sha(finite / old["trace_file"])
        require(trace_sha(out / "finite-replay" / new["trace_file"]) == digest, "Complete finite trace differs")
        comparisons.append({"case": case, "accesses": new["accesses"], "trace_content_sha256": digest})
    checks.append({"name": "full-finite-source-replay", "accepted": True, "expected_accepted": True,
                   "exit_code": run.returncode, "seconds": time.monotonic() - before, "timed_out": False})
    result = {
        "schema": 1, "status": "frozen-softmax-whole-grid-and-finite-traces-replayed", "stage": "whole-grid",
        "source_archive_sha256": sha(packet / "source.tar.gz"), "packet_manifest_sha256": sha(packet / "manifest.json"),
        "local_lean_modules": report["local_lean_modules"], "axiom_audits": len(report["axiom_audits"]),
        "false_lean_claims_rejected": report["false_lean_claims_rejected"], "checks": checks,
        "git_available_on_path": False, "own_lean_compiled_cache_seeded": False,
        "complete_finite_traces_compared": comparisons,
        "actual_first_block_wave_fold_execution_proved": True, "starts_at_actual_initializer": True,
        "maximum_parked_pc": 42, "maximum_resumed_pc": 43, "maximum_block_epoch": 2,
        "accesses_per_maximum_pass": 57409, "input_reads_per_maximum_pass": 57344, "shared_writes_per_maximum_pass": 33, "shared_reads_per_maximum_pass": 32,
        "first_barrier_resume_proved": True, "second_barrier_resume_proved": True,
        "actual_serial_block_wave_fold_execution_proved": True, "all32_serial_partial_reads_proved": True,
        "maximum_pass_race_freedom_proved": True, "checksum_row_maximum_actual_fold_value_proved": True,
        "checksum_row_maximum": 133254668662643834119504341449835759241818635200, "block_scheduler_decomposition_proved": True,
        "remaining_block_fuel_after_maximum": 3, "first_block_race_freedom_proved": True, "source_certificates": 0, "whole_kernel_execution_proved": True,
        "conflict_witness_state_reachability_proved": False, "actual_trace_universal_classification_proved": False,
        "canonical_source_equivalence_proved": False, "ieee_equivalence_proved": False,
        "original_paper_fully_reproduced": False, "model_calls": 0, "gpu_trials": 0,
    }
    result.update({name:report[name] for name in ('actual_exp_scalar_lane_prefix_execution_proved', 'exp_starts_at_proved_maximum_state', 'exp_parked_pc', 'exp_block_epoch', 'exp_outer_rounds', 'exp_components_per_round', 'exp_lane_costs', 'exp_lane_access_increments', 'exp_valid_stores_per_lane', 'exp_converted_outputs_proved', 'exp_unrounded_source_ordered_sum_proved', 'exp_prefix_race_freedom_proved', 'exp_native_indices_preserved_proved', 'exp_word_model', 'exp_word_maximum', 'exp_word_cases', 'exp_word_actual_sum_and_output_values_proved', 'actual_exp_wave_fold_execution_proved', 'actual_exp_block_phase_execution_proved')})
    result.update({name:report[name] for name in (
        "exp_wave_parked_pc", "exp_wave_block_epoch", "exp_wave_logical_partials", "exp_wave_sum_stages",
        "exp_wave_shuffle_kind", "exp_wave_logical_width", "exp_wave_source_ordered_sum_proved",
        "exp_wave_snapshot_transport_proved", "exp_wave_partial_values_proved", "exp_wave_race_freedom_proved",
        "third_barrier_resume_proved", "serial_sum_execution_proved", "exp_wave_word_cases",
        "exp_wave_word_actual_partial_values_proved")})
    result.update({name:report[name] for name in ('actual_reduction_prefix_some_execution_proved', 'reduction_prefix_linked_to_runBlock', 'fourth_barrier_resume_proved', 'reduction_phases', 'reduction_parked_pc', 'reduction_resumed_pc', 'reduction_block_epoch', 'remaining_block_fuel_after_sum', 'accesses_per_exp_block_phase', 'accesses_after_third_barrier', 'shared_reads_per_serial_sum_phase', 'shared_writes_per_serial_sum_phase', 'accesses_after_fourth_barrier', 'all32_exp_partial_values_proved', 'all32_serial_sum_partial_reads_proved', 'source_ordered_row_sum_proved', 'all_exponential_output_values_preserved_proved', 'reduction_prefix_race_freedom_proved', 'reduction_projection_model', 'reduction_projection_values', 'reduction_projection_actual_full_prefix_values_proved', 'serial_checksum_model', 'serial_checksum', 'serial_checksum_isolated_actual_phase_proved', 'serial_checksum_scope', 'normalization_execution_proved')})
    result.update({name:report[name] for name in ('actual_whole_block_some_execution_proved', 'all_five_source_block_phases_proved', 'whole_block_source_ordered_outputs_proved', 'whole_block_source_initializer_bound', 'repaired_whole_block_trace_classification_proved', 'repaired_whole_block_race_freedom_proved', 'original_whole_block_race_freedom_proved', 'whole_grid_execution_proved', 'normalization_outer_rounds', 'normalization_components_per_round', 'whole_block_epoch', 'whole_block_halt_pc', 'normalization_lane_costs', 'normalization_lane_accesses', 'normalization_block_accesses', 'whole_block_accesses', 'whole_block_word', 'whole_block_actual_converted_output_values_proved')})
    result.update({name:report[name] for name in ('whole_grid_variants', 'original_whole_grid_execution_proved', 'repaired_whole_grid_some_execution_proved', 'repaired_whole_grid_race_freedom_proved', 'repaired_whole_grid_trace_classification_proved', 'repaired_whole_grid_all_outputs_proved', 'repaired_whole_grid_extract_proved', 'repaired_whole_grid_source_order_correct_proved', 'whole_grid_source_initializer_bound', 'foreign_block_control_and_memory_frames_proved', 'grid_halt_pc', 'grid_block_epoch', 'grid_accesses_per_row', 'grid_output_cells_per_row', 'grid_all_supported_rows_proved', 'inherited_block_controls_previously_rejected', 'inherited_block_evidence', 'scope')})
    (out / "results.json").write_text(json.dumps(result, indent=2) + "\n")
    shutil.copyfile(Path(__file__), out / "replay.py")
    (out / "manifest.json").write_text(json.dumps({p.name: sha(p) for p in sorted(out.iterdir()) if p.is_file()}, indent=2) + "\n")
    print(json.dumps({"status": result["status"], "modules": result["local_lean_modules"],
                      "audits": result["axiom_audits"], "rejections": result["false_lean_claims_rejected"]}))


if __name__ == "__main__":
    main()
