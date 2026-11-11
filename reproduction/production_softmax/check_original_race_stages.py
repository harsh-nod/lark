"""Reject rehashed original-race claims before archive extraction."""

import argparse
import copy
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
    current = json.loads((args.packet / "results.json").read_text())
    missing = "Missing actual original conflict or one-row counterexample claims"
    witness = "Wrong actual original witness or counterexample scope"
    principal = "Principal original-race audits absent"
    scenarios = [
        ("invented-certificate", {"source_certificates": 1}, "Invented source certificate"),
        ("boolean-certificate", {"source_certificates": False}, "Invented source certificate"),
        ("invented-original-race-freedom", {"original_whole_block_race_freedom_proved": True}, "Invented original-source grid or race-freedom claim"),
        ("invented-original-multirow-grid", {"original_whole_grid_execution_proved": True}, "Invented original-source grid or race-freedom claim"),
        ("invented-canonical-reference", {"canonical_source_equivalence_proved": True}, "Invented whole-source/reference claim"),
        ("invented-ieee-equivalence", {"ieee_equivalence_proved": True}, "Invented whole-source/reference claim"),
        ("invented-paper-completion", {"original_paper_fully_reproduced": True}, "Invented whole-source/reference claim"),
        ("assumed-race-freedom", {"race_freedom_assumed": True}, "Invented whole-source/reference claim"),
        ("omitted-original-refusal", {}, "Wrong original-race replay checks"),
        ("earlier-grid-relabeled-race", {}, principal),
        ("earlier-real-relabeled-race", {}, principal),
        ("synthetic-state-reachability", {"witness_reachability_scope": "The synthetic whole instruction states are reached verbatim"}, witness),
        ("wrong-inherited-grid-refusals", {"inherited_grid_controls_previously_rejected": 129}, witness),
        ("boolean-inherited-grid-refusals", {"inherited_grid_controls_previously_rejected": True}, witness),
        ("wrong-proof-closure", {"local_lean_modules": 125}, "Wrong whole-grid proof closure or original fuel"),
        ("boolean-proof-closure", {"local_lean_modules": True}, "Wrong whole-grid proof closure or original fuel"),
    ]
    claims = (
        "conflict_witness_state_reachability_proved", "original_conflicting_accesses_in_reached_block_trace_proved",
        "original_complete_block_race_proved", "original_racy_block_some_execution_proved",
        "original_single_row_launch_some_execution_proved", "original_single_row_launch_race_proved",
        "original_single_row_not_correct_for_any_reference_proved", "original_exact_instruction_witness_accesses_reached_proved",
    )
    scenarios += [("omitted-" + key, {key: False}, missing) for key in claims]
    scenarios += [("integer-race-reachability", {"conflict_witness_state_reachability_proved": 1}, missing)]
    for field, key, wrong in (
        ("original_reader", "tid", 1), ("original_reader", "iteration", 5), ("original_reader", "component", 1),
        ("original_reader", "unclamped_column", 50256), ("original_reader", "column", 50255),
        ("original_reader", "write", True), ("original_writer", "tid", 81),
        ("original_writer", "column", 50255), ("original_writer", "write", False),
        ("original_conflict_epoch", "grid", 1), ("original_conflict_epoch", "block", 5),
        ("original_conflict_epoch", "warp", 1), ("original_reader", "tid", False),
    ):
        changed = copy.deepcopy(current[field])
        changed[key] = wrong
        prefix = "boolean" if field == "original_reader" and key == "tid" and type(wrong) is bool else "wrong"
        scenarios.append((prefix + "-" + field + "-" + key, {field: changed}, witness))
    audited = (
        "source_original_racy_block", "source_original_reader_member", "source_original_writer_member",
        "source_original_single_row_launch", "source_original_single_row_not_correct", "source_original_exact_witness_members",
        "LarkNativeSoftmax.initial_original_block_race_free_false", "LarkNativeSoftmax.initial_sum_full_epoch",
        "LarkNativeSoftmax.norm_block_original_member", "LarkNativeSoftmax.original_single_row_not_correct",
    )
    scenarios += [("omitted-audit-" + name.replace(".", "-"), {}, principal) for name in audited]
    records = []
    for name, changes, reason in scenarios:
        original = (args.earlier_packet if name == "earlier-grid-relabeled-race" else
                    HERE / "results/canonical-real-v1" if name == "earlier-real-relabeled-race" else args.packet)
        folder = out / name
        packet = folder / "packet"
        packet.mkdir(parents=True)
        manifest = json.loads((original / "manifest.json").read_text())
        for filename, digest in manifest.items():
            if Path(filename).name != filename or sha(original / filename) != digest:
                raise ValueError("Original packet hash/path differs")
            shutil.copyfile(original / filename, packet / filename)
        report = json.loads((packet / "results.json").read_text())
        if name.startswith("earlier-"):
            old_audits, old_archive = report["axiom_audits"], report["source_archive_sha256"]
            report = copy.deepcopy(current)
            report["axiom_audits"], report["source_archive_sha256"] = old_audits, old_archive
        report.update(changes)
        if name == "omitted-original-refusal":
            report["checks"] = [c for c in report["checks"] if c["name"] != "denied-original-reader"]
        if name.startswith("omitted-audit-"):
            key = next(k for k in audited if name == "omitted-audit-" + k.replace(".", "-"))
            del report["axiom_audits"][key]
        (packet / "results.json").write_text(json.dumps(report, indent=2) + "\n")
        (packet / "manifest.json").write_text(json.dumps({p.name: sha(p) for p in sorted(packet.iterdir())
                                                          if p.name != "manifest.json"}, indent=2) + "\n")
        target = folder / "attempted-replay"
        command = [sys.executable, str(HERE / "replay_original_race.py"), "--packet", str(packet),
                   "--finite-trace-packet", str(HERE / "results/finite-trace-v2"), "--output", str(target),
                   "--lean-bin", str(args.lean_bin)]
        run = subprocess.run(command, capture_output=True, text=True, timeout=30)
        log = run.stdout + run.stderr
        (out / (name + ".log")).write_text(log)
        if run.returncode == 0 or reason not in log or target.exists():
            raise ValueError("Wrong original race stage rejection: " + name + "\n" + log)
        records.append({"name": name, "exit_code": run.returncode, "expected_reason": reason,
                        "packet_rehashed": True, "rejected_before_extraction": True})
    report = {
        "schema": 1, "status": "fully-rehashed-false-original-race-stage-claims-rejected-before-extraction",
        "checks": records, "race_packet_manifest_sha256": sha(args.packet / "manifest.json"),
        "earlier_packet_manifest_sha256": sha(args.earlier_packet / "manifest.json"),
        "replayer_sha256": sha(HERE / "replay_original_race.py"), "source_certificates": 0,
        "original_paper_fully_reproduced": False,
    }
    (out / "results.json").write_text(json.dumps(report, indent=2) + "\n")
    shutil.copyfile(Path(__file__), out / "checker.py")
    (out / "manifest.json").write_text(json.dumps({p.name: sha(p) for p in sorted(out.iterdir()) if p.is_file()}, indent=2) + "\n")
    print(json.dumps({"status": report["status"], "checks": len(records)}))


if __name__ == "__main__":
    main()
