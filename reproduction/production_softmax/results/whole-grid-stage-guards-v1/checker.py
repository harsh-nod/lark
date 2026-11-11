"""Reject fully rehashed false grid claims before archive extraction."""

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
    missing = "Missing repaired whole-grid execution/value/race claims"
    counts = "Wrong repaired whole-grid endpoint/counts/scope"
    principal = "Principal whole-grid audits absent"
    scenarios = [
        ("invented-certificate", {"source_certificates": 1}, "Invented source certificate"),
        ("boolean-certificate", {"source_certificates": False}, "Invented source certificate"),
        ("invented-original-grid", {"original_whole_grid_execution_proved": True}, "Invented original-source grid or race-freedom claim"),
        ("invented-original-race-freedom", {"original_whole_block_race_freedom_proved": True}, "Invented original-source grid or race-freedom claim"),
        ("invented-canonical-reference", {"canonical_source_equivalence_proved": True}, "Invented whole-source/reference claim"),
        ("invented-ieee-equivalence", {"ieee_equivalence_proved": True}, "Invented whole-source/reference claim"),
        ("invented-paper-completion", {"original_paper_fully_reproduced": True}, "Invented whole-source/reference claim"),
        ("assumed-race-freedom", {"race_freedom_assumed": True}, "Invented whole-source/reference claim"),
        ("both-grid-variants", {"whole_grid_variants": ["original", "fixed"]}, counts),
        ("canonical-interpretation", {"scope": "Canonical IEEE softmax"}, "Wrong repaired whole-grid interpretation"),
        ("double-counted-inherited-controls", {"inherited_block_evidence": "All old controls rerun here"}, "Wrong repaired whole-grid interpretation"),
        ("wrong-proof-closure", {"local_lean_modules": 124}, "Wrong whole-grid proof closure or original fuel"),
        ("boolean-proof-closure", {"local_lean_modules": True}, "Wrong whole-grid proof closure or original fuel"),
        ("omitted-grid-refusal", {}, "Wrong whole-grid replay checks"),
        ("earlier-block-relabeled", {}, principal),
    ]
    claims = (
        "whole_kernel_execution_proved", "whole_grid_execution_proved",
        "repaired_whole_grid_some_execution_proved", "repaired_whole_grid_race_freedom_proved",
        "repaired_whole_grid_trace_classification_proved", "repaired_whole_grid_all_outputs_proved",
        "repaired_whole_grid_extract_proved", "repaired_whole_grid_source_order_correct_proved",
        "whole_grid_source_initializer_bound", "foreign_block_control_and_memory_frames_proved",
        "grid_all_supported_rows_proved",
    )
    scenarios += [("omitted-" + key, {key: False}, missing) for key in claims]
    scenarios += [("integer-grid-completion", {"whole_grid_execution_proved": 1}, missing)]
    for key in ("grid_halt_pc", "grid_block_epoch", "grid_accesses_per_row", "grid_output_cells_per_row",
                "inherited_block_controls_previously_rejected"):
        scenarios += [("wrong-" + key, {key: current[key] + 1}, counts),
                      ("boolean-" + key, {key: True}, counts)]
    audited = (
        "source_fixed_grid_launch", "source_fixed_grid_correct", "source_fixed_grid_extract",
        "source_fixed_grid_rf", "LarkNativeSoftmax.whole_block_fixed_entry_other",
        "LarkNativeSoftmax.source_order_correct", "LarkNativeSoftmax.fixed_block_fold_output_member",
    )
    scenarios += [("omitted-audit-" + name.rsplit(".", 1)[-1], {}, principal) for name in audited]
    records = []
    for name, changes, reason in scenarios:
        original = args.earlier_packet if name == "earlier-block-relabeled" else args.packet
        folder = out / name
        packet = folder / "packet"
        packet.mkdir(parents=True)
        manifest = json.loads((original / "manifest.json").read_text())
        for filename, digest in manifest.items():
            if Path(filename).name != filename or sha(original / filename) != digest:
                raise ValueError("Original packet hash/path differs")
            shutil.copyfile(original / filename, packet / filename)
        report = json.loads((packet / "results.json").read_text())
        if name == "earlier-block-relabeled":
            # Spoof every new report field, preserving the old block proof
            # audits and old source archive. Required grid audits still fail.
            old_audits = report["axiom_audits"]
            old_archive = report["source_archive_sha256"]
            report = copy.deepcopy(current)
            report["axiom_audits"] = old_audits
            report["source_archive_sha256"] = old_archive
        report.update(changes)
        if name == "omitted-grid-refusal":
            report["checks"] = [c for c in report["checks"] if c["name"] != "missing-grid-output"]
        if name.startswith("omitted-audit-"):
            key = next(k for k in audited if name == "omitted-audit-" + k.rsplit(".", 1)[-1])
            del report["axiom_audits"][key]
        (packet / "results.json").write_text(json.dumps(report, indent=2) + "\n")
        (packet / "manifest.json").write_text(json.dumps({p.name: sha(p) for p in sorted(packet.iterdir())
                                                          if p.name != "manifest.json"}, indent=2) + "\n")
        target = folder / "attempted-replay"
        command = [sys.executable, str(HERE / "replay_whole_grid.py"), "--packet", str(packet),
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
        "schema": 1, "status": "fully-rehashed-false-whole-grid-stage-claims-rejected-before-extraction",
        "checks": records, "grid_packet_manifest_sha256": sha(args.packet / "manifest.json"),
        "earlier_packet_manifest_sha256": sha(args.earlier_packet / "manifest.json"),
        "replayer_sha256": sha(HERE / "replay_whole_grid.py"), "source_certificates": 0,
        "original_paper_fully_reproduced": False,
    }
    (out / "results.json").write_text(json.dumps(report, indent=2) + "\n")
    shutil.copyfile(Path(__file__), out / "checker.py")
    (out / "manifest.json").write_text(json.dumps({p.name: sha(p) for p in sorted(out.iterdir()) if p.is_file()}, indent=2) + "\n")
    print(json.dumps({"status": report["status"], "checks": len(records)}))


if __name__ == "__main__":
    main()
