"""Reject rehashed complete-RoPE scope changes before source extraction."""

import argparse
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

from replay_whole import sha, validate_metadata


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--packet", type=Path, required=True)
    parser.add_argument("--earlier-packet", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--lean-bin", type=Path, required=True)
    args = parser.parse_args()
    validate_metadata(json.loads((args.packet / "results.json").read_text()))
    args.output.mkdir(parents=True, exist_ok=False)
    changes = {
        "missing-certificate": lambda r: r.update(source_certificates=7),
        "boolean-certificate-count": lambda r: r.update(source_certificates=True),
        "missing-whole-launch": lambda r: r.update(whole_kernel_execution_proved=False),
        "missing-actual-trace": lambda r: r.update(actual_trace_race_freedom_proved=False),
        "missing-key-extraction": lambda r: r.update(both_output_buffers_extracted=False),
        "invented-ieee-equivalence": lambda r: r.update(ieee_equivalence_proved=True),
        "invented-paper-completion": lambda r: r.update(original_paper_fully_reproduced=True),
        "unknown-proof-claim": lambda r: r.update(canonical_real_reference_proved=True),
        "missing-principal-audit": lambda r: r["library_axiom_audits"].pop("LarkNativeRope.correct"),
        "invented-extra-axiom": lambda r: r["library_axiom_audits"].update({"LarkNativeRope.correct": "sorryAx"}),
        "false-claim-accepted": lambda r: r["checks"][16].update(accepted=True, expected_accepted=True),
        "timed-out-positive": lambda r: r["checks"][0].update(timed_out=True),
        "promoted-component-packet": lambda r: r.update(
            status="native-rope-source-bound-whole-launch-checked", model_profile="native-rope-whole-v19",
            whole_kernel_execution_proved=True, actual_trace_race_freedom_proved=True,
            source_reference_equality_proved=True, source_certificates=8),
    }
    checks = []
    with tempfile.TemporaryDirectory(prefix="lark-rope-whole-stage-guards-") as temporary:
        base = Path(temporary)
        for name, change in changes.items():
            original = args.earlier_packet if name == "promoted-component-packet" else args.packet
            packet, output = base / name, base / (name + "-replay")
            shutil.copytree(original, packet, ignore=shutil.ignore_patterns("source"))
            report = json.loads((packet / "results.json").read_text())
            change(report)
            (packet / "results.json").write_text(json.dumps(report, indent=2) + "\n")
            manifest = json.loads((packet / "manifest.json").read_text())
            manifest["results.json"] = sha(packet / "results.json")
            (packet / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
            run = subprocess.run([sys.executable, str(Path(__file__).with_name("replay_whole.py")),
                                  "--packet", str(packet), "--output", str(output),
                                  "--lean-bin", str(args.lean_bin)], capture_output=True, text=True, timeout=30)
            log = run.stdout + run.stderr
            (args.output / (name + ".log")).write_text(log)
            if run.returncode == 0 or output.exists() or "Unsupported native RoPE whole-launch" not in log:
                raise ValueError("Wrong whole-launch scope-guard outcome: " + name)
            checks.append({"name": name, "accepted": False, "fully_rehashed": True, "rejected_before_extraction": True})
    report = {"schema": 1, "status": "rehashed-native-rope-whole-launch-stage-claims-rejected-before-extraction",
              "checks": checks, "negative_controls": len(checks), "model_calls": 0, "gpu_trials": 0,
              "original_paper_fully_reproduced": False, "source_packet_manifest_sha256": sha(args.packet / "manifest.json"),
              "earlier_packet_manifest_sha256": sha(args.earlier_packet / "manifest.json"),
              "replayer_sha256": sha(Path(__file__).with_name("replay_whole.py")), "checker_sha256": sha(Path(__file__))}
    (args.output / "results.json").write_text(json.dumps(report, indent=2) + "\n")
    (args.output / "manifest.json").write_text(json.dumps({p.name: sha(p) for p in sorted(args.output.iterdir())}, indent=2) + "\n")
    print(json.dumps({"status": report["status"], "negative_controls": len(checks)}))


if __name__ == "__main__":
    main()
