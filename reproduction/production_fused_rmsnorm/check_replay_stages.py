"""Reject relabeled or incomplete whole-launch reports before archive extraction."""

import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--lean-bin", type=Path, required=True)
    args = parser.parse_args()
    out, lean_bin = args.output.resolve(), args.lean_bin.resolve()
    if any((p / ".git").exists() for p in (out, *out.parents)):
        raise ValueError("Control output must be outside Git")
    out.mkdir(parents=True, exist_ok=False)
    checks = []
    for name, packet in (("relabeled-earlier-stage", "output-lane-v1"),
                         ("missing-extraction-audit", "whole-launch-v1")):
        original = HERE / "results" / packet
        case = out / "inputs" / name
        shutil.copytree(original, case)
        report = json.loads((case / "results.json").read_text())
        if name == "relabeled-earlier-stage":
            report.update({
                "status": "native-inout-whole-launch-checked",
                "whole_kernel_execution_proved": True, "actual_trace_classification_proved": True,
                "whole_launch_race_freedom_proved": True,
                "whole_launch_source_ordered_correctness_proved": True,
                "whole_launch_seeded_inout_relation_proved": True,
                "whole_launch_both_output_buffers_extracted": True,
            })
        else:
            del report["axiom_audits"]["source_whole_launch_extraction"]
        (case / "results.json").write_text(json.dumps(report, indent=2) + "\n")
        manifest = json.loads((case / "manifest.json").read_text())
        manifest["results.json"] = sha(case / "results.json")
        (case / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
        rejected = out / ("must-not-exist-" + name)
        command = [sys.executable, str(HERE / "replay_prefix.py"), "--packet", str(case),
                   "--output", str(rejected), "--lean-bin", str(lean_bin)]
        start = time.monotonic()
        run = subprocess.run(command, capture_output=True, text=True, timeout=30)
        log = run.stdout + run.stderr
        (out / (name + ".log")).write_text(log)
        if run.returncode == 0 or "Whole-launch theorem audits absent" not in log or rejected.exists():
            raise ValueError(name + ": wrong rejection gate\n" + log)
        checks.append({"name": name, "earlier_packet": packet,
                       "earlier_packet_manifest_sha256": sha(original / "manifest.json"),
                       "input_manifest_rehashed": True, "exit_code": run.returncode,
                       "seconds": time.monotonic() - start,
                       "rejected_before_extraction_or_build": True,
                       "gate": "Whole-launch theorem audits absent"})
    result = {
        "schema": 1, "status": "whole-launch-stage-claim-guards-checked", "checks": checks,
        "replayer_sha256": sha(HERE / "replay_prefix.py"),
        "scope": "Two report controls with recomputed manifest hashes reject before extraction/build: an earlier-stage packet relabeled as whole-launch, and a whole-launch packet missing the extraction theorem audit. Positive source checking and archive replay are separate. Inputs are reconstructed from the named frozen packets.",
        "source_certificates": 0, "canonical_source_equivalence_proved": False,
        "original_paper_fully_reproduced": False, "model_calls": 0, "gpu_trials": 0,
    }
    (out / "results.json").write_text(json.dumps(result, indent=2) + "\n")
    shutil.copyfile(Path(__file__), out / "checker.py")
    (out / "manifest.json").write_text(json.dumps({p.name: sha(p) for p in sorted(out.iterdir())
                                                 if p.is_file()}, indent=2) + "\n")
    print(json.dumps({"status": result["status"], "controls": len(checks)}), flush=True)


if __name__ == "__main__":
    main()
