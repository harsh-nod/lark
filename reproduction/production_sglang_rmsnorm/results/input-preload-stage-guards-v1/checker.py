"""Reject fully rehashed overclaims before SGLang RMSNorm prefix source extraction."""

import argparse
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

from replay_input_preloads import sha


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--packet", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--lean-bin", type=Path, required=True)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    records = []
    mutations = {
        "invented-partial-store-reachability": ("initializer_reaches_partial_store_cut_proved", True),
        "invented-lane-success": ("continued_lane_success_proved", True),
        "invented-whole-launch": ("whole_kernel_execution_proved", True),
        "invented-whole-trace": ("actual_whole_trace_classification_proved", True),
        "invented-reference": ("source_reference_equality_proved", True),
        "invented-certificate": ("source_certificates", 1),
        "boolean-certificate": ("source_certificates", False),
        "boolean-module-count": ("local_lean_modules", True),
        "invented-paper-completion": ("original_paper_fully_reproduced", True),
        "missing-source-binding": ("full_source_binding_proved", False),
        "missing-cache-values": ("private_cache_values_and_readonly_globals_proved", False),
        "invented-weight-preload-count": ("prefix_instruction_count", 236),
        "invented-weight-preload-pc": ("prefix_exit_pc", 27),
        "missing-private-store-events": ("prefix_access_events", 16),
        "unknown-proof-claim": ("canonical_real_reference_proved", True),
    }
    with tempfile.TemporaryDirectory(prefix="lark-sglang-rmsnorm-stage-guards-") as temporary:
        base = Path(temporary)
        for name, (key, value) in mutations.items():
            packet, output = base / name, base / (name + "-replay")
            shutil.copytree(args.packet, packet, ignore=shutil.ignore_patterns("source"))
            report = json.loads((packet / "results.json").read_text())
            report[key] = value
            (packet / "results.json").write_text(json.dumps(report, indent=2) + "\n")
            manifest = json.loads((packet / "manifest.json").read_text())
            manifest["results.json"] = sha(packet / "results.json")
            (packet / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
            run = subprocess.run([sys.executable, str(Path(__file__).with_name("replay_input_preloads.py")),
                                  "--packet", str(packet), "--output", str(output),
                                  "--lean-bin", str(args.lean_bin)], capture_output=True, text=True, timeout=30)
            log = run.stdout + run.stderr
            (args.output / (name + ".log")).write_text(log)
            if run.returncode == 0 or output.exists() or "Unsupported SGLang RMSNorm input-preload prefix stage/scope metadata" not in log:
                raise ValueError("Wrong scope-guard outcome: " + name)
            records.append({"name": name, "accepted": False, "fully_rehashed": True, "rejected_before_extraction": True})
    result = {"schema": 1, "status": "fully-rehashed-native-sglang-input-preload-prefix-claims-rejected-before-extraction",
              "checks": records, "negative_controls": len(records), "model_calls": 0, "gpu_trials": 0,
              "original_paper_fully_reproduced": False, "source_packet_manifest_sha256": sha(args.packet / "manifest.json"),
              "replayer_sha256": sha(Path(__file__).with_name("replay_input_preloads.py")), "checker_sha256": sha(Path(__file__))}
    (args.output / "results.json").write_text(json.dumps(result, indent=2) + "\n")
    (args.output / "manifest.json").write_text(json.dumps({p.name: sha(p) for p in sorted(args.output.iterdir())}, indent=2) + "\n")
    print(json.dumps({"status": result["status"], "negative_controls": len(records)}))


if __name__ == "__main__":
    main()
