"""Reject rehashed SGLang whole-launch overclaims before source extraction."""

import argparse
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

from replay_native_real import sha


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--packet", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--lean-bin", type=Path, required=True)
    parser.add_argument("--dependency-project", type=Path, required=True)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    records = []
    mutations = {
        "invented-ieee-proof": ("ieee_equivalence_proved", True),
        "invented-error-bound": ("floating_point_error_bound_proved", True),
        "invented-paper-completion": ("original_paper_fully_reproduced", True),
        "invented-unguarded-proof": ("unguarded_correctness_proved", True),
        "unknown-report-field": ("unsupported_extra_field", False),
        "boolean-schema": ("schema", True),
        "boolean-module-count": ("local_lean_modules", True),
        "wrong-module-count": ("local_lean_modules", 87),
        "wrong-real-module-count": ("local_real_modules", 3),
        "boolean-certificate-count": ("source_certificates", True),
        "wrong-certificate-count": ("source_certificates", 3),
        "wrong-export-rows": ("export_rows", [1, 3, 64]),
        "boolean-export-row": ("export_rows", [True, 3, 64, 131072]),
        "boolean-row-bound": ("rows", {"min": True, "max": 131072}),
        "wrong-row-bound": ("rows", {"min": 1, "max": 262144}),
        "wrong-source-hash": ("source_sha256", "0"*64),
        "wrong-model-profile": ("model_profile", "native-sglang-rmsnorm-real-v22"),
        "wrong-block-size": ("block", 512),
        "wrong-physical-wave": ("physical_warp", 32),
        "wrong-logical-warp": ("logical_warp", 64),
        "missing-parameterized-certificate": ("parameterized_source_certificate", False),
        "missing-whole-launch": ("whole_kernel_execution_proved", False),
        "missing-actual-race-freedom": ("actual_trace_race_freedom_proved", False),
        "missing-source-reference": ("source_reference_equality_proved", False),
        "wrong-false-lean-count": ("false_lean_claims_rejected", 17),
        "wrong-refusal-count": ("false_claims_rejected", 39),
        "boolean-model-calls": ("model_calls", False),
        "invented-gpu-trials": ("gpu_trials", 1),
        "missing-library-audits": ("library_axiom_audits", {}),
        "missing-main-audits": ("main_axiom_audits", {}),
        "missing-export-audits": ("export_axiom_audits", {}),
        "missing-control-receipts": ("checks", []),
    }
    with tempfile.TemporaryDirectory(prefix="lark-sglang-real-stage-guards-") as temporary:
        base = Path(temporary)
        for name, (key, value) in mutations.items():
            packet, output = base / name, base / (name + "-replay")
            # Only top-level manifest-bound files are needed for this gate;
            # proof/certificate trees are deliberately not copied or executed.
            packet.mkdir()
            for path in args.packet.iterdir():
                if path.is_file():
                    shutil.copyfile(path, packet / path.name)
            report = json.loads((packet / "results.json").read_text())
            report[key] = value
            (packet / "results.json").write_text(json.dumps(report, indent=2) + "\n")
            manifest = json.loads((packet / "manifest.json").read_text())
            manifest["results.json"] = sha(packet / "results.json")
            (packet / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
            run = subprocess.run([sys.executable, str(Path(__file__).with_name("replay_native_real.py")),
                                  "--packet", str(packet), "--output", str(output),
                                  "--lean-bin", str(args.lean_bin), "--dependency-project", str(args.dependency_project)],
                                 capture_output=True, text=True, timeout=30)
            log = run.stdout + run.stderr
            (args.output / (name + ".log")).write_text(log)
            if run.returncode == 0 or output.exists() or "Unsupported SGLang RMSNorm real stage/scope metadata" not in log:
                raise ValueError("Wrong scope-guard outcome: " + name)
            records.append({"name": name, "accepted": False, "fully_rehashed": True, "rejected_before_extraction": True})
    result = {"schema": 1, "status": "fully-rehashed-native-sglang-real-claims-rejected-before-extraction",
              "checks": records, "negative_controls": len(records), "model_calls": 0, "gpu_trials": 0,
              "original_paper_fully_reproduced": False, "source_packet_manifest_sha256": sha(args.packet / "manifest.json"),
              "replayer_sha256": sha(Path(__file__).with_name("replay_native_real.py")), "checker_sha256": sha(Path(__file__))}
    (args.output / "results.json").write_text(json.dumps(result, indent=2) + "\n")
    (args.output / "manifest.json").write_text(json.dumps({p.name: sha(p) for p in sorted(args.output.iterdir())}, indent=2) + "\n")
    print(json.dumps({"status": result["status"], "negative_controls": len(records)}))


if __name__ == "__main__":
    main()
