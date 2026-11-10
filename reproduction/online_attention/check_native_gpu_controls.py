"""Reject rehashed proof/completion claims and nonfinite native outputs."""

import argparse
import json
from pathlib import Path
import shutil
import struct

from audit_native_gpu import check
from audit_gpu import require, sha


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", required=True, type=Path)
    parser.add_argument("--host", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    data, host, out = args.input.resolve(), args.host.resolve(), args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    check(data, [host])
    records = []
    for name, expected in (("original-completion-claim", "Unsupported formal or original-paper claim"),
                           ("source-certificate-claim", "Unsupported formal or original-paper claim"),
                           ("nonfinite-native-output", "Numerical tolerance failure: adapted")):
        changed = out / name
        shutil.copytree(host, changed)
        if name == "nonfinite-native-output":
            path = changed / "adapted.bin"
            payload = bytearray(path.read_bytes())
            payload[:2] = struct.pack("<H", 0x7e00)
            path.write_bytes(payload)
        else:
            path = changed / "results.json"
            report = json.loads(path.read_text())
            if name == "original-completion-claim":
                report["original_paper_fully_reproduced"] = True
            else:
                report["source_certificates"] = 1
                report["whole_kernel_execution_proved"] = True
                report["actual_trace_classification_proved"] = True
            path.write_text(json.dumps(report, indent=2) + "\n")
        files = json.loads((changed / "manifest.json").read_text())
        files[path.name] = sha(path)
        (changed / "manifest.json").write_text(json.dumps(files, indent=2) + "\n")
        try:
            check(data, [changed])
        except ValueError as error:
            require(str(error) == expected, "Unexpected rejection: " + str(error))
            records.append({"name": name, "rejected": True, "message": str(error),
                            "fully_rehashed": True, "manifest_sha256": sha(changed / "manifest.json")})
        else:
            raise ValueError("False evidence accepted: " + name)
    report = {"status": "passed", "positive_replays": 1, "negative_controls": records,
              "input_manifest_sha256": sha(data / "manifest.json"),
              "host_manifest_sha256": sha(host / "manifest.json"),
              "auditor_sha256": sha(Path(__file__).with_name("audit_native_gpu.py")),
              "shared_audit_helpers_sha256": sha(Path(__file__).with_name("audit_gpu.py")),
              "control_runner_sha256": sha(Path(__file__)),
              "fresh_lean_checks": 0, "fresh_gpu_trials": 0, "model_calls": 0}
    (out / "results.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report))


if __name__ == "__main__":
    main()
