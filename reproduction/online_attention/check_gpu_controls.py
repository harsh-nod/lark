"""Check that rehashed false claims and nonfinite outputs cannot pass the audit."""

import argparse
import json
from pathlib import Path
import shutil
import struct

from audit_gpu import check, require, sha


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", required=True, type=Path)
    parser.add_argument("--host", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    data, host, out = args.input.resolve(), args.host.resolve(), args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    check(data, [host])
    controls = []
    for name, message in (("original-completion-claim", "Unsupported formal or original-paper claim"),
                          ("nonfinite-output", "Numerical tolerance failure")):
        changed = out / name
        shutil.copytree(host, changed)
        if name == "original-completion-claim":
            path = changed / "results.json"
            report = json.loads(path.read_text())
            report["original_paper_fully_reproduced"] = True
            path.write_text(json.dumps(report, indent=2) + "\n")
        else:
            path = changed / "outputs.bin"
            raw = bytearray(path.read_bytes())
            raw[:4] = struct.pack("<f", float("nan"))
            path.write_bytes(raw)
        hashes = json.loads((changed / "manifest.json").read_text())
        hashes[path.name] = sha(path)
        (changed / "manifest.json").write_text(json.dumps(hashes, indent=2) + "\n")
        try:
            check(data, [changed])
        except ValueError as error:
            require(str(error) == message, "Unexpected rejection channel: " + str(error))
            controls.append({"name": name, "rejected": True, "message": str(error),
                             "fully_rehashed": True, "manifest_sha256": sha(changed / "manifest.json")})
        else:
            raise ValueError("False evidence accepted: " + name)
    result = {
        "status": "passed", "positive_audits": 1, "negative_controls": controls,
        "input_manifest_sha256": sha(data / "manifest.json"),
        "host_manifest_sha256": sha(host / "manifest.json"),
        "auditor_sha256": sha(Path(__file__).with_name("audit_gpu.py")),
        "control_runner_sha256": sha(Path(__file__)),
        "fresh_lean_checks": 0, "fresh_gpu_trials": 0, "model_calls": 0,
    }
    (out / "results.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result))


if __name__ == "__main__":
    main()
