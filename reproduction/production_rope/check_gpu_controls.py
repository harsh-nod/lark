"""Fully rehash numerical evidence mutations and reject semantic false claims."""

import argparse
import hashlib
import json
from pathlib import Path
import shutil
import struct
import tempfile

from audit_gpu import audit, sha


def write(path, data):
    # Break copied hard links before edits; original evidence stays immutable.
    if path.exists():
        path.unlink()
    path.write_bytes(data)


def save(path, data):
    write(path, (json.dumps(data, indent=2) + "\n").encode())


def rehash(root, input=False):
    names = json.loads((root / "manifest.json").read_text())
    if input:
        save(root / "manifest.json", {"schema": 1, "files": {name: sha(root / name) for name in names["files"]}})
    else:
        save(root / "manifest.json", {name: sha(root / name) for name in names})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--host", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    records = []
    with tempfile.TemporaryDirectory(prefix="lark-rope-numerical-controls-") as temporary:
        base = Path(temporary)
        for name in ("rehashed-wrong-output", "invented-whole-launch-proof", "boolean-certificate-count",
                     "missing-native-trial", "widened-tolerance"):
            root = base / name
            data, host = root / "input", root / "host"
            shutil.copytree(args.input, data, copy_function=shutil.os.link)
            shutil.copytree(args.host, host, copy_function=shutil.os.link)
            report = json.loads((host / "results.json").read_text())
            if name == "rehashed-wrong-output":
                path = host / "interleaved-adapted-query.bin"
                write(path, struct.pack("<e", 123.) + path.read_bytes()[2:])
                report["output_sha256"]["interleaved-adapted-query"] = sha(path)
            elif name == "invented-whole-launch-proof":
                report["whole_kernel_execution_proved"] = True
            elif name == "boolean-certificate-count":
                report["source_certificates"] = False
            elif name == "missing-native-trial":
                report["cases"].pop()
            else:
                meta = json.loads((data / "dataset.json").read_text())
                meta["atol"] = 200.
                save(data / "dataset.json", meta)
                rehash(data, input=True)
                report["input_manifest_sha256"] = sha(data / "manifest.json")
            save(host / "results.json", report)
            rehash(host)
            try:
                result = audit(data.resolve(), [host.resolve()])
            except ValueError as error:
                if name == "rehashed-wrong-output":
                    raise
                records.append({"name": name, "accepted": False, "fully_rehashed": True, "reason": str(error)})
            else:
                if name != "rehashed-wrong-output" or result["status"] != "failed" or result["tolerance_failures"] != 1:
                    raise ValueError("Bad numerical claim accepted: " + name)
                records.append({"name": name, "accepted": False, "fully_rehashed": True,
                                "reason": "fresh float64 reference disagrees", "tolerance_failures": 1})
    result = {"schema": 1, "status": "fully-rehashed-native-rope-numerical-false-claims-rejected",
              "checks": records, "negative_controls": 5, "model_calls": 0, "gpu_trials": 0,
              "original_paper_fully_reproduced": False, "auditor_sha256": sha(Path(__file__).with_name("audit_gpu.py")),
              "control_runner_sha256": sha(Path(__file__))}
    save(args.output / "results.json", result)
    save(args.output / "manifest.json", {"results.json": sha(args.output / "results.json")})
    print(json.dumps({"status": result["status"], "negative_controls": 5}))


if __name__ == "__main__":
    main()
