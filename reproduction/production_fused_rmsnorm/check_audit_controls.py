"""Reject rehashed false scope claims and a nonfinite normalized output."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent


def sha(path):
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def write(path, data):
    # Copied trees use hard links; replace the directory entry before mutation.
    path.unlink()
    path.write_text(json.dumps(data, indent=2) + "\n")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--host", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    checks = []
    with tempfile.TemporaryDirectory(prefix="lark-fused-audit-controls-") as temp:
        for name in ("invented-source-certificate", "original-paper-completion", "nonfinite-output"):
            altered = Path(temp) / name
            shutil.copytree(args.host, altered, copy_function=os.link)
            report = json.loads((altered / "results.json").read_text())
            if name == "invented-source-certificate":
                report["source_certificates"] = 1
                message = "Runtime binding or scope differs"
            elif name == "original-paper-completion":
                report["original_paper_fully_reproduced"] = True
                message = "Runtime binding or scope differs"
            else:
                path = altered / "adapted-input.bin"
                replaced = altered / "replacement.bin"
                shutil.copyfile(path, replaced)
                path.unlink()
                replaced.rename(path)
                with path.open("r+b") as stream:
                    stream.write(b"\x00\x7e")
                report["output_sha256"]["adapted-input"] = sha(path)
                message = "Nonfinite normalized output"
            write(altered / "results.json", report)
            hashes = json.loads((altered / "manifest.json").read_text())
            hashes["results.json"] = sha(altered / "results.json")
            if name == "nonfinite-output":
                hashes["adapted-input.bin"] = sha(altered / "adapted-input.bin")
            write(altered / "manifest.json", hashes)
            run = subprocess.run([sys.executable, str(HERE / "audit_gpu.py"), "--input", str(args.input.resolve()),
                                  "--host", str(altered), "--output", str(Path(temp) / (name + ".json"))],
                                 capture_output=True, text=True, timeout=120)
            log = run.stdout + run.stderr
            (out / (name + ".log")).write_text(log)
            if run.returncode == 0 or message not in log:
                raise ValueError("Wrong audit control outcome: " + name + "\n" + log)
            checks.append({"name": name, "accepted": False, "fully_rehashed": True, "gate": message})
    report = {"schema": 1, "status": "passed", "negative_controls": 3, "checks": checks,
              "input_manifest_sha256": sha(args.input / "manifest.json"),
              "host_manifest_sha256": sha(args.host / "manifest.json"),
              "auditor_sha256": sha(HERE / "audit_gpu.py"), "checker_sha256": sha(Path(__file__)),
              "fresh_gpu_trials": 0, "model_calls": 0, "original_paper_fully_reproduced": False}
    (out / "results.json").write_text(json.dumps(report, indent=2) + "\n")
    (out / "manifest.json").write_text(json.dumps({p.name: sha(p) for p in sorted(out.iterdir()) if p.is_file()}, indent=2) + "\n")
    print(json.dumps({"status": "passed", "negative_controls": 3, "fully_rehashed": True}))


if __name__ == "__main__":
    main()
