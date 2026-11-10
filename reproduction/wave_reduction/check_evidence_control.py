"""Confirm a fully rehashed one-bit raw-output alteration fails the evidence audit."""

import argparse
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tarfile
import tempfile

from summarize import read, sha, unpack


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--results", type=Path, default=Path(__file__).resolve().parent / "results")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise ValueError("Fresh control output required")
    with tempfile.TemporaryDirectory(prefix="lark-wave-divergent-stream-") as temporary:
        temp = Path(temporary)
        altered = temp / "results"
        shutil.copytree(args.results.resolve(), altered)
        archive = altered / "mi350-artifacts.tar.gz"
        decoded = temp / "decoded"
        unpack(archive, decoded)
        output = decoded / "gpu/output.bin"
        content = bytearray(output.read_bytes())
        content[0] ^= 1  # One mantissa bit: remains inside the numerical tolerance.
        output.write_bytes(content)
        report_path = decoded / "gpu/results.json"
        report = read(report_path)
        report["output_sha256"] = sha(output)
        report_path.write_text(json.dumps(report, indent=2) + "\n")
        with tarfile.open(archive, "w:gz") as tar:
            for path in sorted(decoded.rglob("*")):
                if path.is_file():
                    tar.add(path, arcname=path.relative_to(decoded), recursive=False)
        validation = read(altered / "validation.json")
        validation["archives"][archive.name] = sha(archive)
        (altered / "validation.json").write_text(json.dumps(validation, indent=2) + "\n")
        # The top-level publication manifest is not an input to the semantic audit.
        # Update it as well so the control does not depend on stale publication hashes.
        if (altered / "manifest.json").exists():
            manifest = {
                p.relative_to(altered).as_posix(): sha(p)
                for p in sorted(altered.rglob("*"))
                if p.is_file() and p != altered / "manifest.json"
            }
            (altered / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
        result = subprocess.run(
            [
                sys.executable,
                str(Path(__file__).with_name("summarize.py")),
                "--results",
                str(altered),
            ],
            capture_output=True,
            text=True,
            timeout=300,
        )
        log = result.stdout + result.stderr
        if result.returncode == 0 or "Raw GPU/source-tree bits differ" not in log:
            raise RuntimeError("Wrong divergent-stream control outcome: " + log)
        args.output.write_text(log)
    print(
        json.dumps(
            {
                "status": "rejected",
                "control": "fully-rehashed-one-bit-raw-output",
                "gate": "actual raw GPU/source-tree bit comparison",
                "fresh_lean_checks": 0,
                "fresh_gpu_trials": 0,
                "model_calls": 0,
            }
        )
    )


if __name__ == "__main__":
    main()
