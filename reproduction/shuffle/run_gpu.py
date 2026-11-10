"""Compile the exact certified HIP sources and check all output bits and guards."""

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import subprocess


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--input", type=Path, required=True)
    p.add_argument("--output", type=Path, required=True)
    args = p.parse_args()
    data, out = args.input.resolve(), args.output.resolve()
    manifest = json.loads((data / "manifest.json").read_text())
    for name, expected in manifest["files"].items():
        if sha(data / name) != expected:
            raise ValueError("Input file differs: " + name)
    out.mkdir(parents=True, exist_ok=False)
    command = [
        "hipcc",
        "-O3",
        "-std=c++17",
        "-ffp-contract=off",
        "--offload-arch=gfx950",
        "--save-temps",
        str(data / "driver.hip"),
        "-o",
        str(out / "driver"),
    ]
    built = subprocess.run(command, cwd=out, capture_output=True, text=True, timeout=180)
    (out / "build.log").write_text(built.stdout + built.stderr)
    if built.returncode:
        raise RuntimeError(built.stderr)
    ran = subprocess.run(
        [
            str(out / "driver"),
            str(data / "input.bin"),
            str(out / "actual.bin"),
            str(out / "device.json"),
        ],
        capture_output=True,
        text=True,
        timeout=60,
    )
    (out / "run.log").write_text(ran.stdout + ran.stderr)
    if ran.returncode:
        raise RuntimeError("Driver failed with code " + str(ran.returncode) + ": " + ran.stderr)
    actual, expected = (out / "actual.bin").read_bytes(), (data / "expected.bin").read_bytes()
    if len(actual) != len(expected) or len(actual) != 3200 * 4:
        raise ValueError("Output count differs")
    mismatches = sum(actual[i : i + 4] != expected[i : i + 4] for i in range(0, len(actual), 4))
    report = {
        "schema": 1,
        "status": "passed" if not mismatches else "failed",
        "timestamp_utc": datetime.now(timezone.utc).isoformat(),
        "device": json.loads((out / "device.json").read_text()),
        "comparisons": 3200,
        "mismatches": mismatches,
        "model_calls": 0,
        "input_manifest_sha256": sha(data / "manifest.json"),
        "runner_sha256": sha(Path(__file__)),
        "binary_sha256": sha(out / "driver"),
        "actual_sha256": sha(out / "actual.bin"),
        "expected_sha256": sha(data / "expected.bin"),
        "compile_command": command,
        "compiler": subprocess.check_output(["hipcc", "--version"], text=True),
        "assembly_sha256": {f.name: sha(f) for f in sorted(out.glob("*.s"))},
        "original_paper_fully_reproduced": False,
        "scope": manifest["scope"],
    }
    (out / "results.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"status": report["status"], "comparisons": 3200, "mismatches": mismatches}))
    if mismatches:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
