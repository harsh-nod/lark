"""Compile the certified source and check all native MFMA outputs and tile guards."""

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
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
        [str(out / "driver"), str(data), str(out)], capture_output=True, text=True, timeout=180
    )
    (out / "run.log").write_text(ran.stdout + ran.stderr)
    if ran.returncode:
        raise RuntimeError(ran.stderr)
    device = json.loads(ran.stdout)
    (out / "device.json").write_text(json.dumps(device, indent=2) + "\n")
    actual, expected = (out / "actual.bin").read_bytes(), (data / "expected.bin").read_bytes()
    if len(actual) != len(expected) or len(actual) != manifest["comparisons"] * 4:
        raise ValueError("Output extents differ")
    identical = actual == expected
    mismatches = (
        0
        if identical
        else sum(actual[i : i + 4] != expected[i : i + 4] for i in range(0, len(actual), 4))
    )
    asm = sorted(out.glob("*.s"))
    native = any(re.search(r"v_mfma_f32_16x16x16_?f16", f.read_text()) for f in asm)
    if not native:
        raise ValueError("Native MFMA instruction missing from captured assembly")
    if (
        not device["inputs_unchanged"]
        or not device["per_tile_guard_zones_unchanged"]
        or device["trials"] != manifest["trials"]
        or device["warp"] != 64
    ):
        raise ValueError("Device trial/guard contract differs")
    report = {
        "schema": 1,
        "status": "passed" if identical else "failed",
        "timestamp_utc": datetime.now(timezone.utc).isoformat(),
        "device": device,
        "comparisons": manifest["comparisons"],
        "mismatches": mismatches,
        "native_mfma_assembly_present": native,
        "model_calls": 0,
        "input_manifest_sha256": sha(data / "manifest.json"),
        "runner_sha256": sha(Path(__file__)),
        "binary_sha256": sha(out / "driver"),
        "actual_sha256": sha(out / "actual.bin"),
        "expected_sha256": sha(data / "expected.bin"),
        "compile_command": command,
        "compiler": subprocess.check_output(["hipcc", "--version"], text=True),
        "assembly_sha256": {f.name: sha(f) for f in asm},
        "original_paper_fully_reproduced": False,
        "scope": manifest["scope"],
    }
    (out / "results.json").write_text(json.dumps(report, indent=2) + "\n")
    print(
        json.dumps(
            {
                "status": report["status"],
                "comparisons": report["comparisons"],
                "mismatches": mismatches,
                "native_mfma_assembly_present": native,
            }
        )
    )
    if not identical:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
