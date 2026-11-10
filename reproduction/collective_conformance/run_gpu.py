"""Compile and check the pinned wave64 shuffle/MFMA probes on an idle gfx950 GPU."""

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import struct
import subprocess


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--input", type=Path, required=True)
    p.add_argument("--output", type=Path, required=True)
    args = p.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    manifest = json.loads((args.input / "dataset.json").read_text())
    source = args.input / "probes.hip"
    assert sha(source) == manifest["source_sha256"]
    for name, digest in manifest["files"].items():
        assert sha(args.input / name) == digest
    exe = args.output / "probes"
    command = [
        "hipcc",
        "-O3",
        "-std=c++17",
        "-ffp-contract=off",
        "--offload-arch=gfx950",
        "--save-temps",
        str(source.resolve()),
        "-o",
        str(exe.resolve()),
    ]
    compiled = subprocess.run(command, cwd=args.output, capture_output=True, text=True, timeout=180)
    (args.output / "build.log").write_text(compiled.stdout + compiled.stderr)
    if compiled.returncode:
        raise RuntimeError(compiled.stderr)
    run = subprocess.run(
        [str(exe.resolve()), str(args.input.resolve()), str(args.output.resolve())],
        capture_output=True,
        text=True,
        timeout=180,
    )
    (args.output / "run.log").write_text(run.stdout + run.stderr)
    if run.returncode:
        raise RuntimeError(run.stderr)
    driver = json.loads(run.stdout)
    results = []
    for stem, count, kind in (
        ("shuffle", manifest["shuffle_comparisons"], "I"),
        ("mfma", manifest["mfma_output_comparisons"], "f"),
    ):
        actual = (args.output / (stem + "-actual.bin")).read_bytes()
        expected = (args.input / (stem + "-expected.bin")).read_bytes()
        assert len(actual) == len(expected) == count * 4
        identical = actual == expected
        mismatches, first = 0, None
        if not identical:
            for i, (a, b) in enumerate(
                zip(
                    struct.iter_unpack("<" + kind, actual), struct.iter_unpack("<" + kind, expected)
                )
            ):
                if a[0] != b[0]:
                    mismatches += 1
                    if first is None:
                        first = {"index": i, "actual": a[0], "expected": b[0]}
        results.append(
            {
                "probe": stem,
                "comparisons": count,
                "mismatches": mismatches,
                "first_mismatch": first,
                "bit_identical": identical,
                "actual_sha256": hashlib.sha256(actual).hexdigest(),
                "expected_sha256": hashlib.sha256(expected).hexdigest(),
            }
        )
    asm = sorted(args.output.glob("*gfx950*.s"))
    mfma_asm = [p for p in asm if "v_mfma_f32_16x16x16" in p.read_text()]
    report = {
        "schema": 1,
        "status": "passed" if not any(r["mismatches"] for r in results) else "failed",
        "experiment": manifest["experiment"],
        "timestamp_utc": datetime.now(timezone.utc).isoformat(),
        "device": driver["device"],
        "architecture": "gfx950",
        "warp": driver["warp"],
        "inputs_unchanged": driver["inputs_unchanged"],
        "guard_zones_unchanged": driver["guard_zones_unchanged"],
        "model_calls": 0,
        "runner_sha256": sha(Path(__file__)),
        "source_sha256": sha(source),
        "dataset_sha256": sha(args.input / "dataset.json"),
        "binary_sha256": sha(exe),
        "compile_command": command,
        "compiler": subprocess.check_output(["hipcc", "--version"], text=True),
        "compiler_mfma_assembly_present": bool(mfma_asm),
        "compiler_assembly_hashes": {p.name: sha(p) for p in asm},
        "results": results,
        "scope": manifest["scope"],
    }
    (args.output / "results.json").write_text(json.dumps(report, indent=2) + "\n")
    print(
        json.dumps(
            {
                "status": report["status"],
                "comparisons": sum(r["comparisons"] for r in results),
                "compiler_mfma_assembly_present": bool(mfma_asm),
            }
        )
    )
    if report["status"] != "passed":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
