"""Audit frozen CPU proofs, regenerate inputs and check both raw AMD output streams.

No fresh Lean, model or GPU execution is performed here. Regeneration uses the
CPU PyTorch version recorded by the original dataset generator.
"""

import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import struct
import subprocess
import sys
import tarfile
import tempfile


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def unpack(archive, dest):
    with tarfile.open(archive) as tar:
        seen = set()
        for m in tar:
            p = PurePosixPath(m.name)
            if not m.isfile() or p.is_absolute() or ".." in p.parts or str(p) in seen:
                raise ValueError("Unexpected archive member")
            seen.add(str(p))
            out = dest / p
            out.parent.mkdir(parents=True, exist_ok=True)
            out.write_bytes(tar.extractfile(m).read())


def manifest(root, records):
    for name, digest in records.items():
        if sha(root / name) != digest:
            raise ValueError("Evidence hash differs: " + name)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--results", required=True, type=Path)
    p.add_argument("--output", type=Path)
    args = p.parse_args()
    root = args.results.resolve()
    validation = json.loads((root / "validation.json").read_text())
    manifest(root, validation["archives"])
    cpu = root / "cpu-20261110"
    manifest(cpu, json.loads((cpu / "manifest.json").read_text()))
    record = json.loads((cpu / "results.json").read_text())
    assert record["status"] == "passed" and len(record["baselines"]) == 2
    assert {x["language"] for x in record["baselines"]} == {"hip", "cuda"}
    assert all(x["status"] == "verified" and x["rechecked"] for x in record["baselines"])
    assert len(record["mutants"]) == 4
    assert all(
        not x["accepted"] and not x["timed_out"] and x["python_preflight_bypassed"]
        for x in record["mutants"]
    )
    for control in record["mutants"]:
        log = (cpu / control["name"] / "lean.log").read_text()
        assert "extract layout (finalState ops input outside)" in log
        assert "application type mismatch" in log
        assert "maximum recursion" not in log and "maximum number of heartbeats" not in log
    hardware = []
    with tempfile.TemporaryDirectory(prefix="lark-production-activation-audit-") as d:
        temp = Path(d)
        frozen, packet, rebuilt = temp / "source", temp / "packet", temp / "rebuilt"
        unpack(root / "source.tar.gz", frozen)
        source_manifest = json.loads((root / "source-manifest.json").read_text())
        manifest(frozen, source_manifest)
        gpu_source = temp / "gpu-source"
        unpack(root / "gpu-source.tar.gz", gpu_source)
        gpu_source_manifest = json.loads((root / "gpu-source-manifest.json").read_text())
        manifest(gpu_source, gpu_source_manifest)
        unpack(root / "gpu-input.tar.gz", packet)
        inputs = packet / "input"
        stored = json.loads((inputs / "manifest.json").read_text())
        manifest(inputs, stored["files"])
        source_runner = "reproduction/production_activation/run_gpu.py"
        assert sha(packet / "runner.py") == gpu_source_manifest[source_runner]
        for name in ("kernel.cu", "reference.py", "task.json", "Main.lean", "report.json"):
            assert (inputs / name).read_bytes() == (cpu / "hip/certificate" / name).read_bytes()
        subprocess.run(
            [
                sys.executable,
                str(gpu_source / "reproduction/production_activation/prepare_gpu.py"),
                "--cpu",
                str(cpu),
                "--output",
                str(rebuilt),
            ],
            check=True,
            capture_output=True,
            text=True,
            timeout=120,
            cwd=gpu_source,
        )
        rebuilt_files = {p.relative_to(rebuilt) for p in rebuilt.rglob("*") if p.is_file()}
        assert rebuilt_files == {p.relative_to(inputs) for p in inputs.rglob("*") if p.is_file()}
        for f in rebuilt_files:
            assert (rebuilt / f).read_bytes() == (inputs / f).read_bytes(), str(f)
        data = json.loads((inputs / "dataset.json").read_text())
        assert len(data["trials"]) == 1024 and data["ast_comparisons"] == 10240
        assert data["intermediate_rounding_differences"] > 0
        for host in ("mi350", "mi350-2"):
            location = temp / host
            unpack(root / (host + "-artifacts.tar.gz"), location)
            run = location / "gpu"
            report = json.loads((run / "results.json").read_text())
            assert report["status"] == "passed" and report["trials"] == 1024
            assert report["input_manifest_sha256"] == sha(inputs / "manifest.json")
            assert report["runner_sha256"] == gpu_source_manifest[source_runner]
            assert report["binary_sha256"] == sha(run / "driver.so")
            a, b = (run / "adapted.bin").read_bytes(), (run / "upstream.bin").read_bytes()
            assert a == b and len(a) == 20480
            assert sha(run / "adapted.bin") == report["adapted_sha256"]
            assert sha(run / "upstream.bin") == report["upstream_sha256"]
            assert report["adapted_upstream_bit_differences"] == 0
            assert report["inputs_unchanged"] and report["all_allocation_guards_unchanged"]
            assert report["adapted_outputs"] == report["upstream_outputs"] == 10240
            expected = [v for trial in data["trials"] for v in trial["expected"]]
            actual = struct.unpack("<10240e", a)
            max_error = max(abs(x - y) for x, y in zip(expected, actual))
            assert all(
                abs(x - y) <= data["atol"] + data["rtol"] * abs(x) for x, y in zip(expected, actual)
            )
            assert report["numerical_failures"] == 0 and report["max_abs_error"] == max_error
            assert report["cpu_reference_comparisons"] == 20480
            hardware.append(
                {
                    "host": host,
                    "trials": 1024,
                    "kernel_launches": 2048,
                    "adapted_outputs": 10240,
                    "upstream_outputs": 10240,
                    "bit_differences": 0,
                    "cpu_reference_comparisons": 20480,
                    "numerical_failures": 0,
                    "max_abs_error": max_error,
                    "inputs_and_guards_unchanged": True,
                }
            )
    summary = {
        "status": "frozen-source-input-regeneration-and-raw-two-host-evidence-audited",
        "certificates": 2,
        "recorded_independent_lean_rechecks": 2,
        "direct_lean_rejections": 4,
        "mutant_timeouts": 0,
        "ast_reference_comparisons": data["ast_comparisons"],
        "outputs_changed_without_intermediate_rounding": data["intermediate_rounding_differences"],
        "hardware": hardware,
        "original_paper_fully_reproduced": False,
        "fresh_lean_checks": 0,
        "fresh_gpu_trials": 0,
        "model_calls": 0,
        "scope": record["scope"],
    }
    if args.output:
        if args.output.exists():
            raise ValueError("Refusing to overwrite an earlier summary")
        args.output.write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
