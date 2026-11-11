"""Restore the frozen numerical packet and rerun its CPU audit outside Git.

Requires NumPy (the recorded run used 2.4.4). This does not run GPUs, Lean or
models. The separate component archives contain their standalone Lean projects.
"""

import argparse
import gzip
import hashlib
import json
from pathlib import Path, PurePosixPath
import shutil
import subprocess
import sys
import tarfile

HERE = Path(__file__).resolve().parent


def sha(path):
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def safe(name):
    path = PurePosixPath(name)
    if path.is_absolute() or ".." in path.parts or not path.parts or str(path) != name:
        raise ValueError("Unsafe packet member: " + name)
    return path


def extract(archive, root):
    seen = set()
    with tarfile.open(archive) as bundle:
        for member in bundle:
            name = safe(member.name)
            if not member.isfile() or member.size > 25_000_000 or name in seen:
                raise ValueError("Unexpected packet member: " + member.name)
            seen.add(name)
            dest = root / name
            dest.parent.mkdir(parents=True, exist_ok=True)
            dest.write_bytes(bundle.extractfile(member).read())


def restore(source, root, archive):
    root.mkdir(parents=True, exist_ok=False)
    extract(source / archive, root)
    for path in sorted(source.glob("*.bin.gz")):
        with gzip.open(path, "rb") as compressed, (root / path.name[:-3]).open("wb") as stream:
            size = 0
            for block in iter(lambda: compressed.read(1024 * 1024), b""):
                size += len(block)
                if size > 150_000_000:
                    raise ValueError("Unexpected decompressed stream size")
                stream.write(block)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--packet", type=Path, default=HERE if (HERE / "report.json").exists() else HERE / "results/native-v1")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    packet, out = args.packet.resolve(), args.output.resolve()
    if out.is_relative_to(packet) or any((p / ".git").exists() for p in (out, *out.parents)):
        raise ValueError("Fresh output must be outside the checkout/packet")
    hashes = json.loads((packet / "manifest.json").read_text())
    if any(p.is_symlink() for p in packet.rglob("*")):
        raise ValueError("Packet symlinks are not accepted")
    actual = {p.relative_to(packet).as_posix() for p in packet.rglob("*") if p.is_file()}
    if actual != set(hashes) | {"manifest.json"}:
        raise ValueError("Unexpected packet files")
    for name, digest in hashes.items():
        if sha(packet / safe(name)) != digest:
            raise ValueError("Packet hash differs: " + name)
    if sha(Path(__file__)) != sha(packet / "replay_packet.py"):
        raise ValueError("Use the frozen replay script")
    report = json.loads((packet / "report.json").read_text())
    if (report["source_certificates"] != 0 or report["whole_kernel_execution_proved"]
            or report["actual_trace_classification_proved"] or report["original_paper_fully_reproduced"]):
        raise ValueError("Unsupported development completion claim")
    source_manifest = json.loads((packet / "source-manifest.json").read_text())
    prefix = "reproduction/production_fused_rmsnorm/"
    if sha(packet / "numerical-auditor.py") != source_manifest[prefix + "audit_gpu.py"]:
        raise ValueError("Auditor differs from experiment source")
    out.mkdir(parents=True, exist_ok=False)
    data = out / "input"
    restore(packet / "input", data, "files.tar.gz")
    input_manifest = json.loads((data / "manifest.json").read_text())
    if input_manifest["generator_sha256"] != source_manifest[prefix + "prepare_gpu.py"]:
        raise ValueError("Generator differs from experiment source")
    hosts = []
    if list(report["restored_host_directories"]) != ["mi350", "mi350-2"]:
        raise ValueError("Unexpected host cohort")
    for label, directory in report["restored_host_directories"].items():
        target = out / safe(directory)
        restore(packet / safe(label), target, "runtime.tar.gz")
        hosts.append(target)
    output = out / "numerical-replay.json"
    command = [sys.executable, str(packet / "numerical-auditor.py"), "--input", str(data), "--output", str(output)]
    for host in hosts:
        command += ["--host", str(host)]
    run = subprocess.run(command, cwd=out, capture_output=True, text=True, timeout=300)
    (out / "audit.log").write_text(run.stdout + run.stderr)
    if run.returncode:
        raise ValueError("Frozen numerical replay failed: " + run.stdout + run.stderr)
    if output.read_bytes() != (packet / "gpu-audit.json").read_bytes():
        raise ValueError("Numerical report differs after independent recomputation")
    result = {"schema": 1, "status": "frozen-numerical-packet-replayed", "outside_git": True,
              "packet_manifest_sha256": sha(packet / "manifest.json"),
              "fresh_cpu_double_reference_cases": 24,
              "normalized_comparisons": 127008768, "residual_bit_comparisons": 127008768,
              "fresh_lean_checks": 0, "fresh_gpu_trials": 0, "model_calls": 0,
              "original_paper_fully_reproduced": False}
    (out / "results.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result))


if __name__ == "__main__":
    main()
