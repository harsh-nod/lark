"""Restore every frozen GPU input/output byte from metadata and release assets."""

import argparse
import gzip
import hashlib
import json
from pathlib import Path, PurePosixPath
import shutil
import tarfile


def sha(path):
    result = hashlib.sha256()
    with path.open("rb") as stream:
        for part in iter(lambda: stream.read(1024 * 1024), b""):
            result.update(part)
    return result.hexdigest()


def extract(archive_path, directory):
    directory.mkdir(parents=True, exist_ok=False)
    seen = set()
    with tarfile.open(archive_path) as archive:
        for member in archive:
            if member.isdir():
                continue
            rel = PurePosixPath(member.name)
            if (not member.isfile() or rel.is_absolute() or ".." in rel.parts
                    or ".git" in rel.parts or member.name in seen):
                raise ValueError("Unsafe archive entry")
            seen.add(member.name)
            target = directory / rel
            target.parent.mkdir(parents=True, exist_ok=True)
            with archive.extractfile(member) as source, target.open("wb") as output:
                shutil.copyfileobj(source, output, length=1024 * 1024)


def check_manifest(directory, nested=False):
    records = json.loads((directory / "manifest.json").read_text())
    if nested:
        records = records["files"]
    for name, expected in records.items():
        p = PurePosixPath(name)
        if p.is_absolute() or ".." in p.parts or sha(directory / p) != expected:
            raise ValueError("Restored artifact path/hash differs: " + name)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--packet", type=Path, required=True)
    parser.add_argument("--assets", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    packet, assets, out = args.packet.resolve(), args.assets.resolve(), args.output.resolve()
    if out.exists():
        raise ValueError("Choose fresh output")
    check_manifest(packet)
    report = json.loads((packet / "results.json").read_text())
    if report["status"] != "native-softmax-numerical-artifacts-frozen" or not report["four_device_streams_losslessly_deduplicated"]:
        raise ValueError("Unexpected data packet")
    for record in report["assets"].values():
        if Path(record["filename"]).name != record["filename"] or sha(assets / record["filename"]) != record["sha256"]:
            raise ValueError("Release asset differs")
    out.mkdir(parents=True)
    extract(assets / report["assets"]["input"]["filename"], out / "input")
    check_manifest(out / "input", True)
    if sha(out / "input/manifest.json") != report["input_manifest_sha256"]:
        raise ValueError("Input manifest differs")
    common = out / "common-output.bin"
    with gzip.open(assets / report["assets"]["output"]["filename"], "rb") as source, common.open("wb") as output:
        shutil.copyfileobj(source, output, length=1024 * 1024)
    if common.stat().st_size != report["assets"]["output"]["raw_bytes"] or sha(common) != report["assets"]["output"]["raw_sha256"]:
        raise ValueError("Output stream differs")
    for host in ("mi350", "mi350-2"):
        dest = out / host
        extract(packet / host / "runtime.tar.gz", dest)
        for name in ("racy-output.bin", "fixed-output.bin"):
            shutil.copyfile(common, dest / name)
        check_manifest(dest)
    common.unlink()
    receipt = {
        "schema": 1, "status": "all-original-gpu-streams-and-manifests-restored",
        "packet_manifest_sha256": sha(packet / "manifest.json"),
        "restored_per_host_output_streams": 2, "hosts": ["mi350", "mi350-2"],
        "every_original_input_and_device_manifest_checked": True,
        "source_certificates": 0, "original_paper_fully_reproduced": False,
    }
    (out / "restoration.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps(receipt))


if __name__ == "__main__":
    main()
