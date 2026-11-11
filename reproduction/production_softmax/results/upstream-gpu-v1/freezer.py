"""Freeze numerical metadata and losslessly deduplicate the four device streams.

Large input/output payloads are separate release assets, keeping Git checkouts
small. Original per-host manifests and all source/compiler artifacts remain
unchanged and are fully reconstructed by restore_gpu.py.
"""

import argparse
import gzip
import json
import os
from pathlib import Path
import shutil
import tarfile

from audit_gpu import manifest, sha


def archive_files(directory, destination, excluded):
    with tarfile.open(destination, "w:gz") as archive:
        for path in sorted(directory.rglob("*")):
            if path.is_file() and str(path.relative_to(directory)) not in excluded:
                info = archive.gettarinfo(str(path), arcname=str(path.relative_to(directory)))
                info.uid = info.gid = info.mtime = 0
                info.uname = info.gname = ""
                with path.open("rb") as stream:
                    archive.addfile(info, stream)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--input-archive", type=Path, required=True)
    parser.add_argument("--mi350", type=Path, required=True)
    parser.add_argument("--mi350-2", type=Path, required=True)
    parser.add_argument("--mi350-audit", type=Path, required=True)
    parser.add_argument("--mi350-2-audit", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--assets", type=Path, required=True)
    parser.add_argument("--label", required=True)
    args = parser.parse_args()
    data, out, assets = args.input.resolve(), args.output.resolve(), args.assets.resolve()
    manifest(data, True)
    devices = {"mi350": args.mi350.resolve(), "mi350-2": args.mi350_2.resolve()}
    audits = {"mi350": args.mi350_audit.resolve(), "mi350-2": args.mi350_2_audit.resolve()}
    hashes = set()
    for host, directory in devices.items():
        manifest(directory)
        manifest(audits[host])
        report = json.loads((audits[host] / "results.json").read_text())
        if report["status"] != "full-native-softmax-numerical-checks-passed" or report["paired_bit_differences"]:
            raise ValueError("Numerical audit not passed/bit-identical: " + host)
        for name in ("racy-output.bin", "fixed-output.bin"):
            hashes.add(sha(directory / name))
    if len(hashes) != 1:
        raise ValueError("This lossless archive layout requires four identical output streams")
    out.mkdir(parents=True, exist_ok=False)
    assets.mkdir(parents=True, exist_ok=True)
    input_asset = assets / (args.label + "-input.tar.gz")
    if input_asset.exists():
        raise ValueError("Input asset already exists")
    os.link(args.input_archive.resolve(), input_asset)
    output_asset = assets / (args.label + "-output.bin.gz")
    with output_asset.open("xb") as raw:
        with gzip.GzipFile(filename="", fileobj=raw, mode="wb", mtime=0) as stream:
            with (devices["mi350"] / "racy-output.bin").open("rb") as source:
                shutil.copyfileobj(source, stream, length=1024 * 1024)
    input_meta = out / "input"
    input_meta.mkdir()
    archive_files(data, input_meta / "files.tar.gz", {"input.bin", "expected.bin"})
    shutil.copyfile(data / "manifest.json", input_meta / "original-manifest.json")
    shutil.copyfile(data / "dataset.json", input_meta / "dataset.json")
    summaries = {}
    for host, directory in devices.items():
        dest = out / host
        dest.mkdir()
        archive_files(directory, dest / "runtime.tar.gz", {"racy-output.bin", "fixed-output.bin"})
        shutil.copytree(audits[host], dest / "audit")
        shutil.copyfile(directory / "results.json", dest / "runtime.json")
        summaries[host] = json.loads((audits[host] / "results.json").read_text())
    for name in ("restore_gpu.py", "audit_gpu.py"):
        shutil.copyfile(Path(__file__).with_name(name), out / name)
    shutil.copyfile(Path(__file__), out / "freezer.py")
    metadata = json.loads((data / "dataset.json").read_text())
    records = {
        "input": {"filename": input_asset.name, "sha256": sha(input_asset), "bytes": input_asset.stat().st_size},
        "output": {"filename": output_asset.name, "sha256": sha(output_asset), "bytes": output_asset.stat().st_size,
                   "raw_sha256": next(iter(hashes)), "raw_bytes": (devices["mi350"] / "racy-output.bin").stat().st_size},
    }
    for asset in records.values():
        if asset["bytes"] >= 2 * 1024 ** 3:
            raise ValueError("Release asset exceeds2GiB; split before publishing")
    report = {
        "schema": 1, "status": "native-softmax-numerical-artifacts-frozen", "label": args.label,
        "assets": records, "rows": [c["rows"] for c in metadata["cases"]],
        "input_manifest_sha256": sha(data / "manifest.json"),
        "four_device_streams_losslessly_deduplicated": True,
        "comparisons_per_host": {host: sum(m["comparisons"] for m in r["methods"].values()) for host, r in summaries.items()},
        "numerical_failures": sum(m["failed"] for r in summaries.values() for m in r["methods"].values()),
        "paired_trials_per_host": {host: r["trials"] for host, r in summaries.items()},
        "whole_kernel_lean_execution_proved": False, "source_certificates": 0,
        "original_source_race_free": False, "repair_universal_race_freedom_proved": False,
        "ieee_equivalence_proved": False, "floating_point_error_bound_proved": False,
        "original_paper_fully_reproduced": False, "model_calls": 0,
    }
    (out / "results.json").write_text(json.dumps(report, indent=2) + "\n")
    (out / "manifest.json").write_text(json.dumps({str(p.relative_to(out)): sha(p)
                                                   for p in sorted(out.rglob("*")) if p.is_file()}, indent=2) + "\n")
    print(json.dumps({"label": args.label, "assets": records, "failures": report["numerical_failures"]}))


if __name__ == "__main__":
    main()
