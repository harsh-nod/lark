"""Verify every FFN payload archive against a separately pinned manifest.

This standard-library-only reader executes no captured Python, Lean or compiled
objects. It checks publication integrity, not kernel correctness or paper results.
"""

import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import tarfile


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for data in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(data)
    return digest.hexdigest()


def write(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n")


def read(path):
    return json.loads(path.read_text())


def valid_sha(value):
    return type(value) is str and re.fullmatch(r"[0-9a-f]{64}", value) is not None


def safe_path(name):
    require(type(name) is str and bool(name), "Nonempty member path required")
    path = PurePosixPath(name)
    require(bool(path.parts) and not path.is_absolute() and str(path) == name and ".." not in path.parts,
            "Unsafe member path")


def verify(root, expected_manifest_sha256, output):
    root, output = Path(root).resolve(), Path(output).resolve()
    require(not output.exists() and not any((p / ".git").exists() for p in (output, *output.parents)),
            "Fresh output outside Git required")
    require(valid_sha(expected_manifest_sha256) and sha(root / "manifest.json") == expected_manifest_sha256,
            "Pinned complete publication manifest differs")
    paths = set()
    for path in root.rglob("*"):
        require(not path.is_symlink(), "Publication symlink")
        if path.is_file():
            paths.add(path.relative_to(root).as_posix())
    inventory = read(root / "manifest.json")
    require(type(inventory) is dict and paths == set(inventory) | {"manifest.json"},
            "Publication file inventory differs")
    for name, value in inventory.items():
        safe_path(name)
        require(valid_sha(value) and sha(root / name) == value, "Publication file bytes differ: " + name)
    report = read(root / "results.json")
    require(report["status"] == "complete-current-FFN-certificate-payloads-packaged-and-byte-checked"
            and report["SDK_producer_commit"] == "f49adeb6472a163b58e209e0ec62646b2f23c75f"
            and report["original_paper_fully_reproduced"] is report["main_promotion_claim"] is False
            and all(type(report[key]) is int and report[key] == value for key, value in {
                "complete_original_positive_checks": 3, "direct_Lean_negative_controls": 4,
                "complete_false_recording_payloads": 31, "current_owned_source_bindings": 72,
                "fresh_Lean_checks_during_packaging": 0, "source_bound_proofs_added": 0,
                "new_registered_source_certificates": 0, "model_calls": 0, "GPU_trials": 0,
            }.items()), "Publication scope/counters differ")
    archives = report["archives"]
    require(type(archives) is dict and bool(archives), "Complete archive roster required")
    expected = {"manifest.json", "results.json", "packaging-driver.py"}
    for label in archives:
        require(type(label) is str and re.fullmatch(r"[a-z0-9-]+", label) is not None,
                "Safe archive label required")
        expected.update((label + ".tar.gz", label + "-files.json"))
    require(paths == expected, "Publication archive roster differs")
    output.mkdir(parents=True)
    checked, total_files, total_bytes = [], 0, 0
    for label, row in archives.items():
        require(type(row) is dict and set(row) == {
            "group", "files", "uncompressed_bytes", "archive_bytes", "archive_sha256", "inventory_sha256"},
            "Archive metadata roster differs")
        require(row["group"] in ("positive", "direct-controls", "installed-wheel", "rehashed-controls")
                and all(type(row[key]) is int and low <= row[key] <= high for key, low, high in (
                    ("files", 1, 100000), ("uncompressed_bytes", 0, 85000000),
                    ("archive_bytes", 1, 90000000))), "Archive bounds differ")
        archive, members_path = root / (label + ".tar.gz"), root / (label + "-files.json")
        require(archive.stat().st_size == row["archive_bytes"] and sha(archive) == row["archive_sha256"]
                and sha(members_path) == row["inventory_sha256"], "Archive/inventory binding differs")
        members = read(members_path)
        require(type(members) is dict and len(members) == row["files"], "Member roster differs")
        for name, bound in members.items():
            safe_path(name)
            require(type(bound) is dict and set(bound) == {"bytes", "sha256"}
                    and type(bound["bytes"]) is int and 0 <= bound["bytes"] <= 10000000
                    and valid_sha(bound["sha256"]), "Member binding/bounds differ")
        seen, size = set(), 0
        with tarfile.open(archive, mode="r|gz") as stream:
            for member in stream:
                require(member.isfile() and member.name in members and member.name not in seen,
                        "Unexpected or nonregular archive member")
                bound = members[member.name]
                require(member.size == bound["bytes"], "Member size differs")
                data = stream.extractfile(member).read()
                require(len(data) == member.size and hashlib.sha256(data).hexdigest() == bound["sha256"],
                        "Actual archive member bytes differ")
                seen.add(member.name)
                size += len(data)
        require(seen == set(members) and size == row["uncompressed_bytes"],
                "Incomplete archive payload")
        total_files += len(seen)
        total_bytes += size
        checked.append({"archive": label, "members": len(seen), "bytes": size})
        write(output / "progress.json", {"archives_checked": checked})
    result = {
        "status": "complete-FFN-publication-payload-integrity-passed",
        "packet_manifest_sha256": expected_manifest_sha256,
        "archives_checked": checked, "archive_members_checked": total_files,
        "uncompressed_member_bytes_checked": total_bytes,
        "captured_code_executed": False, "fresh_Lean_checks": 0, "model_calls": 0, "GPU_trials": 0,
        "new_registered_source_certificates": 0, "original_paper_fully_reproduced": False,
        "scope": "Complete file/archive/member bytes match a separately pinned publication manifest. "
                 "This data-integrity check adds no proof, model, hardware or original-paper result.",
    }
    write(output / "results.json", result)
    write(output / "manifest.json", {p.name: sha(p) for p in output.iterdir() if p.is_file()})
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--packet", type=Path, required=True)
    parser.add_argument("--expected-manifest-sha256", required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    result = verify(args.packet, args.expected_manifest_sha256, args.output)
    print(json.dumps({key: result[key] for key in ("status", "archive_members_checked",
                                                 "uncompressed_member_bytes_checked")}), flush=True)


if __name__ == "__main__":
    main()
