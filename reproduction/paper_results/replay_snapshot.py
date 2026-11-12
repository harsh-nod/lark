"""Build or replay a frozen paper-coverage snapshot without historical checkouts.

Replaying uses Python's standard library, the snapshot, and the pinned original
manuscript archive. It executes the repository-authored frozen auditor, not
Lean, model calls, GPU experiments or code supplied by the manuscript.
"""

import argparse
import gzip
import hashlib
import io
import json
from pathlib import Path, PurePosixPath
import re
import subprocess
import sys
import tarfile
import tempfile

ROOT = Path(__file__).resolve().parents[2]
DEFAULT = Path(__file__).resolve().parent / "snapshots/20261112-v20"


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(content):
    return hashlib.sha256(content).hexdigest()


def read(path):
    return json.loads(path.read_text())


def write(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n")


def safe_path(name):
    path = PurePosixPath(name)
    require(
        bool(path.parts)
        and not path.is_absolute()
        and ".." not in path.parts
        and str(path) == name,
        "Unsafe path: " + name,
    )
    return path


def file_set(root):
    result = set()
    for path in root.rglob("*"):
        require(not path.is_symlink(), "Snapshot symlink")
        if path.is_file():
            result.add(path.relative_to(root).as_posix())
    return result


def verify_manifest(root, manifest, *, exact=False):
    for name, expected in manifest.items():
        path = root / safe_path(name)
        require(not path.is_symlink(), "Snapshot symlink")
        require(digest(path.read_bytes()) == expected, "Snapshot bytes differ: " + name)
    if exact:
        require(file_set(root) == set(manifest), "Unexpected snapshot files")


def unpack(path, root):
    with tarfile.open(path) as archive:
        seen = set()
        for entry in archive:
            name = safe_path(entry.name)
            require(
                entry.isfile() and entry.size <= 10_000_000 and entry.name not in seen,
                "Unexpected frozen entry",
            )
            seen.add(entry.name)
            target = root / name
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(archive.extractfile(entry).read())


def build(snapshot):
    require(snapshot.is_relative_to(ROOT), "Build definitions must be in this repository")
    require(
        not any(
            (snapshot / name).exists()
            for name in (
                "evidence.tar.gz",
                "evidence-manifest.json",
                "provenance.json",
                "results",
                "manifest.json",
            )
        ),
        "Fresh snapshot outputs required",
    )
    config = read(snapshot / "targets.json")
    commit = config["evidence_commit"]
    require(re.fullmatch(r"[0-9a-f]{40}", commit) is not None, "Full experiment commit required")
    names = {p for group in config["evidence_groups"].values() for p in group}
    names.add("reproduction/results/paper-source-manifest.json")
    local = set(config["local_evidence"])
    require(local <= names, "Unused local evidence")
    content, origins = {}, {}
    for name in sorted(names):
        safe_path(name)
        if name in local:
            path = (ROOT / name).resolve()
            require(
                path.is_relative_to(snapshot) and not (ROOT / name).is_symlink(),
                "Local evidence outside snapshot",
            )
            content[name] = path.read_bytes()
            origins[name] = {
                "kind": "recorded-file",
                "snapshot_path": path.relative_to(snapshot).as_posix(),
            }
        else:
            content[name] = subprocess.check_output(["git", "show", commit + ":" + name], cwd=ROOT)
            origins[name] = {"kind": "git-blob", "commit": commit, "path": name}
    for name, source in (
        ("reproduction/paper_results/audit.py", "auditor.py"),
        ("reproduction/paper_results/targets.json", "targets.json"),
    ):
        content[name] = (snapshot / source).read_bytes()
        origins[name] = {"kind": "snapshot-definition", "snapshot_path": source}
    with (snapshot / "evidence.tar.gz").open("wb") as raw:
        with gzip.GzipFile(fileobj=raw, mode="wb", filename="", mtime=0) as compressed:
            with tarfile.open(fileobj=compressed, mode="w") as archive:
                for name, data in sorted(content.items()):
                    info = tarfile.TarInfo(name)
                    info.size, info.mode = len(data), 0o644
                    archive.addfile(info, io.BytesIO(data))
    hashes = {name: digest(data) for name, data in sorted(content.items())}
    write(snapshot / "evidence-manifest.json", hashes)
    write(
        snapshot / "provenance.json",
        {
            "schema": 1,
            "experiment_code_commit": commit,
            "evidence_archive_sha256": digest((snapshot / "evidence.tar.gz").read_bytes()),
            "evidence_manifest_sha256": digest((snapshot / "evidence-manifest.json").read_bytes()),
            "sources": origins,
            "original_paper_fully_reproduced": False,
            "fresh_lean_checks": 0,
            "fresh_gpu_trials": 0,
            "model_calls": 0,
            "scope": "Frozen selected evidence and authored result mapping. Integrity and source enumeration do not establish experimental validity; linked studies retain their own validation and scope.",
        },
    )


def replay(snapshot, manuscript, *, creating=False):
    if not creating:
        manifest = read(snapshot / "manifest.json")
        verify_manifest(snapshot, manifest)
        require(
            file_set(snapshot) == set(manifest) | {"manifest.json"}, "Unexpected snapshot files"
        )
    provenance = read(snapshot / "provenance.json")
    require(
        digest((snapshot / "evidence.tar.gz").read_bytes()) == provenance["evidence_archive_sha256"]
        and digest((snapshot / "evidence-manifest.json").read_bytes())
        == provenance["evidence_manifest_sha256"],
        "Frozen evidence binding differs",
    )
    with tempfile.TemporaryDirectory(prefix="lark-paper-snapshot-") as temporary:
        root = Path(temporary)
        unpack(snapshot / "evidence.tar.gz", root)
        verify_manifest(root, read(snapshot / "evidence-manifest.json"), exact=True)
        for source, target in (("auditor.py", "audit.py"), ("targets.json", "targets.json")):
            require(
                (snapshot / source).read_bytes()
                == (root / "reproduction/paper_results" / target).read_bytes(),
                "Frozen auditor/targets differ from definitions",
            )
        command = [
            sys.executable,
            str(root / "reproduction/paper_results/audit.py"),
            "--source-archive",
            str(manuscript),
            "--output",
            str(snapshot / "results"),
        ]
        if not creating:
            command.append("--check")
        result = subprocess.run(command, cwd=root, text=True, capture_output=True, timeout=120)
        require(
            result.returncode == 0, "Frozen audit replay failed: " + result.stdout + result.stderr
        )
        record = read(snapshot / "results/audit.json")
        require(
            record["counts"] == {"tables": 17, "outer_figure_groups": 7, "narrative_anchors": 16},
            "Coverage inventory differs",
        )
        require(
            record["original_paper_fully_reproduced"] is False
            and record["completion_percentage"] is None,
            "Unsupported completion claim",
        )
        require(
            all(
                r["original_result_reproduced"] is False
                for r in record["floats"] + record["narrative"]
                if r["role"] in ("experiment", "history")
            ),
            "Unsupported original-result claim",
        )
        require(
            record["evidence_commit"] == provenance["experiment_code_commit"],
            "Experiment anchor differs",
        )
        require(
            not any(record[k] for k in ("fresh_lean_checks", "fresh_gpu_trials", "model_calls")),
            "Unexpected fresh experiment count",
        )
    if creating:
        write(
            snapshot / "manifest.json",
            {name: digest((snapshot / name).read_bytes()) for name in sorted(file_set(snapshot))},
        )
    print(
        json.dumps(
            {
                "status": "frozen-snapshot-written" if creating else "frozen-snapshot-replayed",
                **record["counts"],
                "evidence_files": len(record["evidence_sha256"]),
                "frozen_files": len(read(snapshot / "evidence-manifest.json")),
                "original_paper_fully_reproduced": False,
                "fresh_lean_checks": 0,
                "fresh_gpu_trials": 0,
                "model_calls": 0,
            }
        )
    )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--snapshot", type=Path, default=DEFAULT)
    parser.add_argument("--source-archive", type=Path, required=True)
    parser.add_argument(
        "--build",
        action="store_true",
        help="Create fresh outputs from snapshot definitions and pinned Git blobs",
    )
    args = parser.parse_args()
    snapshot, manuscript = args.snapshot.resolve(), args.source_archive.resolve()
    if args.build:
        build(snapshot)
    replay(snapshot, manuscript, creating=args.build)


if __name__ == "__main__":
    main()
