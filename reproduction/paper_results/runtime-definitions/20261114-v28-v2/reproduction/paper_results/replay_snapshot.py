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
import runpy
import subprocess
import sys
import tarfile
import tempfile

ROOT = Path(__file__).resolve().parents[2]
DEFAULT = Path(__file__).resolve().parent / "snapshots/20261114-v28"
AUDITOR_STREAM_BUFFER_BYTES = 1024 * 1024
_TAR_OPEN = tarfile.open
_DEFAULT_BUFFER = object()


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(content):
    return hashlib.sha256(content).hexdigest()


def auditor_tar_open(name=None, mode="r", fileobj=None, bufsize=_DEFAULT_BUFFER, **kwargs):
    """Use larger default stream reads; retain every stdlib parser and check."""
    if bufsize is _DEFAULT_BUFFER:
        bufsize = (AUDITOR_STREAM_BUFFER_BYTES if type(mode) is str and mode.startswith("r|")
                   else tarfile.RECORDSIZE)
    return _TAR_OPEN(name=name, mode=mode, fileobj=fileobj, bufsize=bufsize, **kwargs)


def run_frozen_auditor(script, expected_sha256, arguments):
    """Execute the same verified authored auditor with buffered tar streams."""
    script = Path(script)
    require(not script.is_symlink() and script.is_file()
            and digest(script.read_bytes()) == expected_sha256, "Frozen auditor bytes differ")
    tarfile.open = auditor_tar_open
    # Match direct-script imports and argv. The child starts in isolated mode,
    # so captured files in its working directory cannot shadow the stdlib.
    sys.path.insert(0, str(script.parent))
    sys.argv = [str(script), *arguments]
    runpy.run_path(str(script), run_name="__main__")


def read(path):
    return json.loads(path.read_text())


def write(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n")


def archive_storage():
    # Legacy standalone replays remain standard-library-only and do not need
    # this helper. Version2 standalone replays receive the authored sibling.
    if __package__:
        from . import snapshot_archives
    else:
        import snapshot_archives
    return snapshot_archives


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


def preserved_origins(config, names, local):
    """Select explicitly pinned earlier bytes without replacing their logical paths."""
    selected = config.get("preserved_evidence_origins", {})
    definitions = {"reproduction/paper_results/audit.py", "reproduction/paper_results/targets.json"}
    require(type(selected) is dict and set(selected) <= names - local - definitions,
            "Unused or invalid preserved evidence origin")
    for name, row in selected.items():
        safe_path(name)
        require(type(row) is dict and set(row) == {"commit", "sha256"}
                and type(row["commit"]) is str and re.fullmatch("[0-9a-f]{40}", row["commit"]) is not None
                and type(row["sha256"]) is str and re.fullmatch("[0-9a-f]{64}", row["sha256"]) is not None,
                "Concrete preserved commit and SHA256 required")
    return selected


def committed_evidence(name, commit, selected, *, root=ROOT):
    safe_path(name)
    row = selected.get(name)
    origin = commit if row is None else row["commit"]
    if row is not None:
        result = subprocess.run(["git", "merge-base", "--is-ancestor", origin, commit],
                                cwd=root, capture_output=True)
        require(result.returncode == 0, "Preserved evidence commit is not an ancestor")
    data = subprocess.check_output(["git", "show", origin + ":" + name], cwd=root)
    require(row is None or digest(data) == row["sha256"], "Preserved evidence bytes differ")
    return data, {"kind": "git-blob", "commit": origin, "path": name}


def build(snapshot):
    require(snapshot.is_relative_to(ROOT), "Build definitions must be in this repository")
    require(
        not any(
            (snapshot / name).exists()
            for name in (
                "evidence.tar.gz",
                "evidence-manifest.json",
                "evidence-layout.json",
                "provenance.json",
                "results",
                "manifest.json",
            )
        ),
        "Fresh snapshot outputs required",
    )
    require(not list(snapshot.glob("evidence-part-*.tar.gz")), "Fresh archive parts required")
    config = read(snapshot / "targets.json")
    storage_schema = config.get("storage_schema", 1)
    require(type(storage_schema) is int and storage_schema in (1, 2), "Unsupported storage schema")
    commit = config["evidence_commit"]
    require(re.fullmatch(r"[0-9a-f]{40}", commit) is not None, "Full experiment commit required")
    names = {p for group in config["evidence_groups"].values() for p in group}
    names.add("reproduction/results/paper-source-manifest.json")
    local = set(config["local_evidence"])
    require(local <= names, "Unused local evidence")
    selected = preserved_origins(config, names, local)
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
            content[name], origins[name] = committed_evidence(name, commit, selected)
    for name, source in (
        ("reproduction/paper_results/audit.py", "auditor.py"),
        ("reproduction/paper_results/targets.json", "targets.json"),
    ):
        content[name] = (snapshot / source).read_bytes()
        origins[name] = {"kind": "snapshot-definition", "snapshot_path": source}
    if storage_schema == 1:
        with (snapshot / "evidence.tar.gz").open("wb") as raw:
            with gzip.GzipFile(fileobj=raw, mode="wb", filename="", mtime=0) as compressed:
                with tarfile.open(fileobj=compressed, mode="w") as archive:
                    for name, data in sorted(content.items()):
                        info = tarfile.TarInfo(name)
                        info.size, info.mode = len(data), 0o644
                        archive.addfile(info, io.BytesIO(data))
        archive_binding = {"evidence_archive_sha256": digest((snapshot / "evidence.tar.gz").read_bytes())}
    else:
        layout = archive_storage().build_parts(snapshot, content)
        write(snapshot / "evidence-layout.json", layout)
        archive_binding = {"evidence_layout_sha256": digest((snapshot / "evidence-layout.json").read_bytes())}
    hashes = {name: digest(data) for name, data in sorted(content.items())}
    write(snapshot / "evidence-manifest.json", hashes)
    write(
        snapshot / "provenance.json",
        {
            "schema": storage_schema,
            "experiment_code_commit": commit,
            **archive_binding,
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
    provenance = read(snapshot / "provenance.json")
    schema = provenance["schema"]
    require(type(schema) is int and schema in (1, 2), "Unsupported storage schema")
    expected_archives = None
    if not creating:
        manifest = read(snapshot / "manifest.json")
        if schema == 2:
            # The unpacker compares one actual digest with both independent
            # archive bindings before decoding. Every other file is checked
            # here, and its exact archive roster is checked against the layout.
            expected_archives = {name: value for name, value in manifest.items()
                                 if re.fullmatch(r"evidence-part-[0-9]{4,}\.tar\.gz", name)}
            verify_manifest(snapshot, {name: value for name, value in manifest.items()
                                       if name not in expected_archives})
        else:
            verify_manifest(snapshot, manifest)
        require(
            file_set(snapshot) == set(manifest) | {"manifest.json"}, "Unexpected snapshot files"
        )
    evidence_hashes = read(snapshot / "evidence-manifest.json")
    require(
        digest((snapshot / "evidence-manifest.json").read_bytes())
        == provenance["evidence_manifest_sha256"],
        "Frozen evidence binding differs",
    )
    if schema == 1:
        require(digest((snapshot / "evidence.tar.gz").read_bytes()) == provenance["evidence_archive_sha256"],
                "Frozen archive binding differs")
    else:
        require(digest((snapshot / "evidence-layout.json").read_bytes()) == provenance["evidence_layout_sha256"],
                "Frozen archive layout binding differs")
        layout = read(snapshot / "evidence-layout.json")
        # unpack_parts validates this complete layout and its manifest before
        # reading any archive. Keep that gate once, with the same bound data.
    with tempfile.TemporaryDirectory(prefix="lark-paper-snapshot-") as temporary:
        root = Path(temporary)
        if schema == 1:
            unpack(snapshot / "evidence.tar.gz", root)
            verify_manifest(root, evidence_hashes, exact=True)
        else:
            try:
                archive_storage().unpack_parts(snapshot, layout, root, expected_hashes=evidence_hashes,
                                               expected_archive_hashes=expected_archives)
            except Exception:
                # Invalid structural metadata can fail before the unpacker
                # reaches physical archives. Preserve their outer integrity
                # gate (and its precedence) on that failure path as well.
                if expected_archives is not None:
                    verify_manifest(snapshot, expected_archives)
                raise
        for source, target in (("auditor.py", "audit.py"), ("targets.json", "targets.json")):
            require(
                (snapshot / source).read_bytes()
                == (root / "reproduction/paper_results" / target).read_bytes(),
                "Frozen auditor/targets differ from definitions",
            )
        command = [
            sys.executable,
            "-I",
            str(Path(__file__).resolve()),
            "--_frozen-auditor",
            str(root / "reproduction/paper_results/audit.py"),
            digest((root / "reproduction/paper_results/audit.py").read_bytes()),
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
    if sys.argv[1:2] == ["--_frozen-auditor"]:
        require(len(sys.argv) >= 4, "Frozen auditor source/hash arguments required")
        run_frozen_auditor(sys.argv[2], sys.argv[3], sys.argv[4:])
    else:
        main()
