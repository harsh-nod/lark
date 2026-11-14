"""Versioned, lossless snapshot storage with bounded tar entries and part sizes.

Logical evidence files retain their complete bytes and hashes. Oversized files
are represented by contiguous chunks of at most the existing 10,000,000-byte
tar-entry limit. This adds no model, GPU, Lean or captured-code execution.
"""

import gzip
import hashlib
import io
from pathlib import Path, PurePosixPath
import re
import tarfile

SCHEMA = 2
MAX_ENTRY_BYTES = 10_000_000
MAX_TAR_BYTES = 85_000_000
MAX_ARCHIVE_BYTES = 90_000_000
# Decode larger blocks without changing any physical/member/logical limit.
STREAM_BUFFER_BYTES = 1024 * 1024


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def file_digest(path):
    value = hashlib.sha256()
    with path.open("rb") as source:
        for data in iter(lambda: source.read(1024 * 1024), b""):
            value.update(data)
    return value.hexdigest()


def safe_path(name):
    require(type(name) is str, "String evidence path required")
    path = PurePosixPath(name)
    require(bool(path.parts) and not path.is_absolute() and ".." not in path.parts
            and str(path) == name, "Unsafe evidence path")
    return path


def sha(value):
    return type(value) is str and re.fullmatch(r"[0-9a-f]{64}", value) is not None


def part_name(number):
    return f"evidence-part-{number:04d}.tar.gz"


def validate_layout(layout, expected_hashes=None):
    require(type(layout) is dict and set(layout) == {"schema", "logical_files", "archives"}
            and type(layout["schema"]) is int and layout["schema"] == SCHEMA,
            "Unsupported snapshot archive layout")
    files, archives = layout["logical_files"], layout["archives"]
    require(type(files) is dict and bool(files) and type(archives) is list and bool(archives),
            "Complete logical files and archives required")
    for name, row in files.items():
        path = safe_path(name)
        require(type(row) is dict and set(row) == {"bytes", "sha256"}
                and type(row["bytes"]) is int and row["bytes"] >= 0 and sha(row["sha256"]),
                "Invalid logical file binding")
        require(not any(str(parent) in files for parent in path.parents),
                "Logical file/directory collision")
    if expected_hashes is not None:
        require({name: row["sha256"] for name, row in files.items()} == expected_hashes,
                "Logical evidence manifest differs")
    offsets, started = {name: 0 for name in files}, set()
    for number, archive in enumerate(archives, 1):
        require(type(archive) is dict and set(archive) == {"path", "bytes", "sha256", "entries"}
                and archive["path"] == part_name(number)
                and type(archive["bytes"]) is int and 0 < archive["bytes"] <= MAX_ARCHIVE_BYTES
                and sha(archive["sha256"]) and type(archive["entries"]) is dict
                and bool(archive["entries"]), "Invalid archive binding")
        for member, fragment in archive["entries"].items():
            safe_path(member)
            require(type(fragment) is dict and set(fragment) == {"file", "offset", "bytes", "sha256"},
                    "Invalid evidence fragment")
            name, offset, size = fragment["file"], fragment["offset"], fragment["bytes"]
            require(type(name) is str and name in files and type(offset) is int
                    and type(size) is int and 0 <= size <= MAX_ENTRY_BYTES and sha(fragment["sha256"]),
                    "Invalid bounded fragment binding")
            require(offset == offsets[name] and offset + size <= files[name]["bytes"],
                    "Non-contiguous or oversized logical evidence")
            require((size > 0 and offset < files[name]["bytes"])
                    or (size == 0 and files[name]["bytes"] == 0 and name not in started),
                    "Duplicate or unnecessary empty evidence fragment")
            offsets[name] += size
            started.add(name)
    require(started == set(files) and all(offsets[name] == row["bytes"] for name, row in files.items()),
            "Missing logical evidence bytes")
    return layout


def build_parts(snapshot, content, *, chunk_bytes=MAX_ENTRY_BYTES, tar_bytes=MAX_TAR_BYTES):
    snapshot = Path(snapshot)
    require(snapshot.is_dir() and not snapshot.is_symlink(), "Existing snapshot directory required")
    require(type(chunk_bytes) is int and 0 < chunk_bytes <= MAX_ENTRY_BYTES
            and type(tar_bytes) is int and 1024 <= tar_bytes <= MAX_TAR_BYTES,
            "Existing archive entry/part bounds required")
    require(type(content) is dict and bool(content) and all(type(name) is str for name in content),
            "Complete evidence content with string paths required")
    require(not list(snapshot.glob("evidence-part-*.tar.gz")), "Fresh archive outputs required")
    logical = {}
    for name, data in sorted(content.items()):
        safe_path(name)
        require(type(data) is bytes, "Evidence must be immutable bytes")
        logical[name] = {"bytes": len(data), "sha256": digest(data)}
    archives = []
    raw = compressed = archive = None
    current = None
    used = 0

    def finish():
        nonlocal raw, compressed, archive
        if archive is None:
            return
        archive.close()
        compressed.close()
        raw.close()
        path = snapshot / current["path"]
        current.update(bytes=path.stat().st_size, sha256=file_digest(path))
        require(current["bytes"] <= MAX_ARCHIVE_BYTES, "Archive exceeds existing storage bound")
        raw = compressed = archive = None

    try:
        for file_number, (name, data) in enumerate(sorted(content.items())):
            positions = range(0, len(data), chunk_bytes) if data else (0,)
            for offset in positions:
                chunk = data[offset:offset + chunk_bytes]
                encoded_size = 512 + ((len(chunk) + 511) // 512) * 512
                require(encoded_size <= tar_bytes, "One bounded chunk exceeds the part budget")
                if archive is None or used + encoded_size > tar_bytes:
                    finish()
                    current = {"path": part_name(len(archives) + 1), "entries": {}}
                    archives.append(current)
                    raw = (snapshot / current["path"]).open("xb")
                    compressed = gzip.GzipFile(fileobj=raw, mode="wb", filename="", mtime=0, compresslevel=6)
                    archive = tarfile.open(fileobj=compressed, mode="w")
                    used = 0
                member = f"chunks/{file_number:08d}/{offset:016d}"
                info = tarfile.TarInfo(member)
                info.size, info.mode, info.mtime = len(chunk), 0o644, 0
                archive.addfile(info, io.BytesIO(chunk))
                current["entries"][member] = {
                    "file": name, "offset": offset, "bytes": len(chunk), "sha256": digest(chunk)}
                used += encoded_size
        finish()
    finally:
        if archive is not None:
            archive.close()
        if compressed is not None:
            compressed.close()
        if raw is not None:
            raw.close()
    return validate_layout({"schema": SCHEMA, "logical_files": logical, "archives": archives})


def unpack_parts(snapshot, layout, root, *, expected_hashes=None):
    snapshot, root = Path(snapshot), Path(root)
    validate_layout(layout, expected_hashes)
    require(root.is_dir() and not root.is_symlink() and not any(root.iterdir()),
            "Fresh empty evidence destination required")
    for description in layout["archives"]:
        source = snapshot / description["path"]
        require(not source.is_symlink() and source.stat().st_size == description["bytes"]
                and file_digest(source) == description["sha256"], "Archive bytes differ")
    offsets, hashes, started = {}, {}, set()
    for description in layout["archives"]:
        expected = list(description["entries"])
        count = 0
        # GzipFile decodes every concatenated member used by the complete
        # control writer; tarfile's streaming gzip decoder stops after one.
        with gzip.GzipFile(snapshot / description["path"], mode="rb") as decoded, \
                tarfile.open(fileobj=decoded, mode="r|", bufsize=STREAM_BUFFER_BYTES) as archive:
            for count, entry in enumerate(archive, 1):
                require(count <= len(expected) and entry.name == expected[count - 1]
                        and entry.isfile() and 0 <= entry.size <= MAX_ENTRY_BYTES,
                        "Unexpected bounded archive entry")
                fragment = description["entries"][entry.name]
                require(entry.size == fragment["bytes"], "Archive fragment size differs")
                data = archive.extractfile(entry).read()
                require(len(data) == fragment["bytes"] and digest(data) == fragment["sha256"],
                        "Archive fragment bytes differ")
                name = fragment["file"]
                require(fragment["offset"] == offsets.get(name, 0), "Fragment order differs")
                target = root / safe_path(name)
                target.parent.mkdir(parents=True, exist_ok=True)
                with target.open("ab" if name in started else "xb") as destination:
                    destination.write(data)
                hashes.setdefault(name, hashlib.sha256()).update(data)
                offsets[name] = offsets.get(name, 0) + len(data)
                started.add(name)
        require(count == len(expected), "Missing archive fragments")
    require(started == set(layout["logical_files"]), "Missing evidence files")
    for name, row in layout["logical_files"].items():
        require(offsets[name] == row["bytes"] and hashes[name].hexdigest() == row["sha256"],
                "Reassembled logical evidence differs")
