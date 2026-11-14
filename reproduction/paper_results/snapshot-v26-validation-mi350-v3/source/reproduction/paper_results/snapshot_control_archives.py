"""Lossless schema-two false-control archives with immutable compression reuse.

Only copied control snapshots are rewritten. Unsafe logical names are retained
as control data so the trusted replay reader, rather than this writer, rejects
them. Every physical member remains bounded and has an opaque safe name.
"""

import gzip
import hashlib
import json
from pathlib import Path
import tarfile
import tempfile

if __package__:
    from . import snapshot_archives as storage
else:
    import snapshot_archives as storage


def write(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n")


class ChunkedControlArchive:
    def __init__(self, snapshot, *, chunk_bytes=storage.MAX_ENTRY_BYTES, tar_bytes=storage.MAX_TAR_BYTES):
        self.snapshot = Path(snapshot)
        storage.require(type(chunk_bytes) is int and 0 < chunk_bytes <= storage.MAX_ENTRY_BYTES
                        and type(tar_bytes) is int and 1024 <= tar_bytes <= storage.MAX_TAR_BYTES,
                        "Existing control archive bounds required")
        self.chunk_bytes, self.tar_bytes = chunk_bytes, tar_bytes
        layout = json.loads((self.snapshot / "evidence-layout.json").read_text())
        hashes = json.loads((self.snapshot / "evidence-manifest.json").read_text())
        with tempfile.TemporaryDirectory(prefix="lark-complete-control-baseline-") as temporary:
            root = Path(temporary)
            storage.unpack_parts(self.snapshot, layout, root, expected_hashes=hashes)
            self.entries = {name: (root / name).read_bytes() for name in layout["logical_files"]}
        self.hashes = hashes
        self.fragments = {name: tuple(self.encode(name, data)) for name, data in self.entries.items()}
        self.end = gzip.compress(b"\0" * 1024, compresslevel=1, mtime=0)

    def encode(self, name, data):
        # IDs depend on logical names, preserving immutable compression reuse
        # even when a control adds a name or changes dictionary insertion order.
        identifier = hashlib.sha256(name.encode()).hexdigest()
        offsets = range(0, len(data), self.chunk_bytes) if data else (0,)
        for offset in offsets:
            value = data[offset:offset + self.chunk_bytes]
            member = "chunks/" + identifier + f"/{offset:016d}"
            info = tarfile.TarInfo(member)
            info.size, info.mode, info.mtime = len(value), 0o644, 0
            payload = info.tobuf(format=tarfile.USTAR_FORMAT) + value + b"\0" * ((-len(value)) % 512)
            storage.require(len(payload) <= self.tar_bytes, "Bounded control chunk exceeds the part budget")
            yield member, {"file": name, "offset": offset, "bytes": len(value),
                           "sha256": storage.digest(value)}, gzip.compress(payload, compresslevel=1, mtime=0), len(payload)

    def write(self, snapshot, entries):
        snapshot = Path(snapshot)
        storage.require(snapshot.is_dir() and not snapshot.is_symlink()
                        and type(entries) is dict and bool(entries)
                        and all(type(n) is str and type(v) is bytes for n, v in entries.items()),
                        "Complete control byte mapping required")
        # Deliberately do not validate logical paths here: the traversal control
        # must retain its malicious bytes for the actual trusted reader to refuse.
        layout = {"schema": 2, "logical_files": {}, "archives": []}
        output = current = archive_hash = None
        used = archive_bytes = 0

        def emit(value):
            nonlocal archive_bytes
            output.write(value)
            archive_hash.update(value)
            archive_bytes += len(value)

        def finish():
            nonlocal output
            if output is None:
                return
            emit(self.end)
            output.close()
            output = None
            storage.require(archive_bytes <= storage.MAX_ARCHIVE_BYTES, "Control archive exceeds storage bound")
            current.update(bytes=archive_bytes, sha256=archive_hash.hexdigest())

        try:
            for name, data in sorted(entries.items()):
                unchanged = name in self.entries and data is self.entries[name]
                digest = self.hashes[name] if unchanged else storage.digest(data)
                layout["logical_files"][name] = {"bytes": len(data), "sha256": digest}
                fragments = self.fragments[name] if unchanged else self.encode(name, data)
                for member, binding, compressed, size in fragments:
                    if output is None or used + size > self.tar_bytes:
                        finish()
                        current = {"path": storage.part_name(len(layout["archives"]) + 1), "entries": {}}
                        layout["archives"].append(current)
                        output = (snapshot / current["path"]).open("wb")
                        used, archive_bytes = 0, 0
                        archive_hash = hashlib.sha256()
                    emit(compressed)
                    storage.require(member not in current["entries"], "Duplicate opaque control fragment")
                    current["entries"][member] = binding.copy()
                    used += size
            finish()
        finally:
            if output is not None:
                output.close()
        generated = {row["path"] for row in layout["archives"]}
        for previous in snapshot.glob("evidence-part-*.tar.gz"):
            if previous.name not in generated:
                previous.unlink()
        write(snapshot / "evidence-layout.json", layout)
        write(snapshot / "evidence-manifest.json", {n: row["sha256"]
                                                   for n, row in layout["logical_files"].items()})
        return layout
