"""Lossless schema-two false-control archives with immutable compression reuse.

Only copied control snapshots are rewritten. Unsafe logical names are retained
as control data so the trusted replay reader, rather than this writer, rejects
them. Every physical member remains bounded and has an opaque safe name.
"""

import errno
import gzip
import hashlib
import json
import os
from pathlib import Path
import shutil
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
        # A complete unchanged physical part can be shared as an immutable
        # regular file. Readers still hash and unpack every physical/logical
        # byte. Replacing a part always unlinks its old destination first, so
        # a later rewrite cannot modify the cache or another control snapshot.
        self._cache_directory = tempfile.TemporaryDirectory(prefix="lark-immutable-control-parts-")
        self._part_cache = {}
        _, parts = self.plan(self.entries)
        for index, fragments in enumerate(parts):
            path = Path(self._cache_directory.name) / storage.part_name(index + 1)
            binding = self.emit_part(path, fragments)
            path.chmod(0o444)
            self._part_cache[self.part_key(fragments)] = (path, binding)

    def close(self):
        """Release private cache names; complete linked controls keep their bytes."""
        self._cache_directory.cleanup()

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

    @staticmethod
    def part_key(fragments):
        # Immutable byte values are compared as well as hashed. Keys include
        # every logical binding, including deliberately unsafe control names.
        return tuple((member, tuple(binding.items()), compressed, size)
                     for member, binding, compressed, size in fragments)

    def plan(self, entries):
        logical, parts, current, used = {}, [], [], 0
        for name, data in sorted(entries.items()):
            unchanged = name in self.entries and data is self.entries[name]
            logical[name] = {"bytes": len(data),
                             "sha256": self.hashes[name] if unchanged else storage.digest(data)}
            fragments = self.fragments[name] if unchanged else self.encode(name, data)
            for fragment in fragments:
                if current and used + fragment[3] > self.tar_bytes:
                    parts.append(tuple(current))
                    current, used = [], 0
                current.append(fragment)
                used += fragment[3]
        if current:
            parts.append(tuple(current))
        return logical, parts

    def emit_part(self, path, fragments):
        digest, size = hashlib.sha256(), 0
        with path.open("wb") as output:
            for value in [*(fragment[2] for fragment in fragments), self.end]:
                output.write(value)
                digest.update(value)
                size += len(value)
        storage.require(size <= storage.MAX_ARCHIVE_BYTES, "Control archive exceeds storage bound")
        return {"bytes": size, "sha256": digest.hexdigest()}

    def write(self, snapshot, entries):
        snapshot = Path(snapshot)
        storage.require(snapshot.is_dir() and not snapshot.is_symlink()
                        and type(entries) is dict and bool(entries)
                        and all(type(n) is str and type(v) is bytes for n, v in entries.items()),
                        "Complete control byte mapping required")
        # Logical paths remain deliberately unvalidated: the complete traversal
        # payload must reach the independent trusted reader's refusal gate.
        logical, parts = self.plan(entries)
        layout = {"schema": 2, "logical_files": logical, "archives": []}
        for index, fragments in enumerate(parts):
            path = snapshot / storage.part_name(index + 1)
            storage.require(not path.is_symlink(), "Control archive destination is a symlink")
            if path.exists():
                path.unlink()
            cached = self._part_cache.get(self.part_key(fragments))
            if cached is None:
                binding = self.emit_part(path, fragments)
            else:
                source, binding = cached
                try:
                    os.link(source, path)
                except OSError as error:
                    if error.errno not in (errno.EXDEV, errno.EPERM, errno.EACCES, errno.ENOSYS,
                                           errno.EOPNOTSUPP):
                        raise
                    shutil.copyfile(source, path)
            members = {}
            for member, row, _, _ in fragments:
                storage.require(member not in members, "Duplicate opaque control fragment")
                members[member] = row.copy()
            layout["archives"].append({"path": path.name, "entries": members, **binding})
        generated = {row["path"] for row in layout["archives"]}
        for previous in snapshot.glob("evidence-part-*.tar.gz"):
            if previous.name not in generated:
                previous.unlink()
        write(snapshot / "evidence-layout.json", layout)
        write(snapshot / "evidence-manifest.json", {n: row["sha256"]
                                                   for n, row in layout["logical_files"].items()})
        return layout
