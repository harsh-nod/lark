"""Load finite FP16 probes from a hash-bound binary file without Python float lists."""

import hashlib
import json
from pathlib import Path
import struct


class PackedHalf:
    def __init__(self, payload):
        if len(payload) % 2:
            raise RuntimeError("Odd FP16 payload length")
        self.payload = payload

    def __len__(self):
        return len(self.payload) // 2

    def __iter__(self):
        return (x[0] for x in struct.iter_unpack("<e", self.payload))


def load_dataset(root):
    root = Path(root)
    data = json.loads((root / "cases.json").read_text())
    payload = (root / "tensors.f16").read_bytes()
    if hashlib.sha256(payload).hexdigest() != data["tensor_data_sha256"]:
        raise RuntimeError("Binary probe data hash differs")
    view = memoryview(payload)

    def values(record):
        start, size = record["offset"], record["bytes"]
        if (
            type(start) is not int
            or type(size) is not int
            or start < 0
            or size < 0
            or start + size > len(view)
        ):
            raise RuntimeError("Invalid binary probe extent")
        part = view[start : start + size]
        if hashlib.sha256(part).hexdigest() != record["sha256"]:
            raise RuntimeError("Binary probe extent hash differs")
        return PackedHalf(part)

    for row in data["cases"]:
        for trial in row["trials"]:
            for b in trial["buffers"]:
                b["values"] = values(b["packed"]) if b["role"] == "input" else None
            trial["expected"] = values(trial["expected_packed"])
    return data
