"""Prepare finite tests of the unchanged upstream FP32 online-attention kernel.

Inputs are half-representable values carried in float32 buffers. This is not
the paper's FP16-storage adaptation, a source certificate or an IEEE theorem.
"""

import argparse
import hashlib
import json
import math
from pathlib import Path
import shutil

HERE = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    provenance = json.loads((HERE / "provenance.json").read_text())
    if sha(HERE / "upstream/flash.cu") != provenance["source_sha256"]:
        raise ValueError("Pinned upstream source differs")
    if sha(HERE / "upstream/LICENSE") != provenance["license_sha256"]:
        raise ValueError("Pinned upstream license differs")
    for name in ("flash.cu", "LICENSE"):
        shutil.copyfile(HERE / "upstream" / name, out / name)
    for name in ("driver.hip", "run_gpu.py", "prepare_gpu.py", "provenance.json"):
        shutil.copyfile(HERE / name, out / name)
    text = (out / "flash.cu").read_text()
    start = text.index("__global__")
    end = text.index("\ntorch::Tensor forward(", start)
    kernel = text[start:end]
    (out / "upstream_context.cuh").write_text(kernel)
    import numpy as np
    import torch

    torch.set_num_threads(1)
    meta = {
        "schema": 1, "seed": 261102028, "torch": torch.__version__,
        "torch_git_commit": torch.version.git_version, "numpy": np.__version__,
        "input_storage": "float32 with half-representable values",
        "reference": "CPU Torch float64: softmax(Q @ K.T / sqrt(d)) @ V",
        "atol": 0.0001, "rtol": 0.0002, "cases": [],
        "upstream_definition_sha256": hashlib.sha256(kernel.encode()).hexdigest(),
        "kernel_definition_unchanged": True, "tile": 32,
        "source_certificates": 0, "whole_kernel_execution_proved": False,
        "race_freedom_proved": False, "ieee_equivalence_proved": False,
        "model_calls": 0, "original_paper_fully_reproduced": False,
        "scope": "Independent finite AMD validation of the upstream FP32 kernel; not the paper's FP16 rewrite, original model result or H100 timing.",
    }
    streams = {name: bytearray() for name in ("q", "k", "v", "expected")}
    offset = 0
    for batch, heads, n, d in ((1, 1, 32, 32), (1, 1, 64, 64), (1, 1, 128, 256), (2, 3, 64, 64)):
        shape = (batch, heads, n, d)
        count = math.prod(shape)
        rng = torch.Generator().manual_seed(meta["seed"] + count)
        index = torch.arange(count, dtype=torch.int64).reshape(shape)
        labels = ("seeded-normal", "zero-scores", "constant-scores", "alternating", "sharp", "large-common-score-shift")
        for family in labels:
            q = torch.randn(shape, generator=rng).mul(0.5)
            k = torch.randn(shape, generator=rng).mul(0.5)
            v = torch.randn(shape, generator=rng).mul(0.5)
            if family == "zero-scores":
                q.zero_(); k.zero_()
            elif family == "constant-scores":
                q.fill_(0.25); k.fill_(-0.5)
                v = ((index * 7) % 31 - 15).float().div(8)
            elif family == "alternating":
                q = ((index * 5) % 23 - 11).float().div(4)
                k = ((index * 7) % 29 - 14).float().div(4)
                v = ((index * 11) % 37 - 18).float().div(8)
            elif family == "sharp":
                q.mul_(8); k.mul_(8)
            elif family == "large-common-score-shift":
                q.fill_(8)
                k = torch.full(shape, 16.0) + (index % 3).float().div(16)
            q, k, v = (x.half().float().contiguous() for x in (q, k, v))
            score = (q.double() @ k.double().transpose(-1, -2)) / math.sqrt(d)
            expected = (score.softmax(dim=-1) @ v.double()).contiguous()
            if not torch.isfinite(expected).all():
                raise ValueError("Nonfinite reference")
            for name, tensor in (("q", q), ("k", k), ("v", v), ("expected", expected)):
                streams[name].extend(tensor.numpy().astype("<f8" if name == "expected" else "<f4").tobytes())
            meta["cases"].append({
                "batch": batch, "heads": heads, "n": n, "d": d, "family": family,
                "elements": count, "rows": batch * heads * n, "offset_elements": offset,
                "grid": [batch, heads], "block": 32,
                "shared_bytes": (3 * 32 * d + 32 * 32) * 4,
                "reference_score_min": float(score.min()), "reference_score_max": float(score.max()),
            })
            offset += count
    for name, content in streams.items():
        (out / (name + ".bin")).write_bytes(content)
    write(out / "dataset.json", meta)
    write(out / "manifest.json", {p.name: sha(p) for p in sorted(out.iterdir()) if p.is_file()})
    print(json.dumps({"cases": len(meta["cases"]), "output_values_per_host": offset,
                      "source_certificates": 0, "model_calls": 0}))


if __name__ == "__main__":
    main()
