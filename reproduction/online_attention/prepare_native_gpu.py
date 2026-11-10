"""Freeze paired native FP16 and unchanged upstream FP32 online-attention tests.

No whole-source Lean certificate or source-rewrite equivalence is asserted.
"""

import argparse
import hashlib
import json
import math
from pathlib import Path
import shutil
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from lark_kernels import native_attention as native  # noqa: E402

HERE = Path(__file__).resolve().parent
CASE = HERE / "cases/native_fp16"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    task = native.parse_task((CASE / "task.json").read_text())
    native.check_reference((CASE / "reference.py").read_text(), task)
    tr = native.translate((CASE / "kernel.hip").read_text(), task)
    if tr.shared != [("qi", 8192), ("kj", 8192), ("vj", 8192), ("scores", 1024)] or tr.locals != [("running_m", 4), ("running_l", 4)]:
        raise ValueError("Native array layout differs")
    if len(tr.program) != 91:
        raise ValueError("Native program differs")
    for name in ("kernel.hip", "reference.py", "task.json"):
        shutil.copyfile(CASE / name, out / name)
    for name in ("native_driver.hip", "run_native_gpu.py", "prepare_native_gpu.py"):
        shutil.copyfile(HERE / name, out / name)
    shutil.copyfile(HERE / "driver.hip", out / "fp32_driver.hip")
    provenance = json.loads((HERE / "provenance.json").read_text())
    if sha(HERE / "upstream/flash.cu") != provenance["source_sha256"]:
        raise ValueError("Pinned upstream source differs")
    for name in ("flash.cu", "LICENSE"):
        shutil.copyfile(HERE / "upstream" / name, out / name)
    source = (out / "flash.cu").read_text()
    body = source[source.index("__global__"):source.index("\ntorch::Tensor forward(")]
    (out / "upstream_context.cuh").write_text(body)
    (out / "translation.json").write_text(json.dumps(tr.data(), indent=2) + "\n")
    import numpy as np
    import torch

    torch.set_num_threads(1)
    meta = {
        "schema": 1, "seed": 261102028, "torch": torch.__version__,
        "torch_git_commit": torch.version.git_version, "numpy": np.__version__,
        "reference": "CPU float64 softmax(Q @ K.T / 16) @ V using exact promoted FP16 inputs",
        "adapted_atol": 0.002, "adapted_rtol": 0.002,
        "upstream_atol": 0.0001, "upstream_rtol": 0.0002,
        "native_source_sha256": sha(out / "kernel.hip"),
        "upstream_definition_sha256": hashlib.sha256(body.encode()).hexdigest(),
        "source_certificates": 0, "whole_kernel_execution_proved": False,
        "actual_trace_classification_proved": False, "ieee_equivalence_proved": False,
        "model_calls": 0, "original_paper_fully_reproduced": False, "cases": [],
        "scope": "Independent native FP16-storage adaptation, not the authors' missing adapted source. Conditional footprint and source identity facts do not prove actual execution or RF.",
    }
    streams = {k: bytearray() for k in ("query", "key", "value", "qf", "kf", "vf", "expected")}
    offset = 0
    for groups in (1, 3):
        shape = (groups, 128, 256)
        count = math.prod(shape)
        rng = torch.Generator().manual_seed(meta["seed"] + count)
        index = torch.arange(count, dtype=torch.int64).reshape(shape)
        for family in ("seeded-normal", "zero-scores", "constant-scores", "alternating", "sharp", "large-common-score-shift"):
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
            q, k, v = (x.half().contiguous() for x in (q, k, v))
            score = (q.double() @ k.double().transpose(1, 2)) / 16
            expected = (score.softmax(dim=2) @ v.double()).contiguous()
            if not torch.isfinite(expected).all():
                raise ValueError("Nonfinite reference")
            for name, tensor in (("query", q), ("key", k), ("value", v),
                                 ("qf", q.float()), ("kf", k.float()), ("vf", v.float()),
                                 ("expected", expected)):
                dtype = "<f8" if name == "expected" else "<f4" if len(name) == 2 else "<f2"
                streams[name].extend(tensor.numpy().astype(dtype).tobytes())
            meta["cases"].append({"groups": groups, "n": 128, "d": 256, "tile": 32,
                                  "grid": groups, "block": 32, "family": family,
                                  "elements": count, "offset_elements": offset,
                                  "reference_score_min": float(score.min()),
                                  "reference_score_max": float(score.max())})
            offset += count
    for name, content in streams.items():
        (out / (name + ".bin")).write_bytes(content)
    write(out / "dataset.json", meta)
    write(out / "manifest.json", {p.name: sha(p) for p in sorted(out.iterdir()) if p.is_file()})
    print(json.dumps({"cases": len(meta["cases"]), "paired_outputs_per_host": offset,
                      "cpu_reference_comparisons_per_host": 2 * offset, "model_calls": 0}))


if __name__ == "__main__":
    main()
