"""Independent FP16 normalizations at the paper's length 16384."""

import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from lark_kernels.normalization import KINDS, lane_fuel, reference_expression

ROOT = Path(__file__).resolve().parent


def create(case, kind, language="hip", n=16384):
    case.mkdir(parents=True, exist_ok=False)
    entry = f"induction_{kind}_{language}_{n}"
    seed = "__half2float(x[0])" if kind == "softmax" else "0.0f"
    first = (
        "fmaxf(acc, val)"
        if kind == "softmax"
        else "acc + val * val"
        if kind == "rms"
        else "acc + val"
    )
    context = "acc" if kind == "softmax" else f"acc / {n}.0f"
    second = (
        "expf(val - ctx)"
        if kind == "softmax"
        else "(val - ctx) * (val - ctx)"
        if kind == "layer"
        else "val"
    )
    output = (
        "expf(val - ctx) / acc"
        if kind == "softmax"
        else f"(val - ctx) * rsqrtf(acc / {n}.0f + 0.00001f)"
        if kind == "layer"
        else "val * rsqrtf(ctx + 0.00001f)"
    )
    source = f"""extern "C" __global__ void {entry}(const __half* x, __half* out) {{
  int i = blockIdx.x;
  float acc = {seed};
  float ctx = 0.0f;
  float val = 0.0f;
  int j = {1 if kind == "softmax" else 0};
  while(j < {n}) {{
    val = __half2float(x[j]);
    acc = {first};
    j++;
  }}
  ctx = {context};
  acc = 0.0f;
  j = {n if kind == "rms" else 0};
  while(j < {n}) {{
    val = __half2float(x[j]);
    acc = acc + {second};
    j++;
  }}
  val = __half2float(x[i]);
  out[i] = __float2half({output});
}}
"""
    (case / ("kernel.hip" if language == "hip" else "kernel.cu")).write_text(source)
    (case / "reference.py").write_text(
        "import torch\n\n\ndef reference(x):\n    return " + reference_expression(kind) + "\n"
    )
    task = {
        "name": entry,
        "entry": entry,
        "language": language,
        "buffers": [
            {"name": name, "role": role, "shape": [n], "dtype": "float16"}
            for name, role in (("x", "input"), ("out", "output"))
        ],
        "launch": {"grid": n, "block": 1, "warp": 64 if language == "hip" else 32},
        "fuel": [lane_fuel(kind, n), 1, 1, 1],
    }
    (case / "task.json").write_text(json.dumps(task, indent=2) + "\n")


if __name__ == "__main__":
    for kind in KINDS:
        for language in ("hip", "cuda"):
            create(ROOT / "cases" / kind / language, kind, language)
