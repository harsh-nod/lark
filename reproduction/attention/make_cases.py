"""Three scalar kernels for noncausal dense SDPA and grouped-query contracts."""

import json
import math
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from lark_kernels.attention import reference_expression

ROOT = Path(__file__).resolve().parent


def create(case, language="hip", kv_heads=1, groups=1, seq=128, dim=256):
    case.mkdir(parents=True, exist_ok=False)
    hq = kv_heads * groups
    scale = math.isqrt(dim)
    if scale * scale != dim:
        raise ValueError("integer square-root scale required")
    stem = f"attention_{language}_{kv_heads}_{groups}_{seq}_{dim}"
    for stage in ("score", "value"):
        entry = stem + "_" + stage
        if stage == "score":
            a, b, out = "q", "k", "scores"
            red = dim
            count = hq * seq * seq
            ai = f"(i / {seq * seq}) * {seq * dim} + (((i / {seq}) % {seq}) * {dim} + j)"
            bi = f"((i / {seq * seq}) / {groups}) * {seq * dim} + ((i % {seq}) * {dim} + j)"
            a_type, b_type, out_type = "__half", "__half", "float"
            left = f"__half2float(q[{ai}])"
            right = f"__half2float(k[{bi}])"
            value = f"acc / {scale}.0f"
            shapes = ([hq, seq, dim], [kv_heads, seq, dim], [hq, seq, seq])
            dtypes = ("float16", "float16", "float32")
        else:
            a, b, out = "probabilities", "v", "out"
            red = seq
            count = hq * seq * dim
            ai = f"(i / {seq * dim}) * {seq * seq} + (((i / {dim}) % {seq}) * {seq} + j)"
            bi = f"((i / {seq * dim}) / {groups}) * {seq * dim} + (j * {dim} + i % {dim})"
            a_type, b_type, out_type = "float", "__half", "__half"
            left = f"probabilities[{ai}]"
            right = f"__half2float(v[{bi}])"
            value = "__float2half(acc)"
            shapes = ([hq, seq, seq], [kv_heads, seq, dim], [hq, seq, dim])
            dtypes = ("float32", "float16", "float16")
        source = f"""extern "C" __global__ void {entry}(const {a_type}* {a}, const {b_type}* {b}, {out_type}* {out}) {{
  int i = blockIdx.x;
  float acc = 0.0f;
  int j = 0;
  while(j < {red}) {{
    acc = acc + {left} * {right};
    j++;
  }}
  {out}[i] = {value};
}}
"""
        task = {
            "name": entry,
            "entry": entry,
            "language": language,
            "buffers": [
                {"name": n, "role": r, "shape": s, "dtype": d}
                for n, r, s, d in zip((a, b, out), ("input", "input", "output"), shapes, dtypes)
            ],
            "launch": {"grid": count, "block": 1, "warp": 64 if language == "hip" else 32},
            "fuel": [4 * red + 6, 1, 1, 1],
        }
        (case / (stage + (".hip" if language == "hip" else ".cu"))).write_text(source)
        (case / (stage + "-task.json")).write_text(json.dumps(task, indent=2) + "\n")
    entry = stem + "_softmax"
    ri = f"(i / {seq}) * {seq} + j"
    source = f"""extern "C" __global__ void {entry}(const float* scores, float* probabilities) {{
  int i = blockIdx.x;
  int j = 0;
  float acc = scores[{ri}];
  float ctx = 0.0f;
  float val = 0.0f;
  j = 1;
  while(j < {seq}) {{
    val = scores[{ri}];
    acc = fmaxf(acc, val);
    j++;
  }}
  ctx = acc;
  acc = 0.0f;
  j = 0;
  while(j < {seq}) {{
    val = scores[{ri}];
    acc = acc + expf(val - ctx);
    j++;
  }}
  val = scores[i];
  probabilities[i] = expf(val - ctx) / acc;
}}
"""
    (case / ("softmax" + (".hip" if language == "hip" else ".cu"))).write_text(source)
    task = {
        "name": entry,
        "entry": entry,
        "language": language,
        "buffers": [
            {"name": n, "role": r, "shape": [hq, seq, seq], "dtype": "float32"}
            for n, r in (("scores", "input"), ("probabilities", "output"))
        ],
        "launch": {"grid": hq * seq * seq, "block": 1, "warp": 64 if language == "hip" else 32},
        "fuel": [10 * seq + 9, 1, 1, 1],
    }
    (case / "softmax-task.json").write_text(json.dumps(task, indent=2) + "\n")
    (case / "reference.py").write_text(
        "import torch\n\n\ndef reference(q, k, v):\n    return "
        + reference_expression(groups, scale)
        + "\n"
    )


if __name__ == "__main__":
    for language in ("hip", "cuda"):
        create(ROOT / "cases/dense" / language, language)
        create(ROOT / "cases/gqa" / language, language, kv_heads=2, groups=4, dim=64)
