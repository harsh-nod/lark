"""Scalar four-launch SwiGLU preserving FP32 projections before FP16 storage."""

import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from lark_kernels.swiglu import reference_expression

ROOT = Path(__file__).resolve().parent


def create(case, language="hip", m=64, k=256, h=1024, n=256):
    case.mkdir(parents=True, exist_ok=False)
    for stage, rows, reduction, cols, names, out_dtype in (
        ("gate", m, k, h, ("x", "wgate", "gate"), "float32"),
        ("up", m, k, h, ("x", "wup", "up"), "float32"),
        ("down", m, h, n, ("hidden", "down", "out"), "float16"),
    ):
        a, b, out = names
        entry = f"swiglu_{stage}_{language}_{m}_{k}_{h}_{n}"
        out_type = "float" if out_dtype == "float32" else "__half"
        value = "acc" if out_dtype == "float32" else "__float2half(acc)"
        source = f"""extern "C" __global__ void {entry}(const __half* {a}, const __half* {b}, {out_type}* {out}) {{
  int i = blockIdx.x;
  float acc = 0.0f;
  int j = 0;
  while(j < {reduction}) {{
    acc = acc + __half2float({a}[(i / {cols}) * {reduction} + j]) * __half2float({b}[j * {cols} + i % {cols}]);
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
                {"name": name, "role": role, "shape": shape, "dtype": dtype}
                for name, role, shape, dtype in zip(
                    names,
                    ("input", "input", "output"),
                    ([rows, reduction], [reduction, cols], [rows, cols]),
                    ("float16", "float16", out_dtype),
                )
            ],
            "launch": {"grid": rows * cols, "block": 1, "warp": 64 if language == "hip" else 32},
            "fuel": [4 * reduction + 6, 1, 1, 1],
        }
        (case / (stage + (".hip" if language == "hip" else ".cu"))).write_text(source)
        (case / (stage + "-task.json")).write_text(json.dumps(task, indent=2) + "\n")
    entry = f"swiglu_combine_{language}_{m}_{k}_{h}_{n}"
    source = f"""extern "C" __global__ void {entry}(const float* gate, const float* up, __half* hidden) {{
  int i = blockIdx.x;
  float a = gate[i];
  float b = up[i];
  hidden[i] = __float2half((a * (1.0f / (1.0f + expf(0.0f - a)))) * b);
}}
"""
    (case / ("combine" + (".hip" if language == "hip" else ".cu"))).write_text(source)
    task = {
        "name": entry,
        "entry": entry,
        "language": language,
        "buffers": [
            {"name": name, "role": role, "shape": [m, h], "dtype": dtype}
            for name, role, dtype in (
                ("gate", "input", "float32"),
                ("up", "input", "float32"),
                ("hidden", "output", "float16"),
            )
        ],
        "launch": {"grid": m * h, "block": 1, "warp": 64 if language == "hip" else 32},
        "fuel": [5, 1, 1, 1],
    }
    (case / "combine-task.json").write_text(json.dumps(task, indent=2) + "\n")
    (case / "reference.py").write_text(
        "import torch\n\n\ndef reference(x, wgate, wup, down):\n    return "
        + reference_expression()
        + "\n"
    )


if __name__ == "__main__":
    for language in ("hip", "cuda"):
        create(ROOT / "cases" / language, language)
