"""Two scalar launches for the independent paper-size ReLU FFN contract."""

import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from lark_kernels.feedforward import reference_expression

ROOT = Path(__file__).resolve().parent


def create(case, language="hip", m=64, k=256, h=1024, n=256):
    case.mkdir(parents=True, exist_ok=False)
    for stage, rows, reduction, cols, names in (
        ("up", m, k, h, ("x", "w1", "hidden")),
        ("down", m, h, n, ("hidden", "down", "out")),
    ):
        entry = f"ffn_{stage}_{language}_{m}_{k}_{h}_{n}"
        a, b, out = names
        result = "fmaxf(acc, 0.0f)" if stage == "up" else "acc"
        source = f"""extern "C" __global__ void {entry}(const __half* {a}, const __half* {b}, __half* {out}) {{
  int i = blockIdx.x;
  float acc = 0.0f;
  int j = 0;
  while(j < {reduction}) {{
    acc = acc + __half2float({a}[(i / {cols}) * {reduction} + j]) * __half2float({b}[j * {cols} + i % {cols}]);
    j++;
  }}
  {out}[i] = __float2half({result});
}}
"""
        (case / (stage + (".hip" if language == "hip" else ".cu"))).write_text(source)
        task = {
            "name": entry,
            "entry": entry,
            "language": language,
            "buffers": [
                {"name": name, "role": role, "shape": shape, "dtype": "float16"}
                for name, role, shape in zip(
                    names,
                    ("input", "input", "output"),
                    ([rows, reduction], [reduction, cols], [rows, cols]),
                )
            ],
            "launch": {"grid": rows * cols, "block": 1, "warp": 64 if language == "hip" else 32},
            "fuel": [4 * reduction + 6, 1, 1, 1],
        }
        (case / (stage + "-task.json")).write_text(json.dumps(task, indent=2) + "\n")
    (case / "reference.py").write_text(
        "import torch\n\n\ndef reference(x, w1, down):\n    return " + reference_expression() + "\n"
    )


if __name__ == "__main__":
    for language in ("hip", "cuda"):
        create(ROOT / "cases" / language, language)
