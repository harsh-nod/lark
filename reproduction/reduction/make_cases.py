"""Independent FP16 scalar GEMV at the paper's full [512,1024] matrix shape."""

import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def create(case, language="hip", n=512, k=1024):
    case.mkdir(parents=True, exist_ok=False)
    entry = f"induction_gemv_{language}_{n}_{k}"
    source = f"""extern "C" __global__ void {entry}(const __half* a, const __half* b, __half* out) {{
  int i = blockIdx.x;
  float acc = 0.0f;
  int j = 0;
  while(j < {k}) {{
    acc = acc + __half2float(a[i * {k} + j]) * __half2float(b[j]);
    j++;
  }}
  out[i] = __float2half(acc);
}}
"""
    (case / ("kernel.hip" if language == "hip" else "kernel.cu")).write_text(source)
    (case / "reference.py").write_text(
        "import torch\n\ndef reference(a, b):\n    return (a.float() @ b.float()).half()\n"
    )
    task = {
        "name": f"gemv_{language}_{n}_{k}",
        "entry": entry,
        "language": language,
        "buffers": [
            {"name": name, "role": role, "shape": shape, "dtype": "float16"}
            for name, role, shape in [
                ("a", "input", [n, k]),
                ("b", "input", [k, 1]),
                ("out", "output", [n, 1]),
            ]
        ],
        "launch": {"grid": n, "block": 1, "warp": 64 if language == "hip" else 32},
        "fuel": [4 * k + 6, 1, 1, 1],
    }
    (case / "task.json").write_text(json.dumps(task, indent=2) + "\n")


if __name__ == "__main__":
    for language in ("hip", "cuda"):
        create(ROOT / "cases" / language, language)
