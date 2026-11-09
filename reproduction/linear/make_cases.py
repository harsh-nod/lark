"""Independent paper-size FP16 scalar Linear with broadcast bias."""

import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def create(case, language="hip", m=64, k=256, n=512):
    case.mkdir(parents=True, exist_ok=False)
    entry = f"induction_linear_{language}_{m}_{k}_{n}"
    source = f"""extern "C" __global__ void {entry}(const __half* a, const __half* b, const __half* bias, __half* out) {{
  int i = blockIdx.x;
  float acc = 0.0f;
  int j = 0;
  while(j < {k}) {{
    acc = acc + __half2float(a[(i / {n}) * {k} + j]) * __half2float(b[j * {n} + i % {n}]);
    j++;
  }}
  out[i] = __float2half(acc + __half2float(bias[i % {n}]));
}}
"""
    (case / ("kernel.hip" if language == "hip" else "kernel.cu")).write_text(source)
    (case / "reference.py").write_text(
        "import torch\n\n\ndef reference(a, b, bias):\n    return (a.float() @ b.float() + bias.float()).half()\n"
    )
    task = {
        "name": entry,
        "entry": entry,
        "language": language,
        "buffers": [
            {"name": name, "role": role, "shape": shape, "dtype": "float16"}
            for name, role, shape in [
                ("a", "input", [m, k]),
                ("b", "input", [k, n]),
                ("bias", "input", [n]),
                ("out", "output", [m, n]),
            ]
        ],
        "launch": {"grid": m * n, "block": 1, "warp": 64 if language == "hip" else 32},
        "fuel": [4 * k + 6, 1, 1, 1],
    }
    (case / "task.json").write_text(json.dumps(task, indent=2) + "\n")


if __name__ == "__main__":
    for language in ("hip", "cuda"):
        create(ROOT / "cases" / language, language)
