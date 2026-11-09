"""Independent FP16 interleaved RoPE at the paper's [256,128] shape."""

import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from lark_kernels.rotary import reference_expression

ROOT = Path(__file__).resolve().parent


def create(case, language="hip", m=256, d=128):
    case.mkdir(parents=True, exist_ok=False)
    entry = f"induction_rotary_{language}_{m}_{d}"
    source = f"""extern "C" __global__ void {entry}(const __half* x, const __half* cosine, const __half* sine, __half* out) {{
  int t = blockIdx.x;
  int i = (t / 2) * 2;
  float a = __half2float(x[i]);
  float b = __half2float(x[i + 1]);
  if(t % 2 == 0) {{
    out[t] = __float2half(a * __half2float(cosine[t / 2]) - b * __half2float(sine[t / 2]));
  }} else {{
    out[t] = __float2half(a * __half2float(sine[t / 2]) + b * __half2float(cosine[t / 2]));
  }}
}}
"""
    (case / ("kernel.hip" if language == "hip" else "kernel.cu")).write_text(source)
    expression = reference_expression(m, d, ("x", "cosine", "sine"))
    (case / "reference.py").write_text(
        "import torch\n\n\ndef reference(x, cosine, sine):\n    return " + expression + "\n"
    )
    task = {
        "name": entry,
        "entry": entry,
        "language": language,
        "buffers": [
            {"name": name, "role": role, "shape": shape, "dtype": "float16"}
            for name, role, shape in [
                ("x", "input", [m, d]),
                ("cosine", "input", [m, d // 2]),
                ("sine", "input", [m, d // 2]),
                ("out", "output", [m, d]),
            ]
        ],
        "launch": {"grid": m * d, "block": 1, "warp": 64 if language == "hip" else 32},
        "fuel": [8, 1, 1, 1],
    }
    (case / "task.json").write_text(json.dumps(task, indent=2) + "\n")


if __name__ == "__main__":
    for language in ("hip", "cuda"):
        create(ROOT / "cases" / language, language)
