"""Full-length pointwise sources for the induction proof's one-thread-block profile."""

import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
BODIES = {
    "relu": ("fmaxf(v, 0.0f)", "x.float().relu().half()"),
    "silu": (
        "v * (1.0f / (1.0f + expf(0.0f - v)))",
        "torch.nn.functional.silu(x.float()).half()",
    ),
    "gelu": (
        "0.5f * v * (1.0f + tanhf(0.7978845608028654f * (v + 0.044715f * v * v * v)))",
        'torch.nn.functional.gelu(x.float(), approximate="tanh").half()',
    ),
}


def create(case, family, language="hip", n=16384):
    case.mkdir(parents=True, exist_ok=False)
    expr, ref = BODIES[family]
    entry = f"pointwise_{family}_{language}"
    source = f"""extern "C" __global__ void {entry}(const __half* x, __half* out) {{
  int i = blockIdx.x;
  float v = __half2float(x[i]);
  out[i] = __float2half({expr});
}}
"""
    (case / ("kernel.hip" if language == "hip" else "kernel.cu")).write_text(source)
    (case / "reference.py").write_text(
        "import torch\n\ndef reference(x):\n    return " + ref + "\n"
    )
    task = {
        "name": f"pointwise_{family}_{language}_{n}",
        "entry": entry,
        "language": language,
        "buffers": [
            {"name": name, "role": role, "shape": [n], "dtype": "float16"}
            for name, role in [("x", "input"), ("out", "output")]
        ],
        "launch": {"grid": n, "block": 1, "warp": 64 if language == "hip" else 32},
        "fuel": [4, 1, 1, 1],
    }
    (case / "task.json").write_text(json.dumps(task, indent=2) + "\n")


if __name__ == "__main__":
    for language in ("hip", "cuda"):
        for family in BODIES:
            create(ROOT / "cases" / language / family, family, language)
