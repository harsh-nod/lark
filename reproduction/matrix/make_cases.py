"""Independent paper-size scalar FP16 GEMM and batched GEMM programs."""

import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def create(case, language="hip", family="gemm", batch=1, m=64, k=256, n=512):
    case.mkdir(parents=True, exist_ok=False)
    entry = f"induction_{family}_{language}_{batch}_{m}_{k}_{n}"
    if family == "gemm":
        shapes = [[m, k], [k, n], [m, n]]
        ai, bi = f"(i / {n}) * {k} + j", f"j * {n} + i % {n}"
        if batch != 1:
            raise ValueError("gemm has no batch dimension")
    elif family == "bmm":
        shapes = [[batch, m, k], [batch, k, n], [batch, m, n]]
        ai = f"(i / {m * n}) * {m * k} + (((i / {n}) % {m}) * {k} + j)"
        bi = f"(i / {m * n}) * {k * n} + (j * {n} + i % {n})"
    else:
        raise ValueError("unknown matrix family")
    source = f"""extern "C" __global__ void {entry}(const __half* a, const __half* b, __half* out) {{
  int i = blockIdx.x;
  float acc = 0.0f;
  int j = 0;
  while(j < {k}) {{
    acc = acc + __half2float(a[{ai}]) * __half2float(b[{bi}]);
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
        "name": entry,
        "entry": entry,
        "language": language,
        "buffers": [
            {"name": name, "role": role, "shape": shape, "dtype": "float16"}
            for name, role, shape in zip(("a", "b", "out"), ("input", "input", "output"), shapes)
        ],
        "launch": {"grid": batch * m * n, "block": 1, "warp": 64 if language == "hip" else 32},
        "fuel": [4 * k + 6, 1, 1, 1],
    }
    (case / "task.json").write_text(json.dumps(task, indent=2) + "\n")


if __name__ == "__main__":
    for language in ("hip", "cuda"):
        create(ROOT / "cases" / language / "gemm", language)
        create(ROOT / "cases" / language / "bmm", language, "bmm", batch=32)
