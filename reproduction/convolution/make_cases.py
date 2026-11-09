"""Independent valid square FP16 NCHW convolution fixtures at paper dimensions."""

import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from lark_kernels.convolution import reference_expression

ROOT = Path(__file__).resolve().parent


def create(case, language="hip", family="conv2d", cin=32, cout=8, h=8, k=3):
    if family == "depthwise_conv":
        cout = cin
    elif family != "conv2d" or (cin == cout == 1):
        raise ValueError("use distinct dense/depthwise fixture shapes")
    case.mkdir(parents=True, exist_ok=False)
    side = h - k + 1
    cw = 1 if family == "depthwise_conv" else cin
    reduce = cw * k * k
    channel = f"t / {side * side}" if family == "depthwise_conv" else f"j / {k * k}"
    a_index = f"((({channel}) * {h} + (t / {side}) % {side} + (j / {k}) % {k}) * {h} + t % {side} + j % {k})"
    b_index = f"(t / {side * side}) * {reduce} + j"
    entry = f"induction_{family}_{language}_{cin}_{cout}_{h}_{k}"
    source = f"""extern "C" __global__ void {entry}(const __half* x, const __half* w, __half* out) {{
  int t = blockIdx.x;
  float acc = 0.0f;
  int j = 0;
  while(j < {reduce}) {{
    acc = acc + __half2float(x[{a_index}]) * __half2float(w[{b_index}]);
    j++;
  }}
  out[t] = __float2half(acc);
}}
"""
    (case / ("kernel.hip" if language == "hip" else "kernel.cu")).write_text(source)
    expression = reference_expression(("x", "w"), cin if family == "depthwise_conv" else 1)
    (case / "reference.py").write_text(
        "import torch\n\n\ndef reference(x, w):\n    return " + expression + "\n"
    )
    task = {
        "name": entry,
        "entry": entry,
        "language": language,
        "buffers": [
            {"name": name, "role": role, "shape": shape, "dtype": "float16"}
            for name, role, shape in [
                ("x", "input", [1, cin, h, h]),
                ("w", "input", [cout, cw, k, k]),
                ("out", "output", [1, cout, side, side]),
            ]
        ],
        "launch": {"grid": cout * side * side, "block": 1, "warp": 64 if language == "hip" else 32},
        "fuel": [4 * reduce + 6, 1, 1, 1],
    }
    (case / "task.json").write_text(json.dumps(task, indent=2) + "\n")


if __name__ == "__main__":
    for language in ("hip", "cuda"):
        create(ROOT / "cases" / language / "conv2d", language)
        create(
            ROOT / "cases" / language / "depthwise_conv",
            language,
            "depthwise_conv",
            cin=32,
            h=16,
            k=5,
        )
