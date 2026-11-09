"""Independent reduced fixtures; no original paper programs are implied."""

import json
from pathlib import Path
import re
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from reproduction.catalog import NAMES

ROOT = Path(__file__).resolve().parent


def put(name, inputs, output, body, reference, threads, dtype):
    case = ROOT / "cases" / dtype / name
    case.mkdir(parents=True, exist_ok=True)
    if dtype == "float16":
        for arg, _ in inputs:
            body = re.sub(r"\b" + arg + r"\[([^\]]+)\]", r"__half2float(" + arg + r"[\1])", body)
        body = re.sub(r"out\[([^\]]+)\]\s*=\s*([^;]+);", r"out[\1] = __float2half(\2);", body)
        reference = re.sub(
            r"\b(" + "|".join(arg for arg, _ in inputs) + r")\b", r"\1.float()", reference
        )
        reference = "(" + reference + ").half()"
    ty = "__half" if dtype == "float16" else "float"
    params = ", ".join([f"const {ty}* {a}" for a, _ in inputs] + [f"{ty}* out"])
    entry = "nonlinear_" + name + "_" + dtype
    (case / "kernel.hip").write_text(
        f'extern "C" __global__ void {entry}({params}) {{\n{body.strip()}\n}}\n'
    )
    (case / "reference.py").write_text(
        "import torch\n\ndef reference("
        + ", ".join(a for a, _ in inputs)
        + "):\n    return "
        + reference
        + "\n"
    )
    task = {
        "name": name + "_" + dtype,
        "entry": entry,
        "language": "hip",
        "buffers": [{"name": a, "role": "input", "shape": s, "dtype": dtype} for a, s in inputs]
        + [{"name": "out", "role": "output", "shape": output, "dtype": dtype}],
        "launch": {"grid": 1, "block": threads, "warp": 64},
        "fuel": [1024, 16, 16, 16],
    }
    (case / "task.json").write_text(json.dumps(task, indent=2) + "\n")


def main():
    new = {
        "silu": (
            "int i = threadIdx.x; float v = x[i]; out[i] = v * (1.0f / (1.0f + expf(0.0f - v)));",
            "torch.nn.functional.silu(x)",
        ),
        "gelu": (
            "int i = threadIdx.x; float v = x[i]; out[i] = 0.5f * v * (1.0f + tanhf(0.7978845608028654f * (v + 0.044715f * v * v * v)));",
            'torch.nn.functional.gelu(x, approximate="tanh")',
        ),
        "softmax": (
            """__shared__ float staged[4]; __shared__ float weights[4];
int i = threadIdx.x; staged[i] = x[i]; __syncthreads();
float maximum = staged[0]; int j = 1;
while(j < 4) { maximum = fmaxf(maximum, staged[j]); j++; }
weights[i] = expf(x[i] - maximum); __syncthreads();
float total = 0.0f; int k = 0;
while(k < 4) { total = total + weights[k]; k++; }
out[i] = weights[i] / total;""",
            "torch.softmax(x, dim=0)",
        ),
        "layernorm": (
            """__shared__ float staged[4]; int i = threadIdx.x;
staged[i] = x[i]; __syncthreads();
float total = 0.0f; int j = 0;
while(j < 4) { total = total + staged[j]; j++; }
float mean = total / 4.0f; float variance = 0.0f; int k = 0;
while(k < 4) { float delta = staged[k] - mean; variance = variance + delta * delta; k++; }
variance = variance / 4.0f;
out[i] = (x[i] - mean) * rsqrtf(variance + 1e-5f);""",
            "torch.nn.functional.layer_norm(x, (4,), eps=1e-5)",
        ),
        "rmsnorm": (
            """__shared__ float staged[4]; int i = threadIdx.x;
staged[i] = x[i]; __syncthreads();
float total = 0.0f; int j = 0;
while(j < 4) { total = total + staged[j] * staged[j]; j++; }
out[i] = x[i] * rsqrtf(total / 4.0f + 1e-5f);""",
            "torch.nn.functional.rms_norm(x, (4,), eps=1e-5)",
        ),
    }
    for name, (body, reference) in new.items():
        for dtype in ("float32", "float16"):
            put(name, [("x", [4])], [4], body, reference, 4, dtype)
    for name in NAMES[:12]:
        if name in new:
            continue
        case = ROOT.parent / "cases" / name
        task = json.loads((case / "task.json").read_text())
        source = (case / "kernel.hip").read_text()
        body = source[source.index("{") + 1 : source.rindex("}")]
        expression = (case / "reference.py").read_text().split("return ", 1)[1].strip()
        inputs = [(b["name"], b["shape"]) for b in task["buffers"] if b["role"] == "input"]
        output = next(b["shape"] for b in task["buffers"] if b["role"] == "output")
        put(name, inputs, output, body, expression, task["launch"]["block"], "float16")
    put(
        "rope",
        [("x", [2, 4]), ("cosine", [2, 2]), ("sine", [2, 2])],
        [2, 4],
        """int p = threadIdx.x; int i = p * 2;
float a = x[i]; float b = x[i + 1];
out[i] = a * cosine[p] - b * sine[p];
out[i + 1] = a * sine[p] + b * cosine[p];""",
        "torch.stack((x.reshape(2,2,2).select(2,0)*cosine-x.reshape(2,2,2).select(2,1)*sine, x.reshape(2,2,2).select(2,0)*sine+x.reshape(2,2,2).select(2,1)*cosine), dim=-1).reshape(2,4)",
        4,
        "float16",
    )
    for name in ("ffn", "swiglu"):
        inputs = [("x", [1, 2]), ("w1", [2, 2])]
        if name == "swiglu":
            inputs.append(("up", [2, 2]))
        inputs.append(("down", [2, 2]))
        gate = "fmaxf(a, 0.0f)" if name == "ffn" else "(a * (1.0f / (1.0f + expf(0.0f - a)))) * u"
        body = """int t = threadIdx.x; float result = 0.0f; int j = 0;
while(j < 2) { float a = 0.0f; float u = 0.0f; int k = 0;
while(k < 2) { a = a + x[k] * w1[k * 2 + j]; UP k++; }
float h = __half2float(__float2half(GATE)); result = result + h * down[j * 2 + t]; j++; }
out[t] = result;""".replace(
            "UP", "u = u + x[k] * up[k * 2 + j];" if name == "swiglu" else ""
        ).replace("GATE", gate)
        expression = (
            "((x @ w1).relu().half().float() @ down)"
            if name == "ffn"
            else "((torch.nn.functional.silu(x @ w1) * (x @ up)).half().float() @ down)"
        )
        put(name, inputs, [1, 2], body, expression, 2, "float16")
    for name in ("flash_attn", "gqa"):
        grouped = name == "gqa"
        qshape = [2, 2, 1] if grouped else [2, 4]
        kvshape = [1, 2, 1] if grouped else [2, 4]
        body = """int r = threadIdx.x; int head = r / 2; int row = r % 2;
float score0 = 0.0f; float score1 = 0.0f; int k = 0;
while(k < 4) { score0 = score0 + q[(head * 2 + row) * 4 + k] * key[k];
score1 = score1 + q[(head * 2 + row) * 4 + k] * key[4 + k]; k++; }
score0 = score0 / 2.0f; score1 = score1 / 2.0f;
float maximum = fmaxf(score0, score1); float e0 = expf(score0 - maximum); float e1 = expf(score1 - maximum);
float denominator = 0.0f + e0 + e1;
int col = 0;
while(col < 4) { float result = 0.0f + (e0 / denominator) * value[col];
result = result + (e1 / denominator) * value[4 + col]; out[(head * 2 + row) * 4 + col] = result; col++; }"""
        expression = "((q @ key.transpose(0,1)) / 2.0).softmax(dim=1) @ value"
        if grouped:
            expression = "((q @ key.repeat_interleave(2,dim=0).transpose(1,2)) / 2.0).softmax(dim=2) @ value.repeat_interleave(2,dim=0)"
        if grouped:
            body = body.replace("4", "1").replace(" / 2.0f", " / 1.0f")
            expression = expression.replace(" / 2.0", " / 1.0")
        put(
            name,
            [("q", qshape), ("key", kvshape), ("value", kvshape)],
            qshape,
            body,
            expression,
            4 if grouped else 2,
            "float16",
        )


if __name__ == "__main__":
    main()
