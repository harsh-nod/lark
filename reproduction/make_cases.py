#!/usr/bin/env python3
"""Build independent reduced-shape proof cases for seven paper Level-1 families."""

import json
from pathlib import Path


ROOT = Path(__file__).resolve().parent


def put(name, inputs, shape, body, reference, threads, grid=1):
    p = ROOT / "cases" / name
    p.mkdir(parents=True, exist_ok=True)
    parameters = ", ".join([f"const float* {n}" for n, _ in inputs] + ["float* out"])
    (p / "kernel.hip").write_text(
        f'extern "C" __global__ void verify_{name}({parameters}) {{\n{body.strip()}\n}}\n'
    )
    (p / "reference.py").write_text(
        "import torch\n\ndef reference("
        + ", ".join(n for n, _ in inputs)
        + "):\n    "
        + reference
        + "\n"
    )
    buffers = [dict(name=n, role="input", shape=s, dtype="float32") for n, s in inputs]
    buffers.append(dict(name="out", role="output", shape=shape, dtype="float32"))
    task = dict(
        name="reduced_" + name,
        entry="verify_" + name,
        language="hip",
        buffers=buffers,
        launch=dict(grid=grid, block=threads, warp=64),
        fuel=[256, 16, 16, 16],
    )
    (p / "task.json").write_text(json.dumps(task, indent=2) + "\n")


def main():
    put(
        "relu",
        [("x", [4])],
        [4],
        """
int i = threadIdx.x;
while (i < 4) {
    float v = x[i];
    out[i] = fmaxf(v, 0.0f);
    i += blockDim.x;
}""",
        "return torch.relu(x)",
        2,
    )
    put(
        "gemv",
        [("a", [2, 3]), ("x", [3, 1])],
        [2, 1],
        """
int row = threadIdx.x;
int k = 0;
float acc = 0.0f;
while (k < 3) {
    acc = acc + a[row * 3 + k] * x[k];
    k++;
}
out[row] = acc;""",
        "return a @ x",
        2,
    )
    put(
        "gemm",
        [("a", [1, 2]), ("b", [2, 2])],
        [1, 2],
        """
__shared__ float staged_a[2];
__shared__ float staged_b[4];
int t = threadIdx.x;
staged_a[t] = a[t];
staged_b[t] = b[t];
staged_b[2 + t] = b[2 + t];
__syncthreads();
int k = 0;
float acc = 0.0f;
while (k < 2) {
    acc = acc + staged_a[k] * staged_b[k * 2 + t];
    k++;
}
out[t] = acc;""",
        "return a @ b",
        2,
    )
    put(
        "batchmatmul",
        [("a", [2, 1, 2]), ("b", [2, 2, 2])],
        [2, 1, 2],
        """
int i = threadIdx.x;
int batch = i / 2;
int col = i % 2;
int k = 0;
float acc = 0.0f;
while (k < 2) {
    acc = acc + a[batch * 2 + k] * b[(batch * 2 + k) * 2 + col];
    k++;
}
out[i] = acc;""",
        "return torch.bmm(a, b)",
        4,
    )
    put(
        "linear",
        [("x", [1, 2]), ("w", [2, 2]), ("bias", [2])],
        [1, 2],
        """
int col = threadIdx.x;
int k = 0;
float acc = 0.0f;
while (k < 2) {
    acc = acc + x[k] * w[k * 2 + col];
    k++;
}
out[col] = acc + bias[col];""",
        "return x @ w + bias",
        2,
    )
    put(
        "conv2d",
        [("x", [1, 2, 2, 2]), ("w", [2, 2, 2, 2])],
        [1, 2, 1, 1],
        """
int oc = threadIdx.x;
int c = 0;
float acc = 0.0f;
while (c < 2) {
    int ky = 0;
    while (ky < 2) {
        int kx = 0;
        while (kx < 2) {
            acc = acc + x[(c * 2 + ky) * 2 + kx] * w[((oc * 2 + c) * 2 + ky) * 2 + kx];
            kx++;
        }
        ky++;
    }
    c++;
}
out[oc] = acc;""",
        "return torch.conv2d(x, w)",
        2,
    )
    put(
        "depthwise_conv",
        [("x", [1, 2, 2, 2]), ("w", [2, 1, 2, 2])],
        [1, 2, 1, 1],
        """
int c = threadIdx.x;
int ky = 0;
float acc = 0.0f;
while (ky < 2) {
    int kx = 0;
    while (kx < 2) {
        acc = acc + x[(c * 2 + ky) * 2 + kx] * w[(c * 2 + ky) * 2 + kx];
        kx++;
    }
    ky++;
}
out[c] = acc;""",
        "return torch.conv2d(x, w, groups=2)",
        2,
    )
    put(
        "barrier_sum",
        [("x", [4])],
        [2],
        """
__shared__ float staged[2];
int t = threadIdx.x;
int i = blockIdx.x * blockDim.x + t;
staged[t] = x[i];
__syncthreads();
int j = 0;
while (j < 1) {
    if (t == 0) { out[blockIdx.x] = 0.0f + staged[0] + staged[1]; }
    j++;
}""",
        "return x.reshape(2, 2).sum(dim=1)",
        2,
        grid=2,
    )
    # Minimal final-pass model of the paper's production race; the output is
    # unchanged for every input, so numerical tests cannot detect the conflict.
    body = """int t = threadIdx.x;
if (t < 3) { out[t] = x[t]; }
__syncthreads();
int a = t;
if (t >= 3) { a = 2; }
float yh = out[a];
if (t < 3) { out[t] = yh; }"""
    put("llmc_race", [("x", [3])], [3], body, "return x", 4)
    put(
        "llmc_fixed",
        [("x", [3])],
        [3],
        body.replace(
            "float yh = out[a];\nif (t < 3) { out[t] = yh; }",
            "if (t < 3) { float yh = out[t]; out[t] = yh; }",
        ),
        "return x",
        4,
    )


if __name__ == "__main__":
    main()
