"""Freeze the full three-pass llm.c FP16 HIP adaptation and guarded-load repair."""

import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from lark_kernels import native_softmax as native  # noqa: E402

HERE = Path(__file__).resolve().parent


def source(guarded):
    header = """/*
 * Copyright (c) 2024 Andrej Karpathy.
 * MIT license: ../../upstream/LICENSE.
 * Independent fixed-shape adaptation of softmax_forward_kernel7.
 * Native HIP wave64 contains two complete logical32 reduction groups.
 * FP16 input/output storage is a departure from the pinned FP32 upstream.
 */
extern "C" __global__ void softmax_forward_kernel7(__half* out, const __half* inp) {
__shared__ float maxvals[32];
__shared__ float sumvals[32];
float exp_regs[8];
float norm_regs[8];
int row = blockIdx.x;
int tid = threadIdx.x;
int warp_id = tid / 32;
int lane_id = tid % 32;
float maxval = -INFINITY;
int max_i = tid;
while (max_i < 50257) {
int max_u = 0;
while (max_u < 8) {
int max_col = max_i + max_u * 1024;
if (max_col >= 50257) { max_col = 50256; }
int max_address = row * 50257 + max_col;
float max_input = __half2float(inp[max_address]);
maxval = fmaxf(maxval, max_input);
max_u = max_u + 1;
}
max_i = max_i + 8192;
}
float max_other = 0.0f;
"""
    for distance in (16, 8, 4, 2, 1):
        header += f"max_other = __shfl_down(maxval, {distance}, 32);\nmaxval = fmaxf(maxval, max_other);\n"
    header += """if (lane_id == 0) { maxvals[warp_id] = maxval; }
__syncthreads();
if (tid == 0) {
float block_max = maxvals[0];
int max_warp = 1;
while (max_warp < 32) {
float warp_max = maxvals[max_warp];
block_max = fmaxf(block_max, warp_max);
max_warp = max_warp + 1;
}
maxvals[0] = block_max;
}
__syncthreads();
float offset = maxvals[0];
float sumval = 0.0f;
int exp_i = tid;
while (exp_i < 50257) {
int exp_load_u = 0;
while (exp_load_u < 8) {
int exp_load_col = exp_i + exp_load_u * 1024;
if (exp_load_col >= 50257) { exp_load_col = 50256; }
int exp_load_address = row * 50257 + exp_load_col;
exp_regs[exp_load_u] = __half2float(inp[exp_load_address]);
exp_load_u = exp_load_u + 1;
}
int exp_store_u = 0;
while (exp_store_u < 8) {
int exp_store_col = exp_i + exp_store_u * 1024;
if (exp_store_col < 50257) {
float exp_input = exp_regs[exp_store_u];
float exp_value = expf(exp_input - offset);
int exp_store_address = row * 50257 + exp_store_col;
out[exp_store_address] = __float2half(exp_value);
sumval = sumval + exp_value;
}
exp_store_u = exp_store_u + 1;
}
exp_i = exp_i + 8192;
}
float sum_other = 0.0f;
"""
    for distance in (16, 8, 4, 2, 1):
        header += f"sum_other = __shfl_xor(sumval, {distance}, 32);\nsumval = sumval + sum_other;\n"
    header += """if (lane_id == 0) { sumvals[warp_id] = sumval; }
__syncthreads();
if (tid == 0) {
float block_sum = sumvals[0];
int sum_warp = 1;
while (sum_warp < 32) {
float warp_sum = sumvals[sum_warp];
block_sum = block_sum + warp_sum;
sum_warp = sum_warp + 1;
}
sumvals[0] = block_sum;
}
__syncthreads();
float total_sum = sumvals[0];
int norm_i = tid;
while (norm_i < 50257) {
int norm_load_u = 0;
while (norm_load_u < 8) {
int norm_load_col = norm_i + norm_load_u * 1024;
"""
    if guarded:
        header += """if (norm_load_col < 50257) {
int norm_load_address = row * 50257 + norm_load_col;
norm_regs[norm_load_u] = __half2float(out[norm_load_address]);
}
"""
    else:
        header += """if (norm_load_col >= 50257) { norm_load_col = 50256; }
int norm_load_address = row * 50257 + norm_load_col;
norm_regs[norm_load_u] = __half2float(out[norm_load_address]);
"""
    header += """norm_load_u = norm_load_u + 1;
}
int norm_store_u = 0;
while (norm_store_u < 8) {
int norm_store_col = norm_i + norm_store_u * 1024;
if (norm_store_col < 50257) {
float norm_value = norm_regs[norm_store_u];
int norm_store_address = row * 50257 + norm_store_col;
out[norm_store_address] = __float2half(norm_value / total_sum);
}
norm_store_u = norm_store_u + 1;
}
norm_i = norm_i + 8192;
}
}
"""
    return header


REFERENCE = """import torch


def reference(inp):
    return torch.softmax(inp.float(), dim=1).half()
"""


def main():
    provenance = json.loads((HERE / "provenance.json").read_text())
    upstream = (HERE / "upstream/softmax_forward.cu").read_bytes()
    assert hashlib.sha256(upstream).hexdigest() == provenance["raw_full_source_sha256"]
    assert b"val = fmaxf(val, __shfl_down_sync(0xFFFFFFFF, val, offset));" in upstream
    assert b"val += __shfl_xor_sync(0xFFFFFFFF, val, offset);" in (HERE / "upstream/common.h").read_bytes()
    for name, guarded in (("native_race", False), ("native_fixed", True)):
        case = HERE / "cases" / name
        case.mkdir(parents=True, exist_ok=True)
        task = {
            "name": "independent_llmc_" + name, "entry": "softmax_forward_kernel7", "language": "hip",
            "buffers": [{"name": "out", "role": "output", "shape": [1, native.WIDTH], "dtype": "float16"},
                        {"name": "inp", "role": "input", "shape": [1, native.WIDTH], "dtype": "float16"}],
            "launch": {"grid": 1, "block": native.BLOCK, "warp": 64}, "fuel": list(native.FUEL),
        }
        (case / "task.json").write_text(json.dumps(task, indent=2) + "\n")
        (case / "kernel.hip").write_text(source(guarded))
        (case / "reference.py").write_text(REFERENCE)
        tr = native.translate(source(guarded), native.parse_task(json.dumps(task)))
        print(json.dumps({"case": name, "instructions": len(tr.program), "shared": tr.shared, "private": tr.locals}))
    changes = {
        "upstream_commit": provenance["commit"], "original_paper_artifact": False,
        "mechanical_rewrites": [
            "Instantiate C50257/block1024; grid equals rows, so the tid>=C early return is unreachable",
            "Inline max helper as descending16/8/4/2/1 down-shuffles and sum helper as matching XOR shuffles, logical width32",
            "Replace for loops by while loops, make cache-hint loads ordinary loads, drop unroll pragmas",
            "Use two static32-element shared arrays for the nonoverlapping dynamic max/sum regions",
            "Use two8-element per-thread private arrays for the two original unrolled register-array scopes",
            "Spell row pointers, clamp indices, compound updates and temporary values explicitly",
            "Flatten declarations and give variables unique names in the scoped reader",
            "Target native HIP wave64 with complete aligned logical32 partitions",
        ],
        "departures": ["FP32 input storage becomes FP16 with explicit fromHalf", "FP32 output storage becomes FP16 with explicit toHalf"],
        "repair": "Guard the normalization pass's output-buffer load by its existing bounds predicate; use the unclamped in-bounds index",
        "negative_infinity_model": "Dedicated source spelling -INFINITY lowers to the reserved executable Ops.literal(-1,4294967296) key. withSeed supplies an arbitrary extended-value seed. No ordinary rational/real/IEEE interpretation is asserted.",
        "reference_scope": "Declared numerical reference is torch.softmax(inp.float(), dim=1).half(); an independent FP64 stable-softmax oracle is also checked. No formal source/reference bridge is asserted.",
    }
    (HERE / "rewrites.json").write_text(json.dumps(changes, indent=2) + "\n")


if __name__ == "__main__":
    main()
