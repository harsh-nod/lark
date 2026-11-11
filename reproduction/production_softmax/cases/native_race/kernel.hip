/*
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
max_other = __shfl_down(maxval, 16, 32);
maxval = fmaxf(maxval, max_other);
max_other = __shfl_down(maxval, 8, 32);
maxval = fmaxf(maxval, max_other);
max_other = __shfl_down(maxval, 4, 32);
maxval = fmaxf(maxval, max_other);
max_other = __shfl_down(maxval, 2, 32);
maxval = fmaxf(maxval, max_other);
max_other = __shfl_down(maxval, 1, 32);
maxval = fmaxf(maxval, max_other);
if (lane_id == 0) { maxvals[warp_id] = maxval; }
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
sum_other = __shfl_xor(sumval, 16, 32);
sumval = sumval + sum_other;
sum_other = __shfl_xor(sumval, 8, 32);
sumval = sumval + sum_other;
sum_other = __shfl_xor(sumval, 4, 32);
sumval = sumval + sum_other;
sum_other = __shfl_xor(sumval, 2, 32);
sumval = sumval + sum_other;
sum_other = __shfl_xor(sumval, 1, 32);
sumval = sumval + sum_other;
if (lane_id == 0) { sumvals[warp_id] = sumval; }
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
if (norm_load_col >= 50257) { norm_load_col = 50256; }
int norm_load_address = row * 50257 + norm_load_col;
norm_regs[norm_load_u] = __half2float(out[norm_load_address]);
norm_load_u = norm_load_u + 1;
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
