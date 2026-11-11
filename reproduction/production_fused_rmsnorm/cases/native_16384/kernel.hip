/*
 * Copyright (c) 2024 by FlashInfer team.
 * Licensed under the Apache License, Version 2.0.
 * See ../../upstream/FLASHINFER_LICENSE for the license text.
 *
 * Modified for this independent LARK study: fixed FP16 shape, HIP wave64 with
 * logical32 shuffles, scalarized vector accesses and guarded shared stores.
 * The FP32 shared value remains distinct from the rounded FP16 residual.
 */
extern "C" __global__ void fused_add_rmsnorm(__half* input, __half* residual, const __half* weight) {
__shared__ float partial[32];
__shared__ float unrounded[16384];
int row = blockIdx.x;
int t = threadIdx.x;
int lane = t % 32;
int warp = t / 32;
float sum = 0.0f;
float other = 0.0f;
int iteration = 0;
while (iteration < 2) {
int component = 0;
while (component < 8) {
int column = (iteration * 1024 + t) * 8 + component;
int address = row * 16384 + column;
float x = __half2float(input[address]);
float r = __half2float(residual[address]);
x = x + r;
float square = x * x;
sum = sum + square;
residual[address] = __float2half(x);
unrounded[column] = x;
component = component + 1;
}
iteration = iteration + 1;
}
other = __shfl_xor(sum, 16, 32);
sum = sum + other;
other = __shfl_xor(sum, 8, 32);
sum = sum + other;
other = __shfl_xor(sum, 4, 32);
sum = sum + other;
other = __shfl_xor(sum, 2, 32);
sum = sum + other;
other = __shfl_xor(sum, 1, 32);
sum = sum + other;
if (lane == 0) { partial[warp] = sum; }
__syncthreads();
if (t < 32) {
sum = partial[t];
other = __shfl_xor(sum, 16, 32);
sum = sum + other;
other = __shfl_xor(sum, 8, 32);
sum = sum + other;
other = __shfl_xor(sum, 4, 32);
sum = sum + other;
other = __shfl_xor(sum, 2, 32);
sum = sum + other;
other = __shfl_xor(sum, 1, 32);
sum = sum + other;
if (t == 0) { partial[0] = sum; }
}
__syncthreads();
float total = partial[0];
float mean = total / 16384.0f;
float variance = mean + 0.00001f;
float scale = rsqrtf(variance);
int output_iteration = 0;
while (output_iteration < 2) {
int output_component = 0;
while (output_component < 8) {
int output_column = (output_iteration * 1024 + t) * 8 + output_component;
int output_address = row * 16384 + output_column;
float value = unrounded[output_column];
float w = __half2float(weight[output_column]);
float biased_weight = 0.0f + w;
float normalized = value * scale;
float result = normalized * biased_weight;
input[output_address] = __float2half(result);
output_component = output_component + 1;
}
output_iteration = output_iteration + 1;
}
}
