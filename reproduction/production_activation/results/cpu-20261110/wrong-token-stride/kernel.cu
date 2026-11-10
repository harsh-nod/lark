extern "C" __global__ void vllm_silu_and_mul_adapted(__half* out, const __half* input) {
int token_idx = blockIdx.x;
int idx = threadIdx.x;
while (idx < 5) {
float x = __half2float(input[token_idx * 5 + idx]);
float y = __half2float(input[token_idx * 5 + idx + 5]);
float activated = __half2float(__float2half(x / (1.0f + expf((0.0f - x) * 1.0f))));
out[token_idx * 5 + idx] = __float2half(activated * (y + 0.0f));
idx = idx + blockDim.x;
}
}
