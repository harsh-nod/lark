extern "C" __global__ void nonlinear_layernorm_float16(const __half* x, __half* out) {
__shared__ float staged[4]; int i = threadIdx.x;
staged[i] = __half2float(x[i]); __syncthreads();
float total = 0.0f; int j = 0;
while(j < 4) { total = total + staged[j]; j++; }
float mean = total / 4.0f; float variance = 0.0f; int k = 0;
while(k < 4) { float delta = staged[k] - mean; variance = variance + delta * delta; k++; }
variance = variance / 4.0f;
out[i] = __float2half((__half2float(x[i]) - mean) * rsqrtf(variance + 1e-5f));
}
