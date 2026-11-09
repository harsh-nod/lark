extern "C" __global__ void nonlinear_gemm_float16(const __half* a, const __half* b, __half* out) {
__shared__ float staged_a[2];
__shared__ float staged_b[4];
int t = threadIdx.x;
staged_a[t] = __half2float(a[t]);
staged_b[t] = __half2float(b[t]);
staged_b[2 + t] = __half2float(b[2 + t]);
__syncthreads();
int k = 0;
float acc = 0.0f;
while (k < 2) {
    acc = acc + staged_a[k] * staged_b[k * 2 + t];
    k++;
}
out[t] = __float2half(acc);
}
