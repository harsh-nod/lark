extern "C" __global__ void verify_gemm(const float* a, const float* b, float* out) {
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
out[t] = acc;
}
