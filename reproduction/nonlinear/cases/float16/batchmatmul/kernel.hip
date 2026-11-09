extern "C" __global__ void nonlinear_batchmatmul_float16(const __half* a, const __half* b, __half* out) {
int i = threadIdx.x;
int batch = i / 2;
int col = i % 2;
int k = 0;
float acc = 0.0f;
while (k < 2) {
    acc = acc + __half2float(a[batch * 2 + k]) * __half2float(b[(batch * 2 + k) * 2 + col]);
    k++;
}
out[i] = __float2half(acc);
}
