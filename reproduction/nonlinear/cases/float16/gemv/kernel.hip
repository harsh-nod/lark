extern "C" __global__ void nonlinear_gemv_float16(const __half* a, const __half* x, __half* out) {
int row = threadIdx.x;
int k = 0;
float acc = 0.0f;
while (k < 3) {
    acc = acc + __half2float(a[row * 3 + k]) * __half2float(x[k]);
    k++;
}
out[row] = __float2half(acc);
}
