extern "C" __global__ void nonlinear_linear_float16(const __half* x, const __half* w, const __half* bias, __half* out) {
int col = threadIdx.x;
int k = 0;
float acc = 0.0f;
while (k < 2) {
    acc = acc + __half2float(x[k]) * __half2float(w[k * 2 + col]);
    k++;
}
out[col] = __float2half(acc + __half2float(bias[col]));
}
