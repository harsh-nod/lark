extern "C" __global__ void nonlinear_relu_float16(const __half* x, __half* out) {
int i = threadIdx.x;
while (i < 4) {
    float v = __half2float(x[i]);
    out[i] = __float2half(fmaxf(v, 0.0f));
    i += blockDim.x;
}
}
