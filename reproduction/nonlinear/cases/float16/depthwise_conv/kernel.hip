extern "C" __global__ void nonlinear_depthwise_conv_float16(const __half* x, const __half* w, __half* out) {
int c = threadIdx.x;
int ky = 0;
float acc = 0.0f;
while (ky < 2) {
    int kx = 0;
    while (kx < 2) {
        acc = acc + __half2float(x[(c * 2 + ky) * 2 + kx]) * __half2float(w[(c * 2 + ky) * 2 + kx]);
        kx++;
    }
    ky++;
}
out[c] = __float2half(acc);
}
