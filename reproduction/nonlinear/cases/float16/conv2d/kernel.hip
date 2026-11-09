extern "C" __global__ void nonlinear_conv2d_float16(const __half* x, const __half* w, __half* out) {
int oc = threadIdx.x;
int c = 0;
float acc = 0.0f;
while (c < 2) {
    int ky = 0;
    while (ky < 2) {
        int kx = 0;
        while (kx < 2) {
            acc = acc + __half2float(x[(c * 2 + ky) * 2 + kx]) * __half2float(w[((oc * 2 + c) * 2 + ky) * 2 + kx]);
            kx++;
        }
        ky++;
    }
    c++;
}
out[oc] = __float2half(acc);
}
