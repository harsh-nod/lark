extern "C" __global__ void verify_depthwise_conv(const float* x, const float* w, float* out) {
int c = threadIdx.x;
int ky = 0;
float acc = 0.0f;
while (ky < 2) {
    int kx = 0;
    while (kx < 2) {
        acc = acc + x[(c * 2 + ky) * 2 + kx] * w[(c * 2 + ky) * 2 + kx];
        kx++;
    }
    ky++;
}
out[c] = acc;
}
