extern "C" __global__ void verify_conv2d(const float* x, const float* w, float* out) {
int oc = threadIdx.x;
int c = 0;
float acc = 0.0f;
while (c < 2) {
    int ky = 0;
    while (ky < 2) {
        int kx = 0;
        while (kx < 2) {
            acc = acc + x[(c * 2 + ky) * 2 + kx] * w[((oc * 2 + c) * 2 + ky) * 2 + kx];
            kx++;
        }
        ky++;
    }
    c++;
}
out[oc] = acc;
}
