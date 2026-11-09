extern "C" __global__ void verify_relu(const float* x, float* out) {
int i = threadIdx.x;
while (i < 4) {
    float v = x[i];
    out[i] = fmaxf(v, 0.0f);
    i += blockDim.x;
}
}
