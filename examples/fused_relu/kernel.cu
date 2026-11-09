extern "C" __global__ void fused_relu(const float* x, const float* y, float* out) {
    int i = threadIdx.x;
    float v = x[i] + y[i];
    out[i] = fmaxf(v, 0.0f) * y[i];
}
