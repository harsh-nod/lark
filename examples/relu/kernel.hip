extern "C" __global__ void relu(const float* x, float* out) {
    int i = threadIdx.x;
    out[i] = fmaxf(x[i], 0.0f);
}
