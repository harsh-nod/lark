extern "C" __global__ void saxpy(const float* x, const float* y, float* out) {
    int i = threadIdx.x;
    out[i] = 2.0f * x[i] + y[i];
}
