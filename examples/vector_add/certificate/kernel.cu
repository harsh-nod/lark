extern "C" __global__ void vector_add(const float* x, const float* y, float* out) {
    int i = blockIdx.x * blockDim.x + threadIdx.x;
    out[i] = x[i] + y[i];
}
