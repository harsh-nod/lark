extern "C" __global__ void reverse(const float* x, float* out) {
    __shared__ float staged[4];
    int i = threadIdx.x;
    staged[i] = x[i];
    __syncthreads();
    out[i] = staged[3 - i];
}
