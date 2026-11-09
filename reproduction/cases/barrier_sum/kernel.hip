extern "C" __global__ void verify_barrier_sum(const float* x, float* out) {
__shared__ float staged[2];
int t = threadIdx.x;
int i = blockIdx.x * blockDim.x + t;
staged[t] = x[i];
__syncthreads();
int j = 0;
while (j < 1) {
    if (t == 0) { out[blockIdx.x] = 0.0f + staged[0] + staged[1]; }
    j++;
}
}
