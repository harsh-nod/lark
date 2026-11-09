extern "C" __global__ void nonlinear_rmsnorm_float32(const float* x, float* out) {
__shared__ float staged[4]; int i = threadIdx.x;
staged[i] = x[i]; __syncthreads();
float total = 0.0f; int j = 0;
while(j < 4) { total = total + staged[j] * staged[j]; j++; }
out[i] = x[i] * rsqrtf(total / 4.0f + 1e-5f);
}
