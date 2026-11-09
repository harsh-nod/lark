extern "C" __global__ void nonlinear_softmax_float32(const float* x, float* out) {
__shared__ float staged[4]; __shared__ float weights[4];
int i = threadIdx.x; staged[i] = x[i]; __syncthreads();
float maximum = staged[0]; int j = 1;
while(j < 4) { maximum = fmaxf(maximum, staged[j]); j++; }
weights[i] = expf(x[i] - maximum); __syncthreads();
float total = 0.0f; int k = 0;
while(k < 4) { total = total + weights[k]; k++; }
out[i] = weights[i] / total;
}
