extern "C" __global__ void broadcast_subgroup(const float* x, float* out) {
  int i = threadIdx.x;
  float value = x[i];
  float result = __shfl(value, 1, 8);
  out[i] = result;
}
