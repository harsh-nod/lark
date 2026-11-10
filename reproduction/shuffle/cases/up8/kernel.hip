extern "C" __global__ void up_subgroup(const float* x, float* out) {
  int i = threadIdx.x;
  float value = x[i];
  value = __shfl_up(value, 1, 8);
  out[i] = value;
}
