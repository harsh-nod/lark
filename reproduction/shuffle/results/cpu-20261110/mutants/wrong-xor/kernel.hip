extern "C" __global__ void xor_subgroup(const float* x, float* out) {
  int i = threadIdx.x;
  float value = x[i];
  value = __shfl_xor(value, 2, 8);
  out[i] = value;
}
