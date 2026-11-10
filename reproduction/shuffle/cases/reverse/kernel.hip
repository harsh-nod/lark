extern "C" __global__ void reverse_wave(const float* x, float* out) {
  int i = threadIdx.x;
  float value = x[i];
  value = __shfl(value, 63 - i, 64);
  out[i] = value;
}
