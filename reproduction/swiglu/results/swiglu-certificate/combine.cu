extern "C" __global__ void swiglu_combine_hip_64_256_1024_256(const float* gate, const float* up, __half* hidden) {
  int i = blockIdx.x;
  float a = gate[i];
  float b = up[i];
  hidden[i] = __float2half((a * (1.0f / (1.0f + expf(0.0f - a)))) * b);
}
