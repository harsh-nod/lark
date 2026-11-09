extern "C" __global__ void pointwise_gelu_hip(const __half* x, __half* out) {
  int i = blockIdx.x;
  float v = __half2float(x[i]);
  out[i] = __float2half(0.5f * v * (1.0f + tanhf(0.7978845608028654f * (v + 0.044715f * v * v * v))));
}
