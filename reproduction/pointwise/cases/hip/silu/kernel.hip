extern "C" __global__ void pointwise_silu_hip(const __half* x, __half* out) {
  int i = blockIdx.x;
  float v = __half2float(x[i]);
  out[i] = __float2half(v * (1.0f / (1.0f + expf(0.0f - v))));
}
