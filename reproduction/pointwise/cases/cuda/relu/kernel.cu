extern "C" __global__ void pointwise_relu_cuda(const __half* x, __half* out) {
  int i = blockIdx.x;
  float v = __half2float(x[i]);
  out[i] = __float2half(fmaxf(v, 0.0f));
}
