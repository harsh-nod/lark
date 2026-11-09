extern "C" __global__ void induction_depthwise_conv_hip_32_32_16_5(const __half* x, const __half* w, __half* out) {
  int t = blockIdx.x;
  float acc = 0.0f;
  int j = 0;
  while(j < 25) {
    acc = acc + __half2float(x[(((t / 144) * 16 + (t / 12) % 12 + (j / 5) % 5) * 16 + t % 12 + j % 5)]) * __half2float(w[(t / 144) * 25 + j]);
    j++;
  }
  out[t] = __float2half(acc);
}
