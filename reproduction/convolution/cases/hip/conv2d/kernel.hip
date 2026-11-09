extern "C" __global__ void induction_conv2d_hip_32_8_8_3(const __half* x, const __half* w, __half* out) {
  int t = blockIdx.x;
  float acc = 0.0f;
  int j = 0;
  while(j < 288) {
    acc = acc + __half2float(x[(((j / 9) * 8 + (t / 6) % 6 + (j / 3) % 3) * 8 + t % 6 + j % 3)]) * __half2float(w[(t / 36) * 288 + j]);
    j++;
  }
  out[t] = __float2half(acc);
}
