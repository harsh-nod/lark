extern "C" __global__ void ffn_up_hip_64_256_1024_256(const __half* x, const __half* w1, __half* hidden) {
  int i = blockIdx.x;
  float acc = 0.0f;
  int j = 0;
  while(j < 256) {
    acc = acc + __half2float(x[(i / 1024) * 256 + j]) * __half2float(w1[j * 1024 + i % 1024]);
    j++;
  }
  hidden[i] = __float2half(fmaxf(acc, 0.0f));
}
