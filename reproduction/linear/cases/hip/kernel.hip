extern "C" __global__ void induction_linear_hip_64_256_512(const __half* a, const __half* b, const __half* bias, __half* out) {
  int i = blockIdx.x;
  float acc = 0.0f;
  int j = 0;
  while(j < 256) {
    acc = acc + __half2float(a[(i / 512) * 256 + j]) * __half2float(b[j * 512 + i % 512]);
    j++;
  }
  out[i] = __float2half(acc + __half2float(bias[i % 512]));
}
