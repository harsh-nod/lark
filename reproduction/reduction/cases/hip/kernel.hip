extern "C" __global__ void induction_gemv_hip_512_1024(const __half* a, const __half* b, __half* out) {
  int i = blockIdx.x;
  float acc = 0.0f;
  int j = 0;
  while(j < 1024) {
    acc = acc + __half2float(a[i * 1024 + j]) * __half2float(b[j]);
    j++;
  }
  out[i] = __float2half(acc);
}
