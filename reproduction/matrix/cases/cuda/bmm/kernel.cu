extern "C" __global__ void induction_bmm_cuda_32_64_256_512(const __half* a, const __half* b, __half* out) {
  int i = blockIdx.x;
  float acc = 0.0f;
  int j = 0;
  while(j < 256) {
    acc = acc + __half2float(a[(i / 32768) * 16384 + (((i / 512) % 64) * 256 + j)]) * __half2float(b[(i / 32768) * 131072 + (j * 512 + i % 512)]);
    j++;
  }
  out[i] = __float2half(acc);
}
