extern "C" __global__ void attention_cuda_1_1_128_256_value(const float* probabilities, const __half* v, __half* out) {
  int i = blockIdx.x;
  float acc = 0.0f;
  int j = 0;
  while(j < 128) {
    acc = acc + probabilities[(i / 32768) * 16384 + (((i / 256) % 128) * 128 + j)] * __half2float(v[((i / 32768) / 1) * 32768 + (j * 256 + i % 256)]);
    j++;
  }
  out[i] = __float2half(acc);
}
