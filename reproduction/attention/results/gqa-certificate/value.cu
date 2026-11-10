extern "C" __global__ void attention_hip_2_4_128_64_value(const float* probabilities, const __half* v, __half* out) {
  int i = blockIdx.x;
  float acc = 0.0f;
  int j = 0;
  while(j < 128) {
    acc = acc + probabilities[(i / 8192) * 16384 + (((i / 64) % 128) * 128 + j)] * __half2float(v[((i / 8192) / 4) * 8192 + (j * 64 + i % 64)]);
    j++;
  }
  out[i] = __float2half(acc);
}
