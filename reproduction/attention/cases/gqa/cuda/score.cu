extern "C" __global__ void attention_cuda_2_4_128_64_score(const __half* q, const __half* k, float* scores) {
  int i = blockIdx.x;
  float acc = 0.0f;
  int j = 0;
  while(j < 64) {
    acc = acc + __half2float(q[(i / 16384) * 8192 + (((i / 128) % 128) * 64 + j)]) * __half2float(k[((i / 16384) / 4) * 8192 + ((i % 128) * 64 + j)]);
    j++;
  }
  scores[i] = acc / 8.0f;
}
