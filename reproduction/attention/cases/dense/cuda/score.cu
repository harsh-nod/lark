extern "C" __global__ void attention_cuda_1_1_128_256_score(const __half* q, const __half* k, float* scores) {
  int i = blockIdx.x;
  float acc = 0.0f;
  int j = 0;
  while(j < 256) {
    acc = acc + __half2float(q[(i / 16384) * 32768 + (((i / 128) % 128) * 256 + j)]) * __half2float(k[((i / 16384) / 1) * 32768 + ((i % 128) * 256 + j)]);
    j++;
  }
  scores[i] = acc / 16.0f;
}
