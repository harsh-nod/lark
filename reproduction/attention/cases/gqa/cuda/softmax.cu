extern "C" __global__ void attention_cuda_2_4_128_64_softmax(const float* scores, float* probabilities) {
  int i = blockIdx.x;
  int j = 0;
  float acc = scores[(i / 128) * 128 + j];
  float ctx = 0.0f;
  float val = 0.0f;
  j = 1;
  while(j < 128) {
    val = scores[(i / 128) * 128 + j];
    acc = fmaxf(acc, val);
    j++;
  }
  ctx = acc;
  acc = 0.0f;
  j = 0;
  while(j < 128) {
    val = scores[(i / 128) * 128 + j];
    acc = acc + expf(val - ctx);
    j++;
  }
  val = scores[i];
  probabilities[i] = expf(val - ctx) / acc;
}
