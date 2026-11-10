extern "C" __global__ void induction_layer_cuda_16384(const __half* x, __half* out) {
  int i = blockIdx.x;
  float acc = 0.0f;
  float ctx = 0.0f;
  float val = 0.0f;
  int j = 0;
  while(j < 16384) {
    val = __half2float(x[j]);
    acc = acc + val;
    j++;
  }
  ctx = acc / 16384.0f;
  acc = 0.0f;
  j = 0;
  while(j < 16384) {
    val = __half2float(x[j]);
    acc = acc + (val - ctx) * (val - ctx);
    j++;
  }
  val = __half2float(x[i]);
  out[i] = __float2half((val - ctx) * rsqrtf(acc / 16384.0f + 0.00001f));
}
