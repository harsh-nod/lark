extern "C" __global__ void induction_softmax_hip_16384(const __half* x, __half* out) {
  int i = blockIdx.x;
  float acc = __half2float(x[0]);
  float ctx = 0.0f;
  float val = 0.0f;
  int j = 1;
  while(j < 16384) {
    val = __half2float(x[j]);
    acc = fmaxf(acc, val);
    j++;
  }
  ctx = acc;
  acc = 0.0f;
  j = 0;
  while(j < 16384) {
    val = __half2float(x[j]);
    acc = acc + expf(val - ctx);
    j++;
  }
  val = __half2float(x[i]);
  out[i] = __float2half(expf(val - ctx) / acc);
}
