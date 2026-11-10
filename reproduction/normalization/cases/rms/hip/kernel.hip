extern "C" __global__ void induction_rms_hip_16384(const __half* x, __half* out) {
  int i = blockIdx.x;
  float acc = 0.0f;
  float ctx = 0.0f;
  float val = 0.0f;
  int j = 0;
  while(j < 16384) {
    val = __half2float(x[j]);
    acc = acc + val * val;
    j++;
  }
  ctx = acc / 16384.0f;
  acc = 0.0f;
  j = 16384;
  while(j < 16384) {
    val = __half2float(x[j]);
    acc = acc + val;
    j++;
  }
  val = __half2float(x[i]);
  out[i] = __float2half(val * rsqrtf(ctx + 0.00001f));
}
