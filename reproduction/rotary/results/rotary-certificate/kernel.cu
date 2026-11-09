extern "C" __global__ void induction_rotary_hip_256_128(const __half* x, const __half* cosine, const __half* sine, __half* out) {
  int t = blockIdx.x;
  int i = (t / 2) * 2;
  float a = __half2float(x[i]);
  float b = __half2float(x[i + 1]);
  if(t % 2 == 0) {
    out[t] = __float2half(a * __half2float(cosine[t / 2]) - b * __half2float(sine[t / 2]));
  } else {
    out[t] = __float2half(a * __half2float(sine[t / 2]) + b * __half2float(cosine[t / 2]));
  }
}
