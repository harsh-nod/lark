extern "C" __global__ void swiglu_down_cuda_64_256_1024_256(const __half* hidden, const __half* down, __half* out) {
  int i = blockIdx.x;
  float acc = 0.0f;
  int j = 0;
  while(j < 1024) {
    acc = acc + __half2float(hidden[(i / 256) * 1024 + j]) * __half2float(down[j * 256 + i % 256]);
    j++;
  }
  out[i] = __float2half(acc);
}
