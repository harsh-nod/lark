extern "C" __global__ void swiglu_gate_cuda_64_256_1024_256(const __half* x, const __half* wgate, float* gate) {
  int i = blockIdx.x;
  float acc = 0.0f;
  int j = 0;
  while(j < 256) {
    acc = acc + __half2float(x[(i / 1024) * 256 + j]) * __half2float(wgate[j * 1024 + i % 1024]);
    j++;
  }
  gate[i] = acc;
}
