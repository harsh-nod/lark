extern "C" __global__ void rmsnorm(__half* output, const __half* input, const __half* weight) {
  __shared__ float partials[16];
  __shared__ float scale[1];
  int row = blockIdx.x;
  int tid = threadIdx.x;
  int lane = tid % 64;
  int warp = tid / 64;
  int valid = 1024 - warp * 64;
  float variance = 0.0f;
  float peer = 0.0f;
  int vector = tid;
  while (vector < 2048) {
    int component = 0;
    while (component < 8) {
      float readValue = __half2float(input[row * 16384 + vector * 8 + component]);
      float square = readValue * readValue;
      variance = variance + square;
      component = component + 1;
    }
    vector = vector + 1024;
  }
  peer = __shfl_down(variance, 1, 64);
  if (lane + 1 < valid) { variance = variance + peer; }
  peer = __shfl_down(variance, 2, 64);
  if (lane + 2 < valid) { variance = variance + peer; }
  peer = __shfl_down(variance, 4, 64);
  if (lane + 4 < valid) { variance = variance + peer; }
  peer = __shfl_down(variance, 8, 64);
  if (lane + 8 < valid) { variance = variance + peer; }
  peer = __shfl_down(variance, 16, 64);
  if (lane + 16 < valid) { variance = variance + peer; }
  peer = __shfl_down(variance, 32, 64);
  if (lane + 32 < valid) { variance = variance + peer; }
  if (lane == 0) { partials[warp] = variance; }

  if (tid < 16) {
    variance = partials[lane];
    peer = __shfl_down(variance, 1, 16);
    if (lane + 1 < 16) { variance = variance + peer; }
    peer = __shfl_down(variance, 2, 16);
    if (lane + 2 < 16) { variance = variance + peer; }
    peer = __shfl_down(variance, 4, 16);
    if (lane + 4 < 16) { variance = variance + peer; }
    peer = __shfl_down(variance, 8, 16);
    if (lane + 8 < 16) { variance = variance + peer; }
    if (tid == 0) { scale[0] = rsqrtf(variance / 16384.0f + 0.00001f); }
  }
  __syncthreads();
  float inverse = scale[0];
  int outVector = tid;
  while (outVector < 2048) {
    int outComponent = 0;
    while (outComponent < 8) {
      float outValue = __half2float(input[row * 16384 + outVector * 8 + outComponent]);
      float outWeight = __half2float(weight[outVector * 8 + outComponent]);
      float scaledValue = outValue * inverse;
      float weightedValue = scaledValue * outWeight;
      output[row * 16384 + outVector * 8 + outComponent] = __float2half(weightedValue);
      outComponent = outComponent + 1;
    }
    outVector = outVector + 1024;
  }
}
