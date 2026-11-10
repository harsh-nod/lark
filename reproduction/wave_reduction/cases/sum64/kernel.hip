extern "C" __global__ void wave_sum(const float* input, float* output) {
 int lane = threadIdx.x;
 float x = input[lane];
 float y = __shfl_xor(x, 32, 64);
 x = x + y;
 y = __shfl_xor(x, 16, 64);
 x = x + y;
 y = __shfl_xor(x, 8, 64);
 x = x + y;
 y = __shfl_xor(x, 4, 64);
 x = x + y;
 y = __shfl_xor(x, 2, 64);
 x = x + y;
 y = __shfl_xor(x, 1, 64);
 x = x + y;
 output[lane] = x;
}
