extern "C" __global__ void sglang_rmsnorm(__half* output, const __half* input, const __half* weight) {
__shared__ float partial[32];
int row = blockIdx.x;
int tid = threadIdx.x;
int lane = tid % 32;
int warp = tid / 32;
__half input_values[16];
__half weight_values[16];
__half output_values[16];
int input_iteration = 0;
while (input_iteration < 2) {
int input_component = 0;
while (input_component < 8) {
int input_column = (input_iteration * 1024 + tid) * 8 + input_component;
int input_address = row * 16384 + input_column;
int input_slot = input_iteration * 8 + input_component;
input_values[input_slot] = input[input_address];
input_component = input_component + 1;
}
input_iteration = input_iteration + 1;
}
int weight_iteration = 0;
while (weight_iteration < 2) {
int weight_component = 0;
while (weight_component < 8) {
int weight_column = (weight_iteration * 1024 + tid) * 8 + weight_component;
int weight_slot = weight_iteration * 8 + weight_component;
weight_values[weight_slot] = weight[weight_column];
weight_component = weight_component + 1;
}
weight_iteration = weight_iteration + 1;
}
float sum = 0.0f;
float other = 0.0f;
int square_iteration = 0;
while (square_iteration < 2) {
int square_pair = 0;
while (square_pair < 4) {
int square_slot = square_iteration * 8 + square_pair * 2;
float x = __half2float(input_values[square_slot]);
float y = __half2float(input_values[square_slot + 1]);
float xx = x * x;
float yy = y * y;
float pair_square = xx + yy;
sum = sum + pair_square;
square_pair = square_pair + 1;
}
square_iteration = square_iteration + 1;
}
other = __shfl_xor(sum, 16, 32);
sum = sum + other;
other = __shfl_xor(sum, 8, 32);
sum = sum + other;
other = __shfl_xor(sum, 4, 32);
sum = sum + other;
other = __shfl_xor(sum, 2, 32);
sum = sum + other;
other = __shfl_xor(sum, 1, 32);
sum = sum + other;
partial[warp] = sum;
__syncthreads();
if (warp == 0) {
float block_sum = 0.0f;
if (tid < 32) {
block_sum = partial[tid];
}
float block_other = 0.0f;
block_other = __shfl_xor(block_sum, 16, 32);
block_sum = block_sum + block_other;
block_other = __shfl_xor(block_sum, 8, 32);
block_sum = block_sum + block_other;
block_other = __shfl_xor(block_sum, 4, 32);
block_sum = block_sum + block_other;
block_other = __shfl_xor(block_sum, 2, 32);
block_sum = block_sum + block_other;
block_other = __shfl_xor(block_sum, 1, 32);
block_sum = block_sum + block_other;
float mean = block_sum / 16384.0f;
float shifted = mean + 0.00001f;
float stored_inverse = rsqrtf(shifted);
partial[tid] = stored_inverse;
}
__syncthreads();
float inverse = partial[warp];
int output_iteration = 0;
while (output_iteration < 2) {
int output_pair = 0;
while (output_pair < 4) {
int output_slot = output_iteration * 8 + output_pair * 2;
float output_x = __half2float(input_values[output_slot]);
float output_y = __half2float(input_values[output_slot + 1]);
float weight_x = __half2float(weight_values[output_slot]);
float weight_y = __half2float(weight_values[output_slot + 1]);
float scaled_x = output_x * inverse;
float result_x = scaled_x * weight_x;
float scaled_y = output_y * inverse;
float result_y = scaled_y * weight_y;
output_values[output_slot] = __float2half(result_x);
output_values[output_slot + 1] = __float2half(result_y);
output_pair = output_pair + 1;
}
output_iteration = output_iteration + 1;
}
int store_iteration = 0;
while (store_iteration < 2) {
int store_component = 0;
while (store_component < 8) {
int store_column = (store_iteration * 1024 + tid) * 8 + store_component;
int store_address = row * 16384 + store_column;
int store_slot = store_iteration * 8 + store_component;
output[store_address] = output_values[store_slot];
store_component = store_component + 1;
}
store_iteration = store_iteration + 1;
}
}
