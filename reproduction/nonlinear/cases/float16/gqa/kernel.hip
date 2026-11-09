extern "C" __global__ void nonlinear_gqa_float16(const __half* q, const __half* key, const __half* value, __half* out) {
int r = threadIdx.x; int head = r / 2; int row = r % 2;
float score0 = 0.0f; float score1 = 0.0f; int k = 0;
while(k < 1) { score0 = score0 + __half2float(q[(head * 2 + row) * 1 + k]) * __half2float(key[k]);
score1 = score1 + __half2float(q[(head * 2 + row) * 1 + k]) * __half2float(key[1 + k]); k++; }
score0 = score0 / 1.0f; score1 = score1 / 1.0f;
float maximum = fmaxf(score0, score1); float e0 = expf(score0 - maximum); float e1 = expf(score1 - maximum);
float denominator = 0.0f + e0 + e1;
int col = 0;
while(col < 1) { float result = 0.0f + (e0 / denominator) * __half2float(value[col]);
result = result + (e1 / denominator) * __half2float(value[1 + col]); out[(head * 2 + row) * 1 + col] = __float2half(result); col++; }
}
