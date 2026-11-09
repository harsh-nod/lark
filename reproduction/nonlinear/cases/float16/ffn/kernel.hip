extern "C" __global__ void nonlinear_ffn_float16(const __half* x, const __half* w1, const __half* down, __half* out) {
int t = threadIdx.x; float result = 0.0f; int j = 0;
while(j < 2) { float a = 0.0f; float u = 0.0f; int k = 0;
while(k < 2) { a = a + __half2float(x[k]) * __half2float(w1[k * 2 + j]);  k++; }
float h = __half2float(__float2half(fmaxf(a, 0.0f))); result = result + h * __half2float(down[j * 2 + t]); j++; }
out[t] = __float2half(result);
}
