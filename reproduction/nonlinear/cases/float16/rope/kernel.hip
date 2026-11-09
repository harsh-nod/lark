extern "C" __global__ void nonlinear_rope_float16(const __half* x, const __half* cosine, const __half* sine, __half* out) {
int p = threadIdx.x; int i = p * 2;
float a = __half2float(x[i]); float b = __half2float(x[i + 1]);
out[i] = __float2half(a * __half2float(cosine[p]) - b * __half2float(sine[p]));
out[i + 1] = __float2half(a * __half2float(sine[p]) + b * __half2float(cosine[p]));
}
