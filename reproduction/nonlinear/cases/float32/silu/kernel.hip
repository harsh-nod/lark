extern "C" __global__ void nonlinear_silu_float32(const float* x, float* out) {
int i = threadIdx.x; float v = x[i]; out[i] = v * (1.0f / (1.0f + expf(0.0f - v)));
}
