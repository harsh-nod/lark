extern "C" __global__ void nonlinear_gelu_float32(const float* x, float* out) {
int i = threadIdx.x; float v = x[i]; out[i] = 0.5f * v * (1.0f + tanhf(0.7978845608028654f * (v + 0.044715f * v * v * v)));
}
