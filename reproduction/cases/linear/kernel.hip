extern "C" __global__ void verify_linear(const float* x, const float* w, const float* bias, float* out) {
int col = threadIdx.x;
int k = 0;
float acc = 0.0f;
while (k < 2) {
    acc = acc + x[k] * w[k * 2 + col];
    k++;
}
out[col] = acc + bias[col];
}
