extern "C" __global__ void verify_gemv(const float* a, const float* x, float* out) {
int row = threadIdx.x;
int k = 0;
float acc = 0.0f;
while (k < 3) {
    acc = acc + a[row * 3 + k] * x[k];
    k++;
}
out[row] = acc;
}
