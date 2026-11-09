extern "C" __global__ void matmul(const float* a, const float* b, float* out) {
    int i = threadIdx.x;
    int row = i / 2;
    int col = i % 2;
    int k = 0;
    float acc = 0.0f;
    while (k < 2) {
        acc = acc + a[row * 2 + k] * b[k * 2 + col];
        k++;
    }
    out[i] = acc;
}
