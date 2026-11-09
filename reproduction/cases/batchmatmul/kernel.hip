extern "C" __global__ void verify_batchmatmul(const float* a, const float* b, float* out) {
int i = threadIdx.x;
int batch = i / 2;
int col = i % 2;
int k = 0;
float acc = 0.0f;
while (k < 2) {
    acc = acc + a[batch * 2 + k] * b[(batch * 2 + k) * 2 + col];
    k++;
}
out[i] = acc;
}
