#include <hip/hip_runtime.h>
#include <cmath>
extern "C" __global__ void verify_relu(const float* x, float* out) {
int i = threadIdx.x;
while (i < 4) {
    float v = x[i];
    out[i] = fmaxf(v, 0.0f);
    i += blockDim.x;
}
}

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

extern "C" __global__ void verify_gemm(const float* a, const float* b, float* out) {
__shared__ float staged_a[2];
__shared__ float staged_b[4];
int t = threadIdx.x;
staged_a[t] = a[t];
staged_b[t] = b[t];
staged_b[2 + t] = b[2 + t];
__syncthreads();
int k = 0;
float acc = 0.0f;
while (k < 2) {
    acc = acc + staged_a[k] * staged_b[k * 2 + t];
    k++;
}
out[t] = acc;
}

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

extern "C" __global__ void verify_conv2d(const float* x, const float* w, float* out) {
int oc = threadIdx.x;
int c = 0;
float acc = 0.0f;
while (c < 2) {
    int ky = 0;
    while (ky < 2) {
        int kx = 0;
        while (kx < 2) {
            acc = acc + x[(c * 2 + ky) * 2 + kx] * w[((oc * 2 + c) * 2 + ky) * 2 + kx];
            kx++;
        }
        ky++;
    }
    c++;
}
out[oc] = acc;
}

extern "C" __global__ void verify_depthwise_conv(const float* x, const float* w, float* out) {
int c = threadIdx.x;
int ky = 0;
float acc = 0.0f;
while (ky < 2) {
    int kx = 0;
    while (kx < 2) {
        acc = acc + x[(c * 2 + ky) * 2 + kx] * w[(c * 2 + ky) * 2 + kx];
        kx++;
    }
    ky++;
}
out[c] = acc;
}

extern "C" __global__ void verify_barrier_sum(const float* x, float* out) {
__shared__ float staged[2];
int t = threadIdx.x;
int i = blockIdx.x * blockDim.x + t;
staged[t] = x[i];
__syncthreads();
int j = 0;
while (j < 1) {
    if (t == 0) { out[blockIdx.x] = 0.0f + staged[0] + staged[1]; }
    j++;
}
}

extern "C" __global__ void verify_llmc_fixed(const float* x, float* out) {
int t = threadIdx.x;
if (t < 3) { out[t] = x[t]; }
__syncthreads();
int a = t;
if (t >= 3) { a = 2; }
if (t < 3) { float yh = out[t]; out[t] = yh; }
}

extern "C" int run_small(int id,void** a,void* stream) {
 switch(id) {
case 0: hipLaunchKernelGGL(verify_relu,dim3(1),dim3(2),0,(hipStream_t)stream,(const float*)a[0], (float*)a[1]); break;
case 1: hipLaunchKernelGGL(verify_gemv,dim3(1),dim3(2),0,(hipStream_t)stream,(const float*)a[0], (const float*)a[1], (float*)a[2]); break;
case 2: hipLaunchKernelGGL(verify_gemm,dim3(1),dim3(2),0,(hipStream_t)stream,(const float*)a[0], (const float*)a[1], (float*)a[2]); break;
case 3: hipLaunchKernelGGL(verify_batchmatmul,dim3(1),dim3(4),0,(hipStream_t)stream,(const float*)a[0], (const float*)a[1], (float*)a[2]); break;
case 4: hipLaunchKernelGGL(verify_linear,dim3(1),dim3(2),0,(hipStream_t)stream,(const float*)a[0], (const float*)a[1], (const float*)a[2], (float*)a[3]); break;
case 5: hipLaunchKernelGGL(verify_conv2d,dim3(1),dim3(2),0,(hipStream_t)stream,(const float*)a[0], (const float*)a[1], (float*)a[2]); break;
case 6: hipLaunchKernelGGL(verify_depthwise_conv,dim3(1),dim3(2),0,(hipStream_t)stream,(const float*)a[0], (const float*)a[1], (float*)a[2]); break;
case 7: hipLaunchKernelGGL(verify_barrier_sum,dim3(2),dim3(2),0,(hipStream_t)stream,(const float*)a[0], (float*)a[1]); break;
case 8: hipLaunchKernelGGL(verify_llmc_fixed,dim3(1),dim3(4),0,(hipStream_t)stream,(const float*)a[0], (float*)a[1]); break;
default:return -1; } return int(hipGetLastError()); }
