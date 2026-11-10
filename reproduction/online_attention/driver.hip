#include <hip/hip_runtime.h>
#include <cmath>
#include "upstream_context.cuh"

// The extracted forward_kernel above is unchanged. This wrapper replaces the
// Torch host launcher, preserves Bc=Br=32, and explicitly enables its LDS size.
__global__ void initialize_maximum(float* m, int n) {
  int i = blockIdx.x * blockDim.x + threadIdx.x;
  if (i < n) m[i] = -INFINITY;
}

extern "C" int runtime_attribute(int which) {
  hipDeviceProp_t p{};
  if (hipGetDeviceProperties(&p, 0) != hipSuccess) return -1;
  return which == 0 ? p.warpSize : which == 1 ? p.maxThreadsPerBlock :
    which == 2 ? (int)p.sharedMemPerBlock : -1;
}

extern "C" int run_case(int batch, int heads, int n, int d,
    const float* q, const float* k, const float* v, float* l, float* m, float* o) {
  if (batch <= 0 || heads <= 0 || n <= 0 || n % 32 || d <= 0 || d > 256)
    return (int)hipErrorInvalidValue;
  size_t rows = (size_t)batch * heads * n;
  hipError_t e = hipMemset(l, 0, rows * sizeof(float));
  if (e != hipSuccess) return (int)e;
  e = hipMemset(o, 0, rows * d * sizeof(float));
  if (e != hipSuccess) return (int)e;
  hipLaunchKernelGGL(initialize_maximum, dim3((rows + 255) / 256), dim3(256), 0, 0, m, (int)rows);
  e = hipGetLastError(); if (e != hipSuccess) return (int)e;
  int shared = (3 * 32 * d + 32 * 32) * sizeof(float);
  e = hipFuncSetAttribute((const void*)forward_kernel,
                         hipFuncAttributeMaxDynamicSharedMemorySize, shared);
  if (e != hipSuccess) return (int)e;
  hipLaunchKernelGGL(forward_kernel, dim3(batch, heads), dim3(32), shared, 0,
      q, k, v, n, d, n / 32, n / 32, 32, 32, 1.0f / sqrtf((float)d), l, m, o);
  return (int)hipGetLastError();
}
