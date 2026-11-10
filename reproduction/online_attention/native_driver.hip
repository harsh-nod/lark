#include "fp32_driver.hip"
#include <hip/hip_fp16.h>
#include "kernel.hip"

extern "C" int run_native_case(int groups, void* adapted, const void* qh,
    const void* kh, const void* vh, void* upstream, const void* qf, const void* kf,
    const void* vf, void* l, void* m) {
  if (groups <= 0 || groups > 65535) return (int)hipErrorInvalidValue;
  hipLaunchKernelGGL(online_attention, dim3(groups), dim3(32), 0, 0,
      (__half*)adapted, (const __half*)qh, (const __half*)kh, (const __half*)vh);
  hipError_t e = hipGetLastError();
  if (e != hipSuccess) return (int)e;
  return run_case(1, groups, 128, 256, (const float*)qf, (const float*)kf,
      (const float*)vf, (float*)l, (float*)m, (float*)upstream);
}
