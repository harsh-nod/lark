#include <hip/hip_runtime.h>
#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <fstream>
#include <vector>
#include "cases/broadcast8/kernel.hip"
#include "cases/down8/kernel.hip"
#include "cases/reverse/kernel.hip"
#include "cases/up8/kernel.hip"
#include "cases/xor8/kernel.hip"

static void checked(hipError_t code) {
  if (code != hipSuccess) { std::fprintf(stderr, "%s\n", hipGetErrorString(code)); std::exit(1); }
}

int main(int argc, char** argv) {
  if (argc != 4) return 2;
  hipDeviceProp_t prop; checked(hipGetDeviceProperties(&prop, 0));
  if (prop.warpSize != 64) return 3;
  std::vector<uint32_t> input(10 * 64);
  std::ifstream in(argv[1], std::ios::binary);
  in.read(reinterpret_cast<char*>(input.data()), input.size() * 4);
  if (in.gcount() != static_cast<std::streamsize>(input.size() * 4) || in.peek() != EOF) return 4;
  std::ofstream out(argv[2], std::ios::binary);
  const uint32_t guard = 0xa5a5a5a5;
  uint32_t *dx, *dy;
  checked(hipMalloc(&dx, 128 * 4)); checked(hipMalloc(&dy, 128 * 4));
  for (int kernel = 0; kernel != 5; ++kernel) {
    for (int trial = 0; trial != 10; ++trial) {
      std::vector<uint32_t> x(128, guard), y(128, guard), gotx(128), goty(128);
      std::copy_n(input.data() + 64 * trial, 64, x.data() + 32);
      checked(hipMemcpy(dx, x.data(), 128 * 4, hipMemcpyHostToDevice));
      checked(hipMemcpy(dy, y.data(), 128 * 4, hipMemcpyHostToDevice));
      float* a = reinterpret_cast<float*>(dx + 32);
      float* b = reinterpret_cast<float*>(dy + 32);
      switch (kernel) {
        case 0: hipLaunchKernelGGL(broadcast_subgroup, dim3(1), dim3(64), 0, 0, a, b); break;
        case 1: hipLaunchKernelGGL(down_subgroup, dim3(1), dim3(64), 0, 0, a, b); break;
        case 2: hipLaunchKernelGGL(reverse_wave, dim3(1), dim3(64), 0, 0, a, b); break;
        case 3: hipLaunchKernelGGL(up_subgroup, dim3(1), dim3(64), 0, 0, a, b); break;
        case 4: hipLaunchKernelGGL(xor_subgroup, dim3(1), dim3(64), 0, 0, a, b); break;
      }
      checked(hipGetLastError()); checked(hipDeviceSynchronize());
      checked(hipMemcpy(gotx.data(), dx, 128 * 4, hipMemcpyDeviceToHost));
      checked(hipMemcpy(goty.data(), dy, 128 * 4, hipMemcpyDeviceToHost));
      if (gotx != x || !std::equal(goty.begin(), goty.begin() + 32, y.begin()) ||
          !std::equal(goty.begin() + 96, goty.end(), y.begin() + 96)) return 5;
      out.write(reinterpret_cast<char*>(goty.data() + 32), 64 * 4);
    }
  }
  checked(hipFree(dx)); checked(hipFree(dy)); out.close();
  if (!out) return 6;
  std::ofstream meta(argv[3]);
  meta << "{\"device\":\"" << prop.name << "\",\"architecture\":\"" << prop.gcnArchName
       << "\",\"warp\":" << prop.warpSize
       << ",\"inputs_unchanged\":true,\"guard_zones_unchanged\":true,\"trials\":50}";
  return !meta;
}
