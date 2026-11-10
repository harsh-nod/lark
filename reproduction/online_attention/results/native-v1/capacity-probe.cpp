#include <hip/hip_runtime.h>
#include <cstdio>
int main() {
  hipDeviceProp_t p{};
  hipError_t e = hipGetDeviceProperties(&p, 0);
  if (e != hipSuccess) { std::fprintf(stderr, "%s\n", hipGetErrorString(e)); return 1; }
  std::printf("{\"name\":\"%s\",\"arch\":\"%s\",\"warp\":%d,\"max_threads\":%d,\"shared_per_block\":%zu,\"shared_per_cu\":%zu}\n", p.name, p.gcnArchName, p.warpSize, p.maxThreadsPerBlock, p.sharedMemPerBlock, p.maxSharedMemoryPerMultiProcessor);
}
