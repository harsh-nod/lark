#include <hip/hip_runtime.h>
#include <cstdint>
#include <cstring>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>

using H4 = _Float16 __attribute__((ext_vector_type(4)));
using F4 = float __attribute__((ext_vector_type(4)));

__global__ void shuffles(const int4* configs, const uint32_t* input, uint32_t* output) {
  int c = blockIdx.x, i = threadIdx.x, at = c * 128 + i;
  int4 p = configs[c];
  uint32_t u = input[at], r = u;
  if (p.w == 0) {
    if (p.x == 0) r = __shfl(u, p.z, p.y);
    if (p.x == 1) r = __shfl_up(u, p.z, p.y);
    if (p.x == 2) r = __shfl_down(u, p.z, p.y);
    if (p.x == 3) r = __shfl_xor(u, p.z, p.y);
  } else {
    float f = __uint_as_float(u), v = f;
    if (p.x == 0) v = __shfl(f, p.z, p.y);
    if (p.x == 1) v = __shfl_up(f, p.z, p.y);
    if (p.x == 2) v = __shfl_down(f, p.z, p.y);
    if (p.x == 3) v = __shfl_xor(f, p.z, p.y);
    r = __float_as_uint(v);
  }
  output[at] = r;
}

__global__ void mfma(const _Float16* a, const _Float16* b, const float* c, float* d) {
  int at = blockIdx.x * 256 + threadIdx.x * 4;
  H4 av = *reinterpret_cast<const H4*>(a + at);
  H4 bv = *reinterpret_cast<const H4*>(b + at);
  F4 cv = *reinterpret_cast<const F4*>(c + at);
  F4 dv = __builtin_amdgcn_mfma_f32_16x16x16f16(av, bv, cv, 0, 0, 0);
  *reinterpret_cast<F4*>(d + at) = dv;
}

void check(hipError_t error) {
  if (error != hipSuccess) throw std::runtime_error(hipGetErrorString(error));
}

std::vector<char> read(const std::string& path) {
  std::ifstream f(path, std::ios::binary | std::ios::ate);
  if (!f) throw std::runtime_error("Cannot read " + path);
  size_t n = f.tellg(); f.seekg(0);
  std::vector<char> data(n); f.read(data.data(), n);
  if (!f) throw std::runtime_error("Incomplete input " + path);
  return data;
}

struct Allocation {
  char* base = nullptr;
  size_t size;
  std::vector<char> original;
  Allocation(const std::vector<char>& data) : size(data.size()), original(size + 256, char(0x5a)) {
    std::memcpy(original.data() + 128, data.data(), size);
    check(hipMalloc(reinterpret_cast<void**>(&base), original.size()));
    check(hipMemcpy(base, original.data(), original.size(), hipMemcpyHostToDevice));
  }
  void* payload() { return base + 128; }
  std::vector<char> verify(bool input) {
    std::vector<char> actual(original.size());
    check(hipMemcpy(actual.data(), base, actual.size(), hipMemcpyDeviceToHost));
    if (std::memcmp(actual.data(), original.data(), 128) ||
        std::memcmp(actual.data() + 128 + size, original.data() + 128 + size, 128))
      throw std::runtime_error("Guard changed");
    if (input && actual != original) throw std::runtime_error("Input changed");
    return std::vector<char>(actual.begin() + 128, actual.end() - 128);
  }
  ~Allocation() { if (base) hipFree(base); }
};

void write(const std::string& path, const std::vector<char>& data) {
  std::ofstream f(path, std::ios::binary); f.write(data.data(), data.size());
  if (!f) throw std::runtime_error("Cannot write " + path);
}

int main(int argc, char** argv) {
  try {
    if (argc != 3) throw std::runtime_error("Expected input and output directories");
    std::string in = argv[1], out = argv[2];
    hipDeviceProp_t prop; check(hipGetDeviceProperties(&prop, 0));
    if (prop.warpSize != 64) throw std::runtime_error("Wave64 required");
    auto config = read(in + "/shuffle-configs.bin");
    auto input = read(in + "/shuffle-input.bin");
    if (config.size() % 16 || input.size() != config.size() / 16 * 128 * 4)
      throw std::runtime_error("Invalid shuffle extents");
    Allocation cfg(config), src(input), dst(std::vector<char>(input.size(), 0));
    hipLaunchKernelGGL(shuffles, dim3(config.size() / 16), dim3(128), 0, 0,
      static_cast<int4*>(cfg.payload()), static_cast<uint32_t*>(src.payload()), static_cast<uint32_t*>(dst.payload()));
    check(hipGetLastError()); check(hipDeviceSynchronize());
    cfg.verify(true); src.verify(true); write(out + "/shuffle-actual.bin", dst.verify(false));
    auto ad = read(in + "/mfma-a.bin"), bd = read(in + "/mfma-b.bin"), cd = read(in + "/mfma-c.bin");
    if (ad.empty() || ad.size() % 512 || bd.size() != ad.size() || cd.size() != ad.size() * 2)
      throw std::runtime_error("Invalid MFMA extents");
    Allocation a(ad), b(bd), c(cd), d(std::vector<char>(cd.size(), 0));
    hipLaunchKernelGGL(mfma, dim3(ad.size() / 512), dim3(64), 0, 0,
      static_cast<_Float16*>(a.payload()), static_cast<_Float16*>(b.payload()), static_cast<float*>(c.payload()), static_cast<float*>(d.payload()));
    check(hipGetLastError()); check(hipDeviceSynchronize());
    a.verify(true); b.verify(true); c.verify(true); write(out + "/mfma-actual.bin", d.verify(false));
    std::cout << "{\"status\":\"executed\",\"device\":\"" << prop.name
      << "\",\"warp\":" << prop.warpSize
      << ",\"inputs_unchanged\":true,\"guard_zones_unchanged\":true}\n";
    return 0;
  } catch (const std::exception& error) {
    std::cerr << error.what() << "\n"; return 1;
  }
}
