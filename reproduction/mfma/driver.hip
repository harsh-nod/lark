#include <hip/hip_runtime.h>
#include <cstring>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>
#include "cases/gemm16/kernel.hip"

static void check(hipError_t code) {
  if (code != hipSuccess) throw std::runtime_error(hipGetErrorString(code));
}

static std::vector<char> read(const std::string& path) {
  std::ifstream f(path, std::ios::binary | std::ios::ate);
  if (!f) throw std::runtime_error("Cannot open data");
  const size_t size = f.tellg(); f.seekg(0);
  std::vector<char> bytes(size); f.read(bytes.data(), size);
  if (!f) throw std::runtime_error("Incomplete data");
  return bytes;
}

struct Tiles {
  char* base = nullptr;
  size_t bytes, count, stride;
  std::vector<char> original;
  Tiles(const std::vector<char>& values, size_t payload) :
      bytes(payload), count(values.size()/payload), stride(payload+256), original(count*stride, char(0x5a)) {
    if (values.empty() || values.size()%bytes) throw std::runtime_error("Invalid tile extents");
    for (size_t i=0; i<count; ++i) std::memcpy(original.data()+i*stride+128, values.data()+i*bytes, bytes);
    check(hipMalloc(reinterpret_cast<void**>(&base), original.size()));
    check(hipMemcpy(base, original.data(), original.size(), hipMemcpyHostToDevice));
  }
  void* payload(size_t trial) { return base+trial*stride+128; }
  std::vector<char> verify(bool input) {
    std::vector<char> actual(original.size()), flat(count*bytes);
    check(hipMemcpy(actual.data(), base, actual.size(), hipMemcpyDeviceToHost));
    if (input && actual != original) throw std::runtime_error("Input bytes changed");
    for (size_t i=0; i<count; ++i) {
      const size_t start = i*stride;
      if (std::memcmp(actual.data()+start, original.data()+start, 128) ||
          std::memcmp(actual.data()+start+128+bytes, original.data()+start+128+bytes, 128))
        throw std::runtime_error("A tile guard changed");
      std::memcpy(flat.data()+i*bytes, actual.data()+start+128, bytes);
    }
    return flat;
  }
  ~Tiles() { if (base) hipFree(base); }
};

int main(int argc, char** argv) {
  try {
    if (argc != 3) throw std::runtime_error("Expected data and output directories");
    const std::string data=argv[1], out=argv[2];
    hipDeviceProp_t prop; check(hipGetDeviceProperties(&prop, 0));
    if (prop.warpSize != 64) throw std::runtime_error("Wave64 required");
    const auto av=read(data+"/a.bin"), bv=read(data+"/b.bin"), cv=read(data+"/c.bin");
    if (av.size()!=bv.size() || av.size()*2!=cv.size()) throw std::runtime_error("Input extents differ");
    Tiles a(av,512), b(bv,512), c(cv,1024), d(std::vector<char>(cv.size(),0),1024);
    for (size_t trial=0; trial<a.count; ++trial) {
      hipLaunchKernelGGL(mfma_tile, dim3(1), dim3(64), 0, 0,
        static_cast<const _Float16*>(a.payload(trial)), static_cast<const _Float16*>(b.payload(trial)),
        static_cast<const float*>(c.payload(trial)), static_cast<float*>(d.payload(trial)));
      check(hipGetLastError());
    }
    check(hipDeviceSynchronize());
    a.verify(true); b.verify(true); c.verify(true);
    auto result=d.verify(false);
    std::ofstream f(out+"/actual.bin",std::ios::binary); f.write(result.data(),result.size());
    if (!f) throw std::runtime_error("Cannot write output");
    std::cout << "{\"device\":\"" << prop.name << "\",\"architecture\":\"" << prop.gcnArchName
      << "\",\"warp\":" << prop.warpSize << ",\"trials\":" << a.count
      << ",\"inputs_unchanged\":true,\"per_tile_guard_zones_unchanged\":true}" << std::endl;
    return 0;
  } catch (const std::exception& e) { std::cerr << e.what() << std::endl; return 1; }
}
