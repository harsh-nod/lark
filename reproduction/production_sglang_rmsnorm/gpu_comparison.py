"""Freeze the two SGLang adaptations and a verbatim upstream-body HIP comparison.

This prepares compilation inputs only; no GPU trial or source certificate is
issued. Comparison helpers replace CUDA runtime/vector/cast/reduction helpers.
"""

import argparse
import hashlib
import json
from pathlib import Path
import shutil
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from lark_kernels import native_sglang_rmsnorm as native

HERE = Path(__file__).resolve().parent
UPSTREAM = HERE / "upstream"
BODY_PATH = "python/sglang/kernels/jit/csrc/elementwise/rmsnorm.cuh"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def upstream_body():
    text = (UPSTREAM / BODY_PATH).read_text()
    signature = text.index("void rmsnorm_cta_double(")
    start = text.rindex("template <", 0, signature)
    begin = text.index("{", signature)
    depth, end = 1, begin + 1
    while depth:
        depth += (text[end] == "{") - (text[end] == "}")
        end += 1
    return text[start:end]


def driver():
    prefix = r'''#include <hip/hip_runtime.h>
#include <hip/hip_fp16.h>
#include <cstdint>
#include <cmath>
#include <type_traits>
#define sglang_rmsnorm sglang_original
#include "kernel_original.hip"
#undef sglang_rmsnorm
#define sglang_rmsnorm sglang_fixed
#include "kernel_fixed.hip"
#undef sglang_rmsnorm
#ifndef __grid_constant__
#define __grid_constant__
#endif
// Explicit HIP comparison helpers; no CUDA helper/compiler equivalence claimed.
namespace comparison {
struct RMSNormParams {
  const void* input;
  const void* __restrict__ weight;
  void* output;
  int64_t input_stride;
  int64_t output_stride;
  uint32_t num_tokens;
  float eps;
};
struct fp32x2_t { float x,y; };
namespace device {
inline constexpr uint32_t kWarpThreads = 32u;
template<typename T> struct PackedType;
template<> struct PackedType<__half> {using type=__half2;};
template<typename T> using packed_t=typename PackedType<T>::type;
template<typename T,int N> struct alignas(sizeof(T)*N) AlignedVector {
  T value[N];
  __device__ T& operator[](uint32_t j) {return value[j];}
  __device__ const T& operator[](uint32_t j) const {return value[j];}
};
static_assert(sizeof(AlignedVector<__half2,4>)==16);
namespace tile {
template<typename T> struct Memory {
  uint32_t tid,tsize;
  __device__ static Memory cta(int count) {return {threadIdx.x,(uint32_t)count};}
  __device__ T load(const void* ptr,int64_t offset=0) const {return static_cast<const T*>(ptr)[tid+offset*tsize];}
  __device__ void store(void* ptr,T value,int64_t offset=0) const {static_cast<T*>(ptr)[tid+offset*tsize]=value;}
};
}
namespace pointer {
template<typename T> __device__ const T* offset(const void* ptr,int64_t n) {return static_cast<const T*>(ptr)+n;}
template<typename T> __device__ T* offset(void* ptr,int64_t n) {return static_cast<T*>(ptr)+n;}
}
namespace warp {
__device__ inline float reduce_sum(float value) {
#pragma unroll
  for(uint32_t mask=16;mask;mask>>=1)value=value+__shfl_xor(value,mask,32);
  return value;
}
}
namespace math { __device__ inline float rsqrt(float value) {return rsqrtf(value);} }
template<bool Enabled> __device__ inline void PDLWaitPrimary() {static_assert(!Enabled);}
template<bool Enabled> __device__ inline void PDLTriggerSecondary() {static_assert(!Enabled);}
template<typename To,typename From> __device__ To cast(const From& value) {
  if constexpr(std::is_same_v<To,fp32x2_t>) {
    static_assert(std::is_same_v<From,__half2>);
    const auto converted=__half22float2(value);
    return {converted.x,converted.y};
  } else {
    static_assert(std::is_same_v<To,__half2> && std::is_same_v<From,fp32x2_t>);
    return __float22half2_rn(make_float2(value.x,value.y));
  }
}
}
'''
    suffix = r'''
}
extern "C" int run_case(int rows,void* original,void* input,void* weight,void* fixed,void* upstream) {
  hipLaunchKernelGGL(sglang_original,dim3(rows),dim3(1024),0,0,
    (__half*)original,(const __half*)input,(const __half*)weight);
  hipError_t e=hipGetLastError();if(e!=hipSuccess)return (int)e;
  hipLaunchKernelGGL(sglang_fixed,dim3(rows),dim3(1024),0,0,
    (__half*)fixed,(const __half*)input,(const __half*)weight);
  e=hipGetLastError();if(e!=hipSuccess)return (int)e;
  comparison::RMSNormParams params={input,weight,upstream,16384,16384,(uint32_t)rows,0.00001f};
  hipLaunchKernelGGL((comparison::rmsnorm_cta_double<16384,false,__half>),dim3(rows),dim3(1024),0,0,params);
  return (int)hipGetLastError();
}
extern "C" int runtime_attribute(int which) {
  hipDeviceProp_t p;if(hipGetDeviceProperties(&p,0)!=hipSuccess)return -1;
  return which==0?p.warpSize:which==1?p.maxThreadsPerBlock:which==2?p.sharedMemPerBlock:-1;
}
extern "C" const char* runtime_architecture() {
  static hipDeviceProp_t p;if(hipGetDeviceProperties(&p,0)!=hipSuccess)return "unknown";
  return p.gcnArchName;
}
'''
    return prefix + upstream_body() + suffix


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    out = args.output.resolve()
    if out.is_relative_to(ROOT):
        raise ValueError("Frozen compilation directory outside checkout required")
    out.mkdir(parents=True, exist_ok=False)
    provenance = json.loads((HERE / "provenance.json").read_text())
    for record in provenance["upstream_files"]:
        raw = (UPSTREAM / record["path"]).read_bytes()
        if (len(raw) != record["bytes"] or hashlib.sha256(raw).hexdigest() != record["sha256"]
                or hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest() != record["git_blob"]):
            raise ValueError("Pinned upstream source differs: " + record["path"])
    records = {}
    for variant, count, filename in (("native_original",109,"kernel_original.hip"),("native_fixed",110,"kernel_fixed.hip")):
        case = HERE / "cases" / variant
        task = native.parse_task((case / "task.json").read_text())
        native.check_reference((case / "reference.py").read_text())
        tr = native.translate((case / "kernel.hip").read_text(), task)
        if len(tr.program) != count:
            raise ValueError("Source instruction count differs")
        shutil.copyfile(case / "kernel.hip", out / filename)
        records[variant] = {"source_sha256":sha(out / filename),"instructions":count}
    shutil.copytree(UPSTREAM, out / "upstream")
    (out / "driver.hip").write_text(driver())
    if driver().count(upstream_body()) != 1:
        raise ValueError("Upstream body was not retained exactly once")
    report = {
        "schema":1,"status":"native-sglang-rmsnorm-three-method-compilation-inputs-frozen",
        "upstream_repo":provenance["repo"],"upstream_commit":provenance["commit"],"sources":records,
        "body_sha256":hashlib.sha256(upstream_body().encode()).hexdigest(),
        "driver_sha256":sha(out / "driver.hip"),"block":1024,"physical_warp":64,"logical_warp":32,
        "comparison_helpers":"Explicit HIP 16-byte aligned half2 vectors, logical32 XOR, rsqrtf, half2 conversion, plain float pair, and PDL=false no-ops; original template body retained verbatim",
        "original_nvidia_kernel_executed":False,"source_certificates":0,"model_calls":0,"gpu_trials":0,
        "original_paper_fully_reproduced":False,
    }
    (out / "results.json").write_text(json.dumps(report,indent=2)+"\n")
    (out / "manifest.json").write_text(json.dumps({str(p.relative_to(out)):sha(p) for p in sorted(out.rglob("*")) if p.is_file()},indent=2)+"\n")
    print(json.dumps({"status":report["status"],"driver_sha256":report["driver_sha256"],"gpu_trials":0}))


if __name__ == "__main__":
    main()
