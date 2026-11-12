#include <hip/hip_runtime.h>
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
template <int64_t kDim, bool kUsePDL, typename Float>
__global__ __launch_bounds__(kDim / 16) void rmsnorm_cta_double(const RMSNormParams __grid_constant__ params) {
  using namespace device;
  using Float2 = packed_t<Float>;
  using Storage = AlignedVector<Float2, 4>;

  constexpr auto kNumThreads = kDim / 16;
  constexpr auto kNumWarps = kNumThreads / kWarpThreads;

  const auto& [input, weight_ptr, output, input_stride, output_stride, num_tokens, eps] = params;
  const auto gmem = tile::Memory<Storage>::cta(kNumThreads);
  __shared__ float smem[32];

  PDLWaitPrimary<kUsePDL>();

  const auto input_ptr = pointer::offset<Float>(input, blockIdx.x * input_stride);
  const auto output_ptr = pointer::offset<Float>(output, blockIdx.x * output_stride);

  const auto input_first = gmem.load(input_ptr, 0);
  const auto input_second = gmem.load(input_ptr, 1);
  const auto weight_first = gmem.load(weight_ptr, 0);
  const auto weight_second = gmem.load(weight_ptr, 1);

  float sum_of_squares = 0.0f;
#pragma unroll
  for (auto j = 0u; j < 4u; ++j) {
    const auto [x, y] = cast<fp32x2_t>(input_first[j]);
    sum_of_squares += x * x + y * y;
  }
#pragma unroll
  for (auto j = 0u; j < 4u; ++j) {
    const auto [x, y] = cast<fp32x2_t>(input_second[j]);
    sum_of_squares += x * x + y * y;
  }

  sum_of_squares = warp::reduce_sum(sum_of_squares);
  float norm_factor;
  if constexpr (kNumWarps == 1) {
    norm_factor = math::rsqrt(sum_of_squares / kDim + eps);
  } else {
    const auto warp_id = threadIdx.x / kWarpThreads;
    smem[warp_id] = sum_of_squares;
    __syncthreads();
    if (warp_id == 0) {
      const auto tx = threadIdx.x;
      const auto local_sum = tx < kNumWarps ? smem[tx] : 0.0f;
      sum_of_squares = warp::reduce_sum(local_sum);
      smem[tx] = math::rsqrt(sum_of_squares / kDim + eps);
    }
    __syncthreads();
    norm_factor = smem[warp_id];
  }

  Storage output_first, output_second;
#pragma unroll
  for (auto j = 0u; j < 4u; ++j) {
    const auto [ix, iy] = cast<fp32x2_t>(input_first[j]);
    const auto [wx, wy] = cast<fp32x2_t>(weight_first[j]);
    output_first[j] = cast<Float2>(fp32x2_t{ix * norm_factor * wx, iy * norm_factor * wy});
  }
#pragma unroll
  for (auto j = 0u; j < 4u; ++j) {
    const auto [ix, iy] = cast<fp32x2_t>(input_second[j]);
    const auto [wx, wy] = cast<fp32x2_t>(weight_second[j]);
    output_second[j] = cast<Float2>(fp32x2_t{ix * norm_factor * wx, iy * norm_factor * wy});
  }

  gmem.store(output_ptr, output_first, 0);
  gmem.store(output_ptr, output_second, 1);

  PDLTriggerSecondary<kUsePDL>();
}
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
