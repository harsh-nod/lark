#include <hip/hip_runtime.h>
#include <hip/hip_fp16.h>
#include <cmath>
__global__ void scalar_probe(const float* x,const float* p,float* out,int n) {
 int i=blockIdx.x*blockDim.x+threadIdx.x;
 if(i<n) {out[i]=x[i]/p[i];out[n+i]=expf(x[i]);out[2*n+i]=tanhf(x[i]);out[3*n+i]=rsqrtf(p[i]);}
}
__global__ void decode_half(const __half* x,float* decoded,__half* roundtrip,int n) {
 int i=blockIdx.x*blockDim.x+threadIdx.x;
 if(i<n) {float v=__half2float(x[i]);decoded[i]=v;roundtrip[i]=__float2half(v);}
}
__global__ void encode_half(const float* x,__half* out,int n) {
 int i=blockIdx.x*blockDim.x+threadIdx.x;
 if(i<n) out[i]=__float2half(x[i]);
}
extern "C" int probe(int kind,void* a,void* b,void* c,int n) {
 if(kind==0) hipLaunchKernelGGL(scalar_probe,dim3((n+255)/256),dim3(256),0,0,(float*)a,(float*)b,(float*)c,n);
 else if(kind==1) hipLaunchKernelGGL(decode_half,dim3((n+255)/256),dim3(256),0,0,(__half*)a,(float*)b,(__half*)c,n);
 else if(kind==2) hipLaunchKernelGGL(encode_half,dim3((n+255)/256),dim3(256),0,0,(float*)a,(__half*)b,n);
 else return -1;
 return int(hipGetLastError());
}
