// Independent, deliberately simple HIP kernels. Not the paper's pinned programs.
#include <hip/hip_runtime.h>
#include <hip/hip_fp16.h>
#include <cmath>
#include <cstdio>

using H = __half;
__device__ float rd(const H* x, int i) { return __half2float(x[i]); }
__device__ void wr(H* x, int i, float v) { x[i] = __float2half(v); }

__global__ void elementwise(const H* x, H* out, int n, int op) {
  int i = blockIdx.x * blockDim.x + threadIdx.x;
  if (i >= n) return;
  float a = rd(x, i), v;
  if (op == 0) v = fmaxf(a, 0.0f);
  else if (op == 1) v = a / (1.0f + expf(-a));
  else v = 0.5f * a * (1.0f + tanhf(0.7978845608028654f * (a + 0.044715f*a*a*a)));
  wr(out, i, v);
}

// One complete reduction per block. All threads participate in every barrier.
__global__ void normalize(const H* x, H* out, int n, int op) {
  __shared__ float scratch[256];
  __shared__ float mean, denominator, maximum;
  int t = threadIdx.x;
  float v = op == 0 ? -INFINITY : 0.0f;
  for (int i=t; i<n; i+=blockDim.x) {
    float a=rd(x,i);
    if (op == 0) v=fmaxf(v,a);
    else if (op == 1) v+=a;
    else v+=a*a;
  }
  scratch[t]=v; __syncthreads();
  for (int step=128; step>0; step/=2) {
    if (t<step) scratch[t]=op==0 ? fmaxf(scratch[t],scratch[t+step]) : scratch[t]+scratch[t+step];
    __syncthreads();
  }
  if (t==0) {
    if (op==0) maximum=scratch[0];
    else if (op==1) mean=scratch[0]/n;
    else denominator=rsqrtf(scratch[0]/n+1e-5f);
  }
  __syncthreads();
  if (op!=2) {
    float sum=0.0f;
    for (int i=t;i<n;i+=blockDim.x) {
      float a=rd(x,i);
      sum += op==0 ? expf(a-maximum) : (a-mean)*(a-mean);
    }
    scratch[t]=sum; __syncthreads();
    for (int step=128;step>0;step/=2) {
      if (t<step) scratch[t]+=scratch[t+step];
      __syncthreads();
    }
    if (t==0) denominator=op==0 ? 1.0f/scratch[0] : rsqrtf(scratch[0]/n+1e-5f);
    __syncthreads();
  }
  for (int i=t;i<n;i+=blockDim.x) {
    float a=rd(x,i);
    wr(out,i,(op==0 ? expf(a-maximum) : op==1 ? a-mean : a)*denominator);
  }
}

__global__ void matmul(const H* a,const H* b,const H* bias,H* out,
                       int batches,int m,int k,int n) {
  int id=blockIdx.x*blockDim.x+threadIdx.x;
  if (id>=batches*m*n) return;
  int batch=id/(m*n), row=(id/n)%m, col=id%n;
  float v=0.0f;
  for (int j=0;j<k;++j) v+=rd(a,(batch*m+row)*k+j)*rd(b,(batch*k+j)*n+col);
  if (bias) v+=rd(bias,col);
  wr(out,id,v);
}

__global__ void convolution(const H* x,const H* w,H* out,int h,int cin,int cout,int k,int groups) {
  int oh=h-k+1, id=blockIdx.x*blockDim.x+threadIdx.x;
  if (id>=cout*oh*oh) return;
  int oc=id/(oh*oh), y=(id/oh)%oh, z=id%oh, channels=cin/groups;
  int group=oc/(cout/groups);
  float v=0.0f;
  for (int c=0;c<channels;++c)
    for (int ky=0;ky<k;++ky)
      for (int kx=0;kx<k;++kx)
        v+=rd(x,((group*channels+c)*h+y+ky)*h+z+kx)*rd(w,((oc*channels+c)*k+ky)*k+kx);
  wr(out,id,v);
}

__global__ void rotary(const H* x,const H* cosine,const H* sine,H* out,int s,int d) {
  int id=blockIdx.x*blockDim.x+threadIdx.x;
  if (id>=s*d/2) return;
  int row=id/(d/2),pair=id%(d/2),i=row*d+pair*2;
  float a=rd(x,i),b=rd(x,i+1),c=rd(cosine,id),sn=rd(sine,id);
  wr(out,i,a*c-b*sn); wr(out,i+1,a*sn+b*c);
}

__global__ void gate(const H* x,const H* w,const H* up,H* hidden,int m,int k,int n,int swiglu) {
  int id=blockIdx.x*blockDim.x+threadIdx.x;
  if (id>=m*n) return;
  int row=id/n,col=id%n;float a=0.0f,b=0.0f;
  for(int j=0;j<k;++j) {
    float v=rd(x,row*k+j); a+=v*rd(w,j*n+col);
    if(swiglu) b+=v*rd(up,j*n+col);
  }
  wr(hidden,id,swiglu ? a/(1.0f+expf(-a))*b : fmaxf(a,0.0f));
}

// Q/O: [heads, sequence, dimension]; K/V: [kv_heads, sequence, dimension].
// This is a straightforward attention implementation, not FlashAttention's algorithm.
__global__ void attention(const H* q,const H* k,const H* v,H* out,int s,int heads,int kvheads,int d) {
  __shared__ float scores[128], weights[128], denom;
  int row=blockIdx.x%s,head=blockIdx.x/s,kh=head/(heads/kvheads),t=threadIdx.x;
  if(t<s) {
    float value=0.0f;
    for(int j=0;j<d;++j) value+=rd(q,(head*s+row)*d+j)*rd(k,(kh*s+t)*d+j);
    scores[t]=value/sqrtf(float(d));
  }
  __syncthreads();
  if(t==0) {
    float maximum=scores[0];
    for(int j=1;j<s;++j) maximum=fmaxf(maximum,scores[j]);
    float sum=0.0f;
    for(int j=0;j<s;++j) { weights[j]=expf(scores[j]-maximum);sum+=weights[j]; }
    denom=sum;
  }
  __syncthreads();
  for(int j=t;j<d;j+=blockDim.x) {
    float value=0.0f;
    for(int z=0;z<s;++z) value+=weights[z]/denom*rd(v,(kh*s+z)*d+j);
    wr(out,(head*s+row)*d+j,value);
  }
}

extern "C" int lark_launch(int task,void** args,void* output,void* scratch,void* stream) {
  auto a=[&](int i){return static_cast<const H*>(args[i]);};
  auto o=static_cast<H*>(output);auto tmp=static_cast<H*>(scratch);auto st=static_cast<hipStream_t>(stream);
  if(task<3) hipLaunchKernelGGL(elementwise,dim3(64),dim3(256),0,st,a(0),o,16384,task);
  else if(task<6) hipLaunchKernelGGL(normalize,dim3(1),dim3(256),0,st,a(0),o,16384,task-3);
  else if(task==6) hipLaunchKernelGGL(matmul,dim3(2),dim3(256),0,st,a(0),a(1),nullptr,o,1,512,1024,1);
  else if(task==7 || task==8 || task==9) {
    int batches=task==8?32:1;
    hipLaunchKernelGGL(matmul,dim3((batches*64*512+255)/256),dim3(256),0,st,
                       a(0),a(1),task==9?a(2):nullptr,o,batches,64,256,512);
  } else if(task==10 || task==11) {
    int h=task==10?8:16,ci=32,co=task==10?8:32,k=task==10?3:5,g=task==10?1:32;
    hipLaunchKernelGGL(convolution,dim3((co*(h-k+1)*(h-k+1)+255)/256),dim3(256),0,st,a(0),a(1),o,h,ci,co,k,g);
  } else if(task==12) {
    hipLaunchKernelGGL(rotary,dim3(64),dim3(256),0,st,a(0),a(1),a(2),o,256,128);
  } else if(task==13 || task==14) {
    hipLaunchKernelGGL(gate,dim3(256),dim3(256),0,st,a(0),a(1),task==14?a(2):nullptr,tmp,64,256,1024,task==14);
    auto down=task==14?a(3):a(2);
    hipLaunchKernelGGL(matmul,dim3(64),dim3(256),0,st,tmp,down,nullptr,o,1,64,1024,256);
  } else if(task==15 || task==16) {
    int heads=task==15?1:8,kv=task==15?1:2,d=task==15?256:64;
    hipLaunchKernelGGL(attention,dim3(128*heads),dim3(256),0,st,a(0),a(1),a(2),o,128,heads,kv,d);
  } else return -1;
  return int(hipGetLastError());
}

// Plain per-operation programs, evaluated on separate operands to avoid FMA.
__global__ void scalar_ops(const float* a,const float* b,float* out,int n) {
  int i=blockIdx.x*blockDim.x+threadIdx.x;
  if(i<n) {out[i]=a[i]+b[i];out[n+i]=a[i]-b[i];out[2*n+i]=a[i]*b[i];out[3*n+i]=fmaxf(a[i],b[i]);}
}
extern "C" int lark_scalar(void* a,void* b,void* out,int n,void* stream) {
  hipLaunchKernelGGL(scalar_ops,dim3((n+255)/256),dim3(256),0,static_cast<hipStream_t>(stream),
                     static_cast<float*>(a),static_cast<float*>(b),static_cast<float*>(out),n);
  return int(hipGetLastError());
}
