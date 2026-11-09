extern "C" __global__ void verify_llmc_race(const float* x, float* out) {
int t = threadIdx.x;
if (t < 3) { out[t] = x[t]; }
__syncthreads();
int a = t;
if (t >= 3) { a = 2; }
float yh = out[a];
if (t < 3) { out[t] = yh; }
}
