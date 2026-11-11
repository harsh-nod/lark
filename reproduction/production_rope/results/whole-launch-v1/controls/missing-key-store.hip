// Independent vLLM adaptation; upstream Apache-2.0 license in ../../upstream/LICENSE.
extern "C" __global__ void rotary_embedding(__half* query, __half* key, const __half* cache) {
  int token = blockIdx.x;
  int qi = threadIdx.x;
  while (qi < 2048) {
    int qh = qi / 64;
    int qr = qi % 64;
    int qx = 2 * qr;
    int qy = 2 * qr + 1;
    int qca = token * 128 + qr;
    int qcb = qca + 64;
    float qc = __half2float(cache[qca]);
    float qs = __half2float(cache[qcb]);
    int qa = token * 4096 + qh * 128 + qx;
    int qb = token * 4096 + qh * 128 + qy;
    float qxf = __half2float(query[qa]);
    float qyf = __half2float(query[qb]);
    float qxc = qxf * qc;
    float qys = qyf * qs;
    float qyc = qyf * qc;
    float qxs = qxf * qs;
    float qox = qxc - qys;
    float qoy = qyc + qxs;
    query[qa] = __float2half(qox);
    query[qb] = __float2half(qoy);
    qi = qi + 512;
  }
  int ki = threadIdx.x;
  while (ki < 512) {
    int kh = ki / 64;
    int kr = ki % 64;
    int kx = 2 * kr;
    int ky = 2 * kr + 1;
    int kca = token * 128 + kr;
    int kcb = kca + 64;
    float kc = __half2float(cache[kca]);
    float ks = __half2float(cache[kcb]);
    int ka = token * 1024 + kh * 128 + kx;
    int kb = token * 1024 + kh * 128 + ky;
    float kxf = __half2float(key[ka]);
    float kyf = __half2float(key[kb]);
    float kxc = kxf * kc;
    float kys = kyf * ks;
    float kyc = kyf * kc;
    float kxs = kxf * ks;
    float kox = kxc - kys;
    float koy = kyc + kxs;
    key[ka] = __float2half(kox);
    ki = ki + 512;
  }
}
