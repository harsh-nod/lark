// SPDX-License-Identifier: Apache-2.0
// Independently adapted from flash-attention-minimal at 00f8f46712d493665c900c32fa3a261c8ef3e20c.
// Native tile32, N128/D256. Development source; no complete Lean certificate yet.
extern "C" __global__ void online_attention(__half* out, const __half* query,
                                          const __half* key, const __half* value) {
  __shared__ float qi[8192];
  __shared__ float kj[8192];
  __shared__ float vj[8192];
  __shared__ float scores[1024];
  float running_m[4];
  float running_l[4];
  int group = blockIdx.x;
  int lane = threadIdx.x;
  int base = group * 32768;
  int init_i = 0;
  while (init_i < 4) {
    int init_x = 0;
    while (init_x < 256) {
      out[base + (init_i * 32 + lane) * 256 + init_x] = __float2half(0.0f);
      init_x = init_x + 1;
    }
    init_i = init_i + 1;
  }
  int tile_j = 0;
  while (tile_j < 4) {
    int load_x = 0;
    while (load_x < 256) {
      kj[lane * 256 + load_x] = __half2float(key[base + tile_j * 8192 + lane * 256 + load_x]);
      vj[lane * 256 + load_x] = __half2float(value[base + tile_j * 8192 + lane * 256 + load_x]);
      load_x = load_x + 1;
    }
    __syncthreads();
    int tile_i = 0;
    while (tile_i < 4) {
      int query_x = 0;
      while (query_x < 256) {
        qi[lane * 256 + query_x] = __half2float(query[base + tile_i * 8192 + lane * 256 + query_x]);
        query_x = query_x + 1;
      }
      float row_m = 0.0f;
      int score_y = 0;
      while (score_y < 32) {
        float sum = 0.0f;
        int score_x = 0;
        while (score_x < 256) {
          float qv = qi[lane * 256 + score_x];
          float kv = kj[score_y * 256 + score_x];
          float product = qv * kv;
          sum = sum + product;
          score_x = score_x + 1;
        }
        sum = sum * 0.0625f;
        scores[lane * 32 + score_y] = sum;
        if (score_y == 0) { row_m = sum; }
        else { row_m = fmaxf(row_m, sum); }
        score_y = score_y + 1;
      }
      float row_l = 0.0f;
      int exp_y = 0;
      while (exp_y < 32) {
        float probability = expf(scores[lane * 32 + exp_y] - row_m);
        scores[lane * 32 + exp_y] = probability;
        row_l = row_l + probability;
        exp_y = exp_y + 1;
      }
      float old_m = row_m;
      float old_l = 0.0f;
      if (tile_j > 0) {
        old_m = running_m[tile_i];
        old_l = running_l[tile_i];
      }
      float new_m = fmaxf(old_m, row_m);
      float old_scale = expf(old_m - new_m);
      float tile_scale = expf(row_m - new_m);
      float new_l = old_scale * old_l + tile_scale * row_l;
      int out_x = 0;
      while (out_x < 256) {
        float pv = 0.0f;
        int value_y = 0;
        while (value_y < 32) {
          float prob = scores[lane * 32 + value_y];
          float vv = vj[value_y * 256 + out_x];
          float term = prob * vv;
          pv = pv + term;
          value_y = value_y + 1;
        }
        float old_o = __half2float(out[base + tile_i * 8192 + lane * 256 + out_x]);
        float old_weighted = old_l * old_scale * old_o;
        float new_weighted = tile_scale * pv;
        float result = (1.0f / new_l) * (old_weighted + new_weighted);
        out[base + tile_i * 8192 + lane * 256 + out_x] = __float2half(result);
        out_x = out_x + 1;
      }
      running_m[tile_i] = new_m;
      running_l[tile_i] = new_l;
      tile_i = tile_i + 1;
    }
    __syncthreads();
    tile_j = tile_j + 1;
  }
}
