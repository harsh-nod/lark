using H4 = _Float16 __attribute__((ext_vector_type(4)));
using F4 = float __attribute__((ext_vector_type(4)));

extern "C" __global__ void awq_fp16_gemm(const _Float16* a, const _Float16* b, _Float16* out) {
  __shared__ _Float16 tileA[640];
  __shared__ _Float16 tileB[4352];
  int lane = threadIdx.x;
  int logicalLane = lane % 32;
  int logicalWarp = lane / 32;
  int block = blockIdx.x;
  int blockRow = block / 2;
  int blockCol = block % 2;
  int inputRow = blockRow * 16 + logicalWarp * 8 + logicalLane / 4;
  int inputCol = (logicalLane % 4) * 8;
  int sharedABase = (logicalWarp * 8 + logicalLane / 4) * 40 + inputCol;
  int outputRow0 = blockRow * 16 + (lane / 16) * 4 + 0;
  int outputRow1 = blockRow * 16 + (lane / 16) * 4 + 1;
  int outputRow2 = blockRow * 16 + (lane / 16) * 4 + 2;
  int outputRow3 = blockRow * 16 + (lane / 16) * 4 + 3;
  F4 acc0 = {0.0f, 0.0f, 0.0f, 0.0f};
  F4 acc1 = {0.0f, 0.0f, 0.0f, 0.0f};
  F4 acc2 = {0.0f, 0.0f, 0.0f, 0.0f};
  F4 acc3 = {0.0f, 0.0f, 0.0f, 0.0f};
  F4 acc4 = {0.0f, 0.0f, 0.0f, 0.0f};
  F4 acc5 = {0.0f, 0.0f, 0.0f, 0.0f};
  F4 acc6 = {0.0f, 0.0f, 0.0f, 0.0f};
  F4 acc7 = {0.0f, 0.0f, 0.0f, 0.0f};
  int kTile = 0;
  while (kTile < 2) {
    __syncthreads();
    int ae = 0;
    if (inputRow < 33) {
      while (ae < 8) {
        tileA[sharedABase + ae] = a[inputRow * 64 + kTile * 32 + inputCol + ae];
        ae++;
      }
    } else {
      while (ae < 8) {
        tileA[sharedABase + ae] = __float2half(0.0f);
        ae++;
      }
    }
    int chunk = 0;
    while (chunk < 8) {
      int bRow = logicalWarp * 2 + logicalLane / 16 + chunk * 4;
      int bCol = (logicalLane % 16) * 8;
      int be = 0;
      while (be < 8) {
        tileB[bRow * 136 + bCol + be] = b[(kTile * 32 + bRow) * 256 + blockCol * 128 + bCol + be];
        be++;
      }
      chunk++;
    }
    __syncthreads();
    H4 left0 = {tileA[(lane % 16) * 40 + 0 + (lane / 16) * 4 + 0], tileA[(lane % 16) * 40 + 0 + (lane / 16) * 4 + 1], tileA[(lane % 16) * 40 + 0 + (lane / 16) * 4 + 2], tileA[(lane % 16) * 40 + 0 + (lane / 16) * 4 + 3]};
    H4 right0_0 = {tileB[(0 + (lane / 16) * 4 + 0) * 136 + 0 + lane % 16], tileB[(0 + (lane / 16) * 4 + 1) * 136 + 0 + lane % 16], tileB[(0 + (lane / 16) * 4 + 2) * 136 + 0 + lane % 16], tileB[(0 + (lane / 16) * 4 + 3) * 136 + 0 + lane % 16]};
    acc0 = __builtin_amdgcn_mfma_f32_16x16x16f16(left0, right0_0, acc0, 0, 0, 0);
    H4 right0_1 = {tileB[(0 + (lane / 16) * 4 + 0) * 136 + 16 + lane % 16], tileB[(0 + (lane / 16) * 4 + 1) * 136 + 16 + lane % 16], tileB[(0 + (lane / 16) * 4 + 2) * 136 + 16 + lane % 16], tileB[(0 + (lane / 16) * 4 + 3) * 136 + 16 + lane % 16]};
    acc1 = __builtin_amdgcn_mfma_f32_16x16x16f16(left0, right0_1, acc1, 0, 0, 0);
    H4 right0_2 = {tileB[(0 + (lane / 16) * 4 + 0) * 136 + 32 + lane % 16], tileB[(0 + (lane / 16) * 4 + 1) * 136 + 32 + lane % 16], tileB[(0 + (lane / 16) * 4 + 2) * 136 + 32 + lane % 16], tileB[(0 + (lane / 16) * 4 + 3) * 136 + 32 + lane % 16]};
    acc2 = __builtin_amdgcn_mfma_f32_16x16x16f16(left0, right0_2, acc2, 0, 0, 0);
    H4 right0_3 = {tileB[(0 + (lane / 16) * 4 + 0) * 136 + 48 + lane % 16], tileB[(0 + (lane / 16) * 4 + 1) * 136 + 48 + lane % 16], tileB[(0 + (lane / 16) * 4 + 2) * 136 + 48 + lane % 16], tileB[(0 + (lane / 16) * 4 + 3) * 136 + 48 + lane % 16]};
    acc3 = __builtin_amdgcn_mfma_f32_16x16x16f16(left0, right0_3, acc3, 0, 0, 0);
    H4 right0_4 = {tileB[(0 + (lane / 16) * 4 + 0) * 136 + 64 + lane % 16], tileB[(0 + (lane / 16) * 4 + 1) * 136 + 64 + lane % 16], tileB[(0 + (lane / 16) * 4 + 2) * 136 + 64 + lane % 16], tileB[(0 + (lane / 16) * 4 + 3) * 136 + 64 + lane % 16]};
    acc4 = __builtin_amdgcn_mfma_f32_16x16x16f16(left0, right0_4, acc4, 0, 0, 0);
    H4 right0_5 = {tileB[(0 + (lane / 16) * 4 + 0) * 136 + 80 + lane % 16], tileB[(0 + (lane / 16) * 4 + 1) * 136 + 80 + lane % 16], tileB[(0 + (lane / 16) * 4 + 2) * 136 + 80 + lane % 16], tileB[(0 + (lane / 16) * 4 + 3) * 136 + 80 + lane % 16]};
    acc5 = __builtin_amdgcn_mfma_f32_16x16x16f16(left0, right0_5, acc5, 0, 0, 0);
    H4 right0_6 = {tileB[(0 + (lane / 16) * 4 + 0) * 136 + 96 + lane % 16], tileB[(0 + (lane / 16) * 4 + 1) * 136 + 96 + lane % 16], tileB[(0 + (lane / 16) * 4 + 2) * 136 + 96 + lane % 16], tileB[(0 + (lane / 16) * 4 + 3) * 136 + 96 + lane % 16]};
    acc6 = __builtin_amdgcn_mfma_f32_16x16x16f16(left0, right0_6, acc6, 0, 0, 0);
    H4 right0_7 = {tileB[(0 + (lane / 16) * 4 + 0) * 136 + 112 + lane % 16], tileB[(0 + (lane / 16) * 4 + 1) * 136 + 112 + lane % 16], tileB[(0 + (lane / 16) * 4 + 2) * 136 + 112 + lane % 16], tileB[(0 + (lane / 16) * 4 + 3) * 136 + 112 + lane % 16]};
    acc7 = __builtin_amdgcn_mfma_f32_16x16x16f16(left0, right0_7, acc7, 0, 0, 0);
    H4 left1 = {tileA[(lane % 16) * 40 + 16 + (lane / 16) * 4 + 0], tileA[(lane % 16) * 40 + 16 + (lane / 16) * 4 + 1], tileA[(lane % 16) * 40 + 16 + (lane / 16) * 4 + 2], tileA[(lane % 16) * 40 + 16 + (lane / 16) * 4 + 3]};
    H4 right1_0 = {tileB[(16 + (lane / 16) * 4 + 0) * 136 + 0 + lane % 16], tileB[(16 + (lane / 16) * 4 + 1) * 136 + 0 + lane % 16], tileB[(16 + (lane / 16) * 4 + 2) * 136 + 0 + lane % 16], tileB[(16 + (lane / 16) * 4 + 3) * 136 + 0 + lane % 16]};
    acc0 = __builtin_amdgcn_mfma_f32_16x16x16f16(left1, right1_0, acc0, 0, 0, 0);
    H4 right1_1 = {tileB[(16 + (lane / 16) * 4 + 0) * 136 + 16 + lane % 16], tileB[(16 + (lane / 16) * 4 + 1) * 136 + 16 + lane % 16], tileB[(16 + (lane / 16) * 4 + 2) * 136 + 16 + lane % 16], tileB[(16 + (lane / 16) * 4 + 3) * 136 + 16 + lane % 16]};
    acc1 = __builtin_amdgcn_mfma_f32_16x16x16f16(left1, right1_1, acc1, 0, 0, 0);
    H4 right1_2 = {tileB[(16 + (lane / 16) * 4 + 0) * 136 + 32 + lane % 16], tileB[(16 + (lane / 16) * 4 + 1) * 136 + 32 + lane % 16], tileB[(16 + (lane / 16) * 4 + 2) * 136 + 32 + lane % 16], tileB[(16 + (lane / 16) * 4 + 3) * 136 + 32 + lane % 16]};
    acc2 = __builtin_amdgcn_mfma_f32_16x16x16f16(left1, right1_2, acc2, 0, 0, 0);
    H4 right1_3 = {tileB[(16 + (lane / 16) * 4 + 0) * 136 + 48 + lane % 16], tileB[(16 + (lane / 16) * 4 + 1) * 136 + 48 + lane % 16], tileB[(16 + (lane / 16) * 4 + 2) * 136 + 48 + lane % 16], tileB[(16 + (lane / 16) * 4 + 3) * 136 + 48 + lane % 16]};
    acc3 = __builtin_amdgcn_mfma_f32_16x16x16f16(left1, right1_3, acc3, 0, 0, 0);
    H4 right1_4 = {tileB[(16 + (lane / 16) * 4 + 0) * 136 + 64 + lane % 16], tileB[(16 + (lane / 16) * 4 + 1) * 136 + 64 + lane % 16], tileB[(16 + (lane / 16) * 4 + 2) * 136 + 64 + lane % 16], tileB[(16 + (lane / 16) * 4 + 3) * 136 + 64 + lane % 16]};
    acc4 = __builtin_amdgcn_mfma_f32_16x16x16f16(left1, right1_4, acc4, 0, 0, 0);
    H4 right1_5 = {tileB[(16 + (lane / 16) * 4 + 0) * 136 + 80 + lane % 16], tileB[(16 + (lane / 16) * 4 + 1) * 136 + 80 + lane % 16], tileB[(16 + (lane / 16) * 4 + 2) * 136 + 80 + lane % 16], tileB[(16 + (lane / 16) * 4 + 3) * 136 + 80 + lane % 16]};
    acc5 = __builtin_amdgcn_mfma_f32_16x16x16f16(left1, right1_5, acc5, 0, 0, 0);
    H4 right1_6 = {tileB[(16 + (lane / 16) * 4 + 0) * 136 + 96 + lane % 16], tileB[(16 + (lane / 16) * 4 + 1) * 136 + 96 + lane % 16], tileB[(16 + (lane / 16) * 4 + 2) * 136 + 96 + lane % 16], tileB[(16 + (lane / 16) * 4 + 3) * 136 + 96 + lane % 16]};
    acc6 = __builtin_amdgcn_mfma_f32_16x16x16f16(left1, right1_6, acc6, 0, 0, 0);
    H4 right1_7 = {tileB[(16 + (lane / 16) * 4 + 0) * 136 + 112 + lane % 16], tileB[(16 + (lane / 16) * 4 + 1) * 136 + 112 + lane % 16], tileB[(16 + (lane / 16) * 4 + 2) * 136 + 112 + lane % 16], tileB[(16 + (lane / 16) * 4 + 3) * 136 + 112 + lane % 16]};
    acc7 = __builtin_amdgcn_mfma_f32_16x16x16f16(left1, right1_7, acc7, 0, 0, 0);
    kTile++;
  }
  if (outputRow0 < 33) {
    out[outputRow0 * 256 + blockCol * 128 + 0 + lane % 16] = __float2half(acc0[0]);
  }
  if (outputRow1 < 33) {
    out[outputRow1 * 256 + blockCol * 128 + 0 + lane % 16] = __float2half(acc0[1]);
  }
  if (outputRow2 < 33) {
    out[outputRow2 * 256 + blockCol * 128 + 0 + lane % 16] = __float2half(acc0[2]);
  }
  if (outputRow3 < 33) {
    out[outputRow3 * 256 + blockCol * 128 + 0 + lane % 16] = __float2half(acc0[3]);
  }
  if (outputRow0 < 33) {
    out[outputRow0 * 256 + blockCol * 128 + 16 + lane % 16] = __float2half(acc1[0]);
  }
  if (outputRow1 < 33) {
    out[outputRow1 * 256 + blockCol * 128 + 16 + lane % 16] = __float2half(acc1[1]);
  }
  if (outputRow2 < 33) {
    out[outputRow2 * 256 + blockCol * 128 + 16 + lane % 16] = __float2half(acc1[2]);
  }
  if (outputRow3 < 33) {
    out[outputRow3 * 256 + blockCol * 128 + 16 + lane % 16] = __float2half(acc1[3]);
  }
  if (outputRow0 < 33) {
    out[outputRow0 * 256 + blockCol * 128 + 32 + lane % 16] = __float2half(acc2[0]);
  }
  if (outputRow1 < 33) {
    out[outputRow1 * 256 + blockCol * 128 + 32 + lane % 16] = __float2half(acc2[1]);
  }
  if (outputRow2 < 33) {
    out[outputRow2 * 256 + blockCol * 128 + 32 + lane % 16] = __float2half(acc2[2]);
  }
  if (outputRow3 < 33) {
    out[outputRow3 * 256 + blockCol * 128 + 32 + lane % 16] = __float2half(acc2[3]);
  }
  if (outputRow0 < 33) {
    out[outputRow0 * 256 + blockCol * 128 + 48 + lane % 16] = __float2half(acc3[0]);
  }
  if (outputRow1 < 33) {
    out[outputRow1 * 256 + blockCol * 128 + 48 + lane % 16] = __float2half(acc3[1]);
  }
  if (outputRow2 < 33) {
    out[outputRow2 * 256 + blockCol * 128 + 48 + lane % 16] = __float2half(acc3[2]);
  }
  if (outputRow3 < 33) {
    out[outputRow3 * 256 + blockCol * 128 + 48 + lane % 16] = __float2half(acc3[3]);
  }
  if (outputRow0 < 33) {
    out[outputRow0 * 256 + blockCol * 128 + 64 + lane % 16] = __float2half(acc4[0]);
  }
  if (outputRow1 < 33) {
    out[outputRow1 * 256 + blockCol * 128 + 64 + lane % 16] = __float2half(acc4[1]);
  }
  if (outputRow2 < 33) {
    out[outputRow2 * 256 + blockCol * 128 + 64 + lane % 16] = __float2half(acc4[2]);
  }
  if (outputRow3 < 33) {
    out[outputRow3 * 256 + blockCol * 128 + 64 + lane % 16] = __float2half(acc4[3]);
  }
  if (outputRow0 < 33) {
    out[outputRow0 * 256 + blockCol * 128 + 80 + lane % 16] = __float2half(acc5[0]);
  }
  if (outputRow1 < 33) {
    out[outputRow1 * 256 + blockCol * 128 + 80 + lane % 16] = __float2half(acc5[1]);
  }
  if (outputRow2 < 33) {
    out[outputRow2 * 256 + blockCol * 128 + 80 + lane % 16] = __float2half(acc5[2]);
  }
  if (outputRow3 < 33) {
    out[outputRow3 * 256 + blockCol * 128 + 80 + lane % 16] = __float2half(acc5[3]);
  }
  if (outputRow0 < 33) {
    out[outputRow0 * 256 + blockCol * 128 + 96 + lane % 16] = __float2half(acc6[0]);
  }
  if (outputRow1 < 33) {
    out[outputRow1 * 256 + blockCol * 128 + 96 + lane % 16] = __float2half(acc6[1]);
  }
  if (outputRow2 < 33) {
    out[outputRow2 * 256 + blockCol * 128 + 96 + lane % 16] = __float2half(acc6[2]);
  }
  if (outputRow3 < 33) {
    out[outputRow3 * 256 + blockCol * 128 + 96 + lane % 16] = __float2half(acc6[3]);
  }
  if (outputRow0 < 33) {
    out[outputRow0 * 256 + blockCol * 128 + 112 + lane % 16] = __float2half(acc7[0]);
  }
  if (outputRow1 < 33) {
    out[outputRow1 * 256 + blockCol * 128 + 112 + lane % 16] = __float2half(acc7[1]);
  }
  if (outputRow2 < 33) {
    out[outputRow2 * 256 + blockCol * 128 + 112 + lane % 16] = __float2half(acc7[2]);
  }
  if (outputRow3 < 33) {
    out[outputRow3 * 256 + blockCol * 128 + 112 + lane % 16] = __float2half(acc7[3]);
  }
}
