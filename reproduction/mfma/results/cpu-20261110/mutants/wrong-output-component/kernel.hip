using H4 = _Float16 __attribute__((ext_vector_type(4)));
using F4 = float __attribute__((ext_vector_type(4)));

extern "C" __global__ void mfma_tile(const _Float16* a, const _Float16* b, const float* c, float* out) {
  int lane = threadIdx.x;
  H4 left = {a[(lane % 16) * 16 + (lane / 16) * 4 + 0], a[(lane % 16) * 16 + (lane / 16) * 4 + 1], a[(lane % 16) * 16 + (lane / 16) * 4 + 2], a[(lane % 16) * 16 + (lane / 16) * 4 + 3]};
  H4 right = {b[((lane / 16) * 4 + 0) * 16 + (lane % 16)], b[((lane / 16) * 4 + 1) * 16 + (lane % 16)], b[((lane / 16) * 4 + 2) * 16 + (lane % 16)], b[((lane / 16) * 4 + 3) * 16 + (lane % 16)]};
  F4 acc = {c[((lane / 16) * 4 + 0) * 16 + (lane % 16)], c[((lane / 16) * 4 + 1) * 16 + (lane % 16)], c[((lane / 16) * 4 + 2) * 16 + (lane % 16)], c[((lane / 16) * 4 + 3) * 16 + (lane % 16)]};
  acc = __builtin_amdgcn_mfma_f32_16x16x16f16(left, right, acc, 0, 0, 0);
  out[((lane / 16) * 4 + 0) * 16 + (lane % 16)] = acc[1];
  out[((lane / 16) * 4 + 1) * 16 + (lane % 16)] = acc[1];
  out[((lane / 16) * 4 + 2) * 16 + (lane % 16)] = acc[2];
  out[((lane / 16) * 4 + 3) * 16 + (lane % 16)] = acc[3];
}
