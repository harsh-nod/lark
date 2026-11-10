# MI350X collective-layout conformance

Run date: 2026-11-09. **Independent finite hardware experiment, zero model calls.**
[Method and boundaries](README.md), [archived evidence](results/).

| Host | Device | Shuffle bit-copy comparisons | MFMA output comparisons | Mismatches | Inputs / allocation guards |
| --- | --- | ---: | ---: | ---: | --- |
| mi350 | AMD Instinct MI350X | 133,632 | 16,850,944 | 0 | unchanged |
| mi350-2 | AMD Instinct MI350X | 133,632 | 16,850,944 | 0 | unchanged |

Each host passed **16,984,576 bit-identical output comparisons**. Actual output
payloads, compiler assembly, compile/run logs and every input/reference byte are
archived and SHA-256-bound; `summarize.py` audits these bindings. Both native
compilers emitted `v_mfma_f32_16x16x16...` in the saved device assembly.

- **Shuffles:** 1,044 full-partition configurations, two complete wave64s per
  configuration. Index/up/down/xor, every supported power-of-two width 1..64,
  all in-partition source selectors/xor masks, and all up/down offsets through
  the width. uint32 and float32 bit-copy overloads use seeded 32-bit payloads.
  Out-of-partition up/down reads check the documented self-return behavior;
  undefined index selectors are not issued.
- **One native MFMA shape:** FP16-input, FP32-accumulator 16x16x16, one full
  wave64, default modifiers. All **65,536 input basis pairs** cover every pair
  of A/B element positions, including matching and nonmatching reduction
  coordinates. Another **256 accumulator basis** cases and **32 exact random
  tiles** check accumulator preservation and arithmetic. The random integers
  and binary fractions are exactly representable throughout these tiny products.
- All source/config/input bytes stayed unchanged, and all seven device
  allocations retained 128-byte prefix/suffix guards.

This records finite conformance and lane/fragment layouts for these AMD forms.
It is **not** a proof of all IEEE operands, all modifiers, other MFMA shapes,
divergent/partial masks, barriers, NVIDIA/PTX collectives or the paper's complete
per-language instruction table. The existing Lean source reader still refuses
these operations. No whole-kernel certificate or race-freedom proof is inferred
from these measurements. Hardware/compiler correspondence remains trusted.
