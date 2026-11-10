# Full-size attention contracts

This independent adaptation proves three connected scalar launches for noncausal
dense scaled-dot-product attention and grouped-query attention. It does not
implement FlashAttention's online softmax algorithm or the authors' optimized
PTX kernels. [Measured results](RESULTS.md), [paper coverage](../COVERAGE.md).

The separate [online-attention study](../online_attention/README.md) proves the
tiled value recurrence and numerically checks an unchanged upstream FP32 kernel
on both MI350X hosts. Its actual launch and race-freedom proofs remain open;
it adds no certificate to this dense three-launch family.

Scores are FP32 dot products of promoted FP16 Q/K, divided by the exact integer
square root of the head dimension. Row softmax stays FP32; the last product with
FP16 V rounds only the final output to FP16. Query head `h` reads KV head
`h / groups`. Six named allocations and three ordered launches are required.

`RowPhase.lean` checks each five-instruction FP32 reduction cycle and its loop.
`RowSoftmax.lean` checks the complete 22-instruction softmax lane and grid.
`AttentionAddress.lean` proves primitive bounded grouped indices.
`AttentionPipeline.lean` connects actual final memories and proves all valid
intermediate reads, all launch completions, race freedom and final outputs.
Theorems quantify over arbitrary scalar operations, inputs and outside memories.

```bash
python3 -m lark_kernels verify-attention reproduction/attention/cases/gqa/hip \
  --output /tmp/gqa-certificate --lean /path/to/lean-4.19.0/bin/lean
python3 -m lark_kernels check /tmp/gqa-certificate --lean /path/to/lean
python3 reproduction/attention/run_cpu.py --output /tmp/attention-cpu --lean /path/to/lean
python3 reproduction/attention/prepare_gpu.py --cpu /tmp/attention-cpu \
  --output /tmp/attention-input --lean /path/to/lean
```

Copy the prepared files and `reproduction/attention/{run_gpu,bundle}.py` to a
ROCm host, preserving that relative layout, then run:

```bash
HIP_VISIBLE_DEVICES=0 python3 reproduction/attention/run_gpu.py \
  --input /tmp/attention-input --output /tmp/attention-device
```

The device runner needs only standard-library Python and `hipcc`, not PyTorch.
It validates every intermediate/final cell, input bytes and 128-byte allocation
guards. `-ffp-contract=off` prevents accidental contraction of the scalar source.
The CPU preparation requires PyTorch. Scaling and fixed-program mutation checks
are proof experiments rather than device benchmarks or semantic mutant diagnoses.

The profile currently accepts positive rank-three layouts with each footprint
below 2^31, KV heads dividing query heads and a perfect-square head dimension.
The reference return AST is closed and checked before a minimal module safety
check; exports regenerate all three programs, shapes and proof-library hashes
on independent recheck. This is a conservative supported subset.
