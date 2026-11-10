# Full-wave reduction with an exact-real reference

This independent HIP fixture adds a source-bound proof of a six-stage XOR
butterfly reduction. One native wave64 block loads 64 float32 inputs, combines
partners at masks 32, 16, 8, 4, 2 and 1, and writes all 64 outputs. The separate
PyTorch reference sums the input and repeats that result 64 times.

Lean proves actual completion of the full sixteen-instruction launch, race
freedom and equality of every output to the canonical sum, for every **real**
input and initial outside-memory state. The core proof preserves the source
expression tree for arbitrary `Ops`; the optional pinned Mathlib interpretation
then justifies reassociation and permutation. The nonlinear and collective
machines are unchanged. No arithmetic axiom, inserted memory barrier or
kernel-specific assumption is added.

The proof follows the initial load fold, five shuffle/add phases and the final
shuffle/add/store phase. A generic snapshot-gather lemma connects each shuffle
to the actual register state. Induction and the unique-writer trace invariant
establish the phase, launch and footprint properties. The real bridge proves
that each lane's addition tree contains a permutation of all 64 input indices.

This is one independent primitive. It does not recover an original production
reduction, weighted normalization, packed vector kernel, multiwave reduction,
partial subgroup, online attention algorithm or NVIDIA/PTX implementation.
The [recorded results](RESULTS.md) include both successful ordinary numerical
checks and cancellation disagreements on the two AMD hosts. Exact-real equality
does not establish IEEE equality or a numerical-error bound.

## Check a certificate

Initialize the [optional pinned dependencies](../../lean-real/README.md), then:

```bash
python3 -m lark_kernels verify-wave-sum \
  reproduction/wave_reduction/cases/sum64/kernel.hip \
  --reference reproduction/wave_reduction/cases/sum64/reference.py \
  --task reproduction/wave_reduction/cases/sum64/task.json \
  --output /tmp/lark-wave-certificate
python3 -m lark_kernels check /tmp/lark-wave-certificate
```

`LARK_REAL_PROJECT` may select another initialized `lean-real` checkout. The
checker validates the nine locked dependency source revisions, compiles its
pinned proof sources into a managed content-addressed cache, validates the
cached own-library hashes, and checks a newly generated `Main.lean` in a fresh
directory. It regenerates the translation and all 64 reference cells from the
recorded sources. Only the standard printed axioms are accepted. Certificate
build files and certificate-supplied compiled imports are never executed or
loaded by `lark check`. The pinned Mathlib/dependency compiled import cache
remains trusted. A standalone source export also includes a pinned Lake project
for conventional rebuilding in a trusted environment.

The closed profile requires separate contiguous float32[64] input and output
buffers and grid 1, block 64, warp 64. It refuses other source programs,
reference ASTs, precisions and geometries. Proof-provider/model arguments are
not used. Formatting and comments may vary while the lossless source lowering
and closed reference AST remain the same.

## Repeat the study

```bash
LARK_TEST_REAL=1 python3 -m unittest discover -s tests -p test_wave_sum.py -v
python3 reproduction/wave_reduction/run_cpu.py --output /tmp/lark-wave-study
```

The CPU runner freezes source bytes before running its worker. Use that frozen
archive's `prepare_gpu.py` with `--cpu /tmp/lark-wave-study/cpu` and a fresh
`--output` to generate the numerical packet. It requires the recorded CPU
PyTorch/NumPy versions. Package the `input` directory and the same frozen
`run_gpu.py` as `runner.py` in a regular-file tar archive. `run_host.py` transports
that packet to an explicitly selected idle GPU on `mi350` or `mi350-2`. It refuses
an existing remote run directory, checks immediate GPU activity and uses the
runner's 98% free-memory guard. The runner compiles the exact certified source
with `-ffp-contract=off` and checks input preservation and allocation guards.

The published evidence can be audited without a GPU or new Lean/model calls:

```bash
python3 reproduction/wave_reduction/summarize.py
```

The audit regenerates the positive and four negative statements using the
frozen frontend, regenerates every numerical input/reference/driver file, and
independently compares the archived raw output streams with both the source
expression tree and CPU Torch. It reports cancellation probes separately.
`checkpoint/` retains an earlier proved-library checkpoint; the source-bound
certificate and two-host study in `results/` supersede its pending-work status.
