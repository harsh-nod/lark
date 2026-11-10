# Small upstream-derived SiLU-and-mul study

This is an independent adaptation of vLLM's scalar FP16 SiLU-and-mul path at
**two tokens and hidden width five**, with grid two and block five. It concerns
the public upstream revision in [provenance.json](provenance.json), downloaded
on November 10, 2026, rather than the unavailable LARK paper registry revision.
It does not reproduce the paper's production pass rates or original shapes.

The kernel keeps the packed input layout `[tokens, 2 * hidden]`, writes a
separate `[tokens, hidden]` output, and retains the intermediate half rounding
inside the upstream SiLU helper. Rounding only after the gating multiply is a
different function. The independent PyTorch reference explicitly rounds at both
boundaries. The recorded index-width departure reads the small token and loop
indices as int32; the host launch matches the selected small scalar fallback.

[Results](RESULTS.md) keep the abstract-operation proof, finite hardware checks
and upstream-source correspondence separate. The upstream rewrite itself has no
source-to-source equivalence theorem. The original complete templated translation
unit is not certified. The archived source and license are in [upstream/](upstream/).

To run the CPU certificates and direct Lean controls:

```bash
python3 reproduction/production_activation/run_cpu.py \
  --output /tmp/lark-production-activation-cpu --lean /path/to/lean
```

The controller freezes the implementation, Lean libraries, fixtures and study
scripts into a source archive and executes the CPU study from that copy. Each
HIP/CUDA certificate is freshly checked. Negative controls bypass Python's
numerical preflight and submit the changed program directly to Lean. An
unproved attempt is recorded as rejection of that supplied proof, not a proof
that no proof can exist. Timeouts and unexpected acceptance fail the study.

Prepare numerical evidence using an existing CPU PyTorch installation:

```bash
python3 reproduction/production_activation/prepare_gpu.py \
  --cpu /tmp/lark-production-activation-cpu/cpu \
  --output /tmp/lark-production-activation-input
```

Copy the input directory and GPU runner to an idle MI350X. No model, PyTorch,
Docker or NVIDIA runtime is needed on that host:

```bash
ROCR_VISIBLE_DEVICES=0 python3 reproduction/production_activation/run_gpu.py \
  --input /tmp/lark-production-activation-input \
  --output /tmp/lark-production-activation-gpu
```

The runner checks all input hashes, compiles for gfx950 and requires at least
98% free GPU memory immediately before execution. Each trial runs the exact
certified HIP source and a scalar specialization extracted from the pinned
upstream helpers/loop. Their outputs must match bit for bit, and each is checked
against CPU PyTorch at the declared tolerance. Inputs and 128-byte guards on
both sides of every allocation must remain unchanged. These finite comparisons
are evidence about the adaptation, not a universal upstream or IEEE theorem.

All model calls are zero. CUDA has CPU Lean evidence only; device validation is
HIP on the two AMD hosts. The existing seventeen-family full-shape ledger is a
separate study and does not include this small production-derived fixture.
