The unchanged `activation_kernels.cu` and `LICENSE` files are from
[vLLM](https://github.com/vllm-project/vllm) at commit
`83f5de466a889c29ac5fbfbe342d6fe4c09811e8` (Apache License 2.0).

The separate `cases/silu_and_mul/kernel.cu` is a modified, independently prepared
scalar specialization, with the changes and semantic departure recorded in
`../provenance.json`. It is not the original translation unit or the authors'
LARK registry file. The GPU comparison extracts the two helper bodies and scalar
loop from the archived public source, specializes the kernel header, removes the
unselected packed path and replaces the cache-load macro with ordinary loads.
No equivalence theorem for that source rewrite or general upstream program is
claimed; its numerical comparison is finite evidence.

The `torch_headers` directory contains eight unchanged header files from the
official PyTorch 2.11.0+cu130 installation, commit
`70d99e998b4955e0049d13a98d77ae1b14db1f45`. Their hashes are in the provenance
record. `PYTORCH_LICENSE` preserves that distribution's license notices. The
comparison instantiates the upstream helper with `torch::headeronly::Half`;
those headers supply the carrier without requiring a PyTorch runtime on the
GPU hosts.
