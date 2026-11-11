"""Freeze native fused Q/K inputs and a retained-upstream HIP comparison."""

import argparse
import hashlib
import json
from pathlib import Path
import shutil
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from lark_kernels import native_qknorm_rope as native

HERE = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def upstream_parts():
    text = (HERE / "upstream/csrc/fused_qknorm_rope_kernel.cu").read_text()
    start = text.index("namespace tensorrt_llm::common {")
    end = text.index("}  // namespace tensorrt_llm::common", start) + len("}  // namespace tensorrt_llm::common")
    common = text[start:end]
    start = text.index("template <typename scalar_t_in, typename scalar_t_cache, int head_dim,")
    body = text.index("{", start)
    depth, end = 1, body + 1
    while depth:
        depth += (text[end] == "{") - (text[end] == "}")
        end += 1
    return common, text[start:end]


def driver():
    common, kernel = upstream_parts()
    return '''#include <hip/hip_runtime.h>
#include <hip/hip_fp16.h>
#include <hip/hip_bf16.h>
#include <cmath>
#include <cstdint>
#include <type_traits>
#define USE_ROCM 1
#include "upstream/csrc/type_convert.cuh"
#define FINAL_MASK 0xffffffffffffffffULL
#define VLLM_LDG(pointer) (*(pointer))
#define fused_qknorm_rope fused_interleaved
#include "interleaved/kernel.hip"
#undef fused_qknorm_rope
#define fused_qknorm_rope fused_split
#include "split-half/kernel.hip"
#undef fused_qknorm_rope
''' + common + '\nnamespace tensorrt_llm::kernels {\n' + kernel + '''
}
using OriginalHalf = torch::headeronly::Half;
static_assert(sizeof(OriginalHalf)==2 && alignof(OriginalHalf)==2);
extern "C" int run_case(int neox,int rows,void* output,void* qkv,void* qw,void* kw,void* cache,void* upstream,void* pos) {
 if(neox) {
  hipLaunchKernelGGL(fused_split,dim3(rows*5),dim3(256),0,0,
   (__half*)output,(const __half*)qkv,(const __half*)qw,(const __half*)kw,(const __half*)cache);
 } else {
  hipLaunchKernelGGL(fused_interleaved,dim3(rows*5),dim3(256),0,0,
   (__half*)output,(const __half*)qkv,(const __half*)qw,(const __half*)kw,(const __half*)cache);
 }
 hipError_t e=hipGetLastError(); if(e!=hipSuccess)return (int)e;
 if(neox) {
  hipLaunchKernelGGL((tensorrt_llm::kernels::fusedQKNormRopeKernel<OriginalHalf,OriginalHalf,128,false>),
   dim3(rows*5),dim3(256),0,0,upstream,32,8,8,.00001f,qw,kw,cache,(const int64_t*)pos,rows,128);
 } else {
  hipLaunchKernelGGL((tensorrt_llm::kernels::fusedQKNormRopeKernel<OriginalHalf,OriginalHalf,128,true>),
   dim3(rows*5),dim3(256),0,0,upstream,32,8,8,.00001f,qw,kw,cache,(const int64_t*)pos,rows,128);
 }
 return (int)hipGetLastError();
}
extern "C" int runtime_attribute(int which) {
 hipDeviceProp_t p; if(hipGetDeviceProperties(&p,0)!=hipSuccess)return -1;
 return which==0?p.warpSize:which==1?p.maxThreadsPerBlock:-1;
}
'''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    provenance = json.loads((HERE / "provenance.json").read_text())
    for name, expected in provenance["files_sha256"].items():
        if sha(HERE / name) != expected:
            raise ValueError("Pinned source differs: " + name)
    for layout, instructions in (("interleaved", 88), ("split-half", 107)):
        case = HERE / "cases" / layout
        contract = native.parse_task((case / "task.json").read_text())
        native.check_reference((case / "reference.py").read_text(), layout)
        tr = native.translate((case / "kernel.hip").read_text(), contract)
        if len(tr.program) != instructions or tr.shared:
            raise ValueError("Native source identity differs")
        shutil.copytree(case, out / layout)
    shutil.copytree(HERE / "upstream", out / "upstream")
    shutil.copyfile(HERE / "provenance.json", out / "provenance.json")
    shutil.copyfile(HERE / "run_gpu.py", out / "run_gpu.py")
    (out / "driver.hip").write_text(driver())
    import numpy as np
    import torch
    torch_include = Path(torch.__file__).resolve().parent / "include/torch/headeronly"
    shutil.copytree(torch_include, out / "torch_headers/torch/headeronly")
    shutil.copyfile(ROOT / "reproduction/production_activation/upstream/PYTORCH_LICENSE", out / "PYTORCH_LICENSE")
    meta = {
        "schema": 1, "seed": 261102028, "numpy": np.__version__, "torch_headers_version": torch.__version__,
        "torch_headers_git_commit": torch.version.git_version, "atol": 0.002, "rtol": 0.002,
        "layouts": list(native.LAYOUTS), "cases": [],
        "upstream_retained_parts_sha256": [hashlib.sha256(p.encode()).hexdigest() for p in upstream_parts()],
        "comparison": "Selected upstream kernel and common helper namespace retained verbatim; original type_convert.cuh compiled with frozen official Torch headers. HIP includes/full mask/plain VLLM_LDG replace unrelated translation-unit context. Identity position rows compare gathered cache; V heads must stay unchanged.",
        "source_certificates": 0, "whole_kernel_execution_proved": False, "model_calls": 0,
        "original_paper_fully_reproduced": False,
    }
    names = ("qkv", "q_weight", "k_weight", "cache")
    streams = {n: (out / (n + ".bin")).open("wb") for n in names}
    try:
        for rows in (1, 3, 64, 256):
            rng = np.random.default_rng(meta["seed"] + rows)
            for trial in ("normal", "signed-zero", "structured", "cancellation", "wide", "small"):
                size = rows * 6144
                i = np.arange(size)
                if trial == "normal":
                    values = rng.normal(0, .7, size)
                elif trial == "signed-zero":
                    values = np.zeros(size, dtype="<f2")
                    values.view("<u2")[i % 2 == 1] = 0x8000
                elif trial == "structured":
                    values = ((i * 7) % 129 - 64) / 8.
                elif trial == "cancellation":
                    values = np.full(size, .75)
                elif trial == "wide":
                    values = rng.uniform(-100, 100, size)
                else:
                    values = rng.uniform(-.001, .001, size)
                qkv = np.asarray(values, dtype="<f2").reshape(rows, 48, 128)
                qkv[:, 40:, :] = ((np.arange(rows * 1024).reshape(rows, 8, 128) * 13) % 129 - 64) / 8.
                j = np.arange(128)
                qw = (((j * 7) % 65 - 32) / 16).astype("<f2")
                kw = (((j * 11) % 63 - 31) / 12).astype("<f2")
                if trial == "cancellation":
                    qw.fill(1)
                    kw.fill(1)
                cache = rng.uniform(-1, 1, (rows, 128)).astype("<f2")
                if trial == "signed-zero":
                    cache[:, :64], cache[:, 64:] = 1, 0
                elif trial == "cancellation":
                    cache.fill(.5)
                record = {"rows": rows, "trial": trial, "offset_bytes": {}, "sha256": {}}
                for name, value in zip(names, (qkv, qw, kw, cache)):
                    payload = value.tobytes()
                    record["offset_bytes"][name] = streams[name].tell()
                    streams[name].write(payload)
                    record["sha256"][name] = hashlib.sha256(payload).hexdigest()
                meta["cases"].append(record)
    finally:
        for stream in streams.values():
            stream.close()
    (out / "dataset.json").write_text(json.dumps(meta, indent=2) + "\n")
    files = {p.relative_to(out).as_posix(): sha(p) for p in sorted(out.rglob("*")) if p.is_file()}
    (out / "manifest.json").write_text(json.dumps({"schema": 1, "files": files}, indent=2) + "\n")
    print(json.dumps({"status": "native-fused-qknorm-rope-inputs-frozen", "cases": len(meta["cases"]), "files": len(files)}))


if __name__ == "__main__":
    main()
