"""Freeze native FlashInfer RMSNorm inputs and an upstream-body HIP comparison.

The selected upstream CUDA template body is retained verbatim; its shuffle,
rsqrt and vector helpers are explicitly replaced for the HIP comparison.
"""

import argparse
import hashlib
import json
from pathlib import Path
import shutil
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from lark_kernels import native_flashinfer_rmsnorm as native

HERE = Path(__file__).resolve().parent


def sha(path):
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for data in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(data)
    return h.hexdigest()


def upstream_body():
    text = (HERE / "upstream/flashinfer-norm.cuh").read_text()
    start = text.index("template <uint32_t VEC_SIZE, typename T>\n__global__ void RMSNormKernel")
    begin = text.index("{", start)
    depth, end = 1, begin + 1
    while depth:
        depth += (text[end] == "{") - (text[end] == "}")
        end += 1
    return text[start:end]


def driver():
    prefix = """#include <hip/hip_runtime.h>
#include <hip/hip_fp16.h>
#include <cstdint>
#include <cmath>
#include "kernel.hip"
// HIP comparison helpers; these are not the original CUDA helper definitions.
namespace comparison {
__host__ __device__ inline uint32_t ceil_div(uint32_t n,uint32_t d) {return (n+d-1)/d;}
namespace math {
__device__ inline float shfl_xor_sync(float x,uint32_t d) {return __shfl_xor(x,d,32);}
__device__ inline float rsqrt(float x) {return rsqrtf(x);}
}
template<typename T,uint32_t N> struct vec_t {
 T value[N];
 __device__ void fill(float v) {for(uint32_t j=0;j<N;j++) value[j]=(T)v;}
 __device__ void load(const T* p) {for(uint32_t j=0;j<N;j++) value[j]=p[j];}
 __device__ void store(T* p) const {for(uint32_t j=0;j<N;j++) p[j]=value[j];}
 __device__ T& operator[](uint32_t j) {return value[j];}
 __device__ const T& operator[](uint32_t j) const {return value[j];}
};
"""
    suffix = """
}
extern "C" int run_case(int rows,void* output,void* input,void* weight,void* upstream_output) {
 hipLaunchKernelGGL(flashinfer_rmsnorm,dim3(rows),dim3(1024),0,0,
   (__half*)output,(const __half*)input,(const __half*)weight);
 hipError_t e=hipGetLastError(); if(e!=hipSuccess)return (int)e;
 hipLaunchKernelGGL((comparison::RMSNormKernel<8,__half>),dim3(rows),dim3(32,32),32*sizeof(float),0,
   (__half*)input,(__half*)weight,(__half*)upstream_output,16384u,16384u,16384u,0.f,0.00001f);
 return (int)hipGetLastError();
}
extern "C" int runtime_attribute(int which) {
 hipDeviceProp_t p; if(hipGetDeviceProperties(&p,0)!=hipSuccess)return -1;
 return which==0?p.warpSize:which==1?p.maxThreadsPerBlock:which==2?p.sharedMemPerBlock:-1;
}
extern "C" const char* runtime_architecture() {
 static hipDeviceProp_t p; if(hipGetDeviceProperties(&p,0)!=hipSuccess)return "unknown";
 return p.gcnArchName;
}
"""
    return prefix + upstream_body() + suffix


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    case = HERE / "cases/native_16384"
    task = native.parse_task((case / "task.json").read_text())
    native.check_reference((case / "reference.py").read_text())
    tr = native.translate((case / "kernel.hip").read_text(), task)
    if len(tr.program) != 68 or tr.shared != [("partial", 32)]:
        raise ValueError("Native source identity differs")
    provenance = json.loads((HERE / "provenance.json").read_text())
    for name, digest in provenance["files_sha256"].items():
        if sha(HERE / "upstream" / name) != digest:
            raise ValueError("Pinned upstream source differs: " + name)
    for name in ("kernel.hip", "reference.py", "task.json"):
        shutil.copyfile(case / name, out / name)
    shutil.copytree(HERE / "upstream", out / "upstream")
    shutil.copyfile(HERE / "run_gpu.py", out / "run_gpu.py")
    shutil.copyfile(HERE / "audit_gpu.py", out / "audit_gpu.py")
    (out / "driver.hip").write_text(driver())
    if (out / "driver.hip").read_text().count(upstream_body()) != 1:
        raise ValueError("Upstream template body was not retained exactly once")

    import numpy as np
    import torch
    torch.set_num_threads(1)
    metadata = {
        "schema": 1, "seed": 261102028, "torch": torch.__version__, "numpy": np.__version__,
        "atol": .002, "rtol": .002, "cases": [],
        "upstream_template_body_sha256": hashlib.sha256(upstream_body().encode()).hexdigest(),
        "comparison_helpers": "Explicit HIP logical32 shuffle, rsqrtf and scalar vec_t; selected template body retained verbatim; no CUDA helper/compiler-equivalence proof",
        "reference": "Fresh CPU float64 dense RMSNorm and separate CPU Torch FP32 from exactly promoted frozen FP16 input/weight; no stored reference output is trusted",
        "source_certificates": 0, "whole_kernel_execution_proved": False,
        "actual_trace_classification_proved": False, "source_reference_equality_proved": False,
        "model_calls": 0, "original_paper_fully_reproduced": False,
    }
    offset = 0
    streams = {name: (out / (name + ".bin")).open("wb") for name in ("input", "weight")}
    try:
        for rows in (1, 3, 64, 255):
            count = rows * native.WIDTH
            index = np.arange(count, dtype=np.int64)
            rng = np.random.default_rng(metadata["seed"] + rows)
            weight = (((np.arange(native.WIDTH) * 7) % 65 - 32) / 16).astype("<f2")
            entry = {"rows": rows, "elements": count, "trials": []}
            for trial in range(6):
                if trial == 0:
                    x = rng.normal(0, .25, count).astype("<f2")
                    label = "seeded-normal"
                elif trial == 1:
                    x = np.where(index % 2, -0., 0.).astype("<f2")
                    label = "signed-zero"
                elif trial == 2:
                    x = np.full(count, .125, dtype="<f2")
                    label = "constant"
                elif trial == 3:
                    x = (((index * 17) % 67 - 33) / 16).astype("<f2")
                    label = "structured-dyadic"
                elif trial == 4:
                    x = np.array([1, 1.5, -1, -1.5, 2048, -2048, 2**-24, 0], dtype="<f2")[(index + index // 71) % 8]
                    label = "half-rounding-and-subnormals"
                else:
                    x = np.array([-8192, 8192, 2**-24, -(2**-24), 1, -1, 0, .001], dtype="<f2")[(index * 7 + index // 13) % 8]
                    label = "mixed-magnitudes"
                promoted = x.astype(np.float64).reshape(rows, native.WIDTH)
                reference = (promoted / np.sqrt((promoted * promoted).mean(axis=1, keepdims=True) + 1e-5)
                             * weight.astype(np.float64)).reshape(-1)
                tx, tw = torch.from_numpy(x.copy()).float().reshape(rows, native.WIDTH), torch.from_numpy(weight.copy()).float()
                torch_reference = (tx * torch.rsqrt((tx * tx).mean(dim=1, keepdim=True) + 1e-5)
                                   * (0.0 + tw)).half().numpy().astype("<f2", copy=False).reshape(-1)
                if not np.isfinite(reference).all() or not np.isfinite(torch_reference).all():
                    raise ValueError("Nonfinite prepared reference")
                woff = streams["weight"].tell()
                streams["input"].write(x.tobytes())
                streams["weight"].write(weight.tobytes())
                entry["trials"].append({
                    "trial": trial, "label": label, "offset_elements": offset,
                    "weight_offset_bytes": woff,
                    "cpu_float64_reference_sha256": hashlib.sha256(reference.astype("<f8").tobytes()).hexdigest(),
                    "torch_fp32_rounded_reference_sha256": hashlib.sha256(torch_reference.tobytes()).hexdigest(),
                })
                offset += count
            metadata["cases"].append(entry)
            print(json.dumps({"prepared_rows": rows, "trials": 6}), flush=True)
    finally:
        for stream in streams.values():
            stream.close()
    metadata["outputs_per_method"] = offset
    (out / "dataset.json").write_text(json.dumps(metadata, indent=2) + "\n")
    manifest = {"files": {p.relative_to(out).as_posix(): sha(p) for p in sorted(out.rglob("*")) if p.is_file()},
                "generator_sha256": sha(Path(__file__))}
    (out / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(json.dumps({"status": "prepared", "trials": 24, "outputs_per_method": offset}), flush=True)


if __name__ == "__main__":
    main()
