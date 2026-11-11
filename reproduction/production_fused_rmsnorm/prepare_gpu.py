"""Freeze independent FP16 in-place fused RMSNorm numerical comparisons.

The comparison kernel retains the selected upstream template body verbatim,
with explicitly replaced HIP shuffle/rsqrt and scalar-vector helper definitions.
This is a HIP comparison adaptation, not execution of NVIDIA source unchanged.
"""

import argparse
import hashlib
import json
from pathlib import Path
import shutil
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from lark_kernels import native_fused_rmsnorm as native

HERE = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def upstream_body():
    text = (HERE / "upstream/flashinfer-norm.cuh").read_text()
    start = text.index("template <uint32_t VEC_SIZE, typename T>\n__global__ void FusedAddRMSNormKernel")
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
// Explicit HIP comparison helpers, not FlashInfer's original CUDA helper text.
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
extern "C" int run_case(int rows,void* input,void* residual,void* weight,void* upstream_input,void* upstream_residual) {
 hipLaunchKernelGGL(fused_add_rmsnorm,dim3(rows),dim3(1024),0,0,
   (__half*)input,(__half*)residual,(const __half*)weight);
 hipError_t e=hipGetLastError(); if(e!=hipSuccess)return (int)e;
 hipLaunchKernelGGL((comparison::FusedAddRMSNormKernel<8,__half>),dim3(rows),dim3(32,32),(32+16384)*sizeof(float),0,
   (__half*)upstream_input,(__half*)upstream_residual,(__half*)weight,16384u,16384u,16384u,0.f,0.00001f);
 return (int)hipGetLastError();
}
extern "C" int runtime_attribute(int which) {
 hipDeviceProp_t p; if(hipGetDeviceProperties(&p,0)!=hipSuccess)return -1;
 return which==0?p.warpSize:which==1?p.maxThreadsPerBlock:which==2?p.sharedMemPerBlock:-1;
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
    contract = native.parse_task((case / "task.json").read_text())
    native.check_reference((case / "reference.py").read_text())
    tr = native.translate((case / "kernel.hip").read_text(), contract)
    if len(tr.program) != 72 or tr.shared != [("partial", 32), ("unrounded", 16384)]:
        raise ValueError("Development source identity differs")
    provenance = json.loads((HERE / "provenance.json").read_text())
    for name, digest in provenance["files_sha256"].items():
        if sha(HERE / "upstream" / name) != digest:
            raise ValueError("Pinned upstream file differs: " + name)
    for name in ("kernel.hip", "reference.py", "task.json"):
        shutil.copyfile(case / name, out / name)
    shutil.copytree(HERE / "upstream", out / "upstream")
    shutil.copyfile(HERE / "run_gpu.py", out / "run_gpu.py")
    (out / "driver.hip").write_text(driver())

    import numpy as np
    import torch
    torch.set_num_threads(1)
    meta = {
        "schema": 1, "seed": 261102028, "torch": torch.__version__, "numpy": np.__version__,
        "atol": 0.002, "rtol": 0.002, "cases": [],
        "upstream_template_body_sha256": hashlib.sha256(upstream_body().encode()).hexdigest(),
        "comparison_helpers": "Explicit HIP width32 shuffle, rsqrtf and scalar vec_t helpers; selected upstream body retained verbatim, original helper/compiler equivalence is not proved",
        "reference": "CPU float64 RMSNorm using exactly promoted FP16 input/residual/weight; residual requires exact FP32-add then FP16-store bits",
        "source_certificates": 0, "whole_kernel_execution_proved": False,
        "actual_trace_classification_proved": False, "model_calls": 0,
        "original_paper_fully_reproduced": False,
    }
    offset = 0
    streams = {name: (out / (name + ".bin")).open("wb") for name in
               ("input", "residual", "weight", "expected-input", "expected-residual")}
    try:
        for rows in (1, 3, 64, 255):
            count = rows * 16384
            index = np.arange(count, dtype=np.int64)
            rng = np.random.default_rng(meta["seed"] + rows)
            weight = (((np.arange(16384) * 7) % 65 - 32) / 16).astype("<f2")
            entry = {"rows": rows, "elements": count, "trials": []}
            for trial in range(6):
                if trial == 0:
                    a = rng.normal(0, .25, count).astype("<f2")
                    r = rng.normal(0, .25, count).astype("<f2")
                    label = "seeded-normal"
                elif trial == 1:
                    a = np.where(index % 2, -0., 0.).astype("<f2")
                    r = np.where(index % 3, -0., 0.).astype("<f2")
                    label = "signed-zero"
                elif trial == 2:
                    a = np.full(count, .125, dtype="<f2")
                    r = np.full(count, .25, dtype="<f2")
                    label = "constant"
                elif trial == 3:
                    a = (((index * 17) % 67 - 33) / 16).astype("<f2")
                    r = (((index * 19) % 71 - 35) / 32).astype("<f2")
                    label = "structured-dyadic"
                elif trial == 4:
                    a = np.array([1, 1.5, -1, -1.5, 2048, -2048, 2**-24, 0], dtype="<f2")[index % 8]
                    r = np.array([2**-11, 2**-10, -(2**-11), 2**-10, -2047, 2047, 2**-24, -0.0], dtype="<f2")[(index + index // 71) % 8]
                    label = "half-rounding-and-cancellation"
                else:
                    a = np.array([-8192, 8192, 2**-24, -(2**-24), 1, -1, 0, .001], dtype="<f2")[(index * 7 + index // 13) % 8]
                    r = np.array([4096, -4096, 1, -1, -8192, 8192, -(2**-24), 2**-24], dtype="<f2")[(index * 3 + index // 17) % 8]
                    label = "mixed-magnitudes"
                x32 = a.astype(np.float32) + r.astype(np.float32)
                x64 = (a.astype(np.float64) + r.astype(np.float64)).reshape(rows, 16384)
                ref64 = x64 / np.sqrt((x64 * x64).mean(axis=1, keepdims=True) + 1e-5) * weight.astype(np.float64)
                expected_residual = x32.astype("<f2")
                if not np.isfinite(ref64).all() or not np.isfinite(expected_residual).all():
                    raise ValueError("Nonfinite prepared numerical reference")
                woff = streams["weight"].tell()
                for name, value in [("input", a), ("residual", r), ("weight", weight),
                                    ("expected-input", ref64.astype("<f4")),
                                    ("expected-residual", expected_residual)]:
                    streams[name].write(value.tobytes())
                entry["trials"].append({"trial": trial, "label": label, "offset_elements": offset,
                                         "weight_offset_bytes": woff})
                offset += count
            meta["cases"].append(entry)
            print(json.dumps({"prepared_rows": rows, "trials": 6}), flush=True)
    finally:
        for stream in streams.values():
            stream.close()
    meta["outputs_per_method_per_buffer"] = offset
    (out / "dataset.json").write_text(json.dumps(meta, indent=2) + "\n")
    manifest = {"files": {p.relative_to(out).as_posix(): sha(p) for p in sorted(out.rglob("*")) if p.is_file()},
                "generator_sha256": sha(Path(__file__))}
    (out / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(json.dumps({"status": "prepared", "trials": 24, "outputs_per_method_per_buffer": offset}), flush=True)


if __name__ == "__main__":
    main()
