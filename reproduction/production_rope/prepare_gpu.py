"""Freeze native Q/K RoPE inputs and a retained-upstream HIP comparison."""

import argparse
import hashlib
import json
from pathlib import Path
import shutil
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from lark_kernels import native_rope as native

HERE = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def upstream_body():
    text = (HERE / "upstream/pos_encoding_kernels.cu").read_text()
    start = text.index("namespace vllm {")
    end = text.index("}  // namespace vllm", start) + len("}  // namespace vllm")
    return text[start:end]


def driver():
    return '''#include <hip/hip_runtime.h>
#include <hip/hip_fp16.h>
#include <cstdint>
#define rotary_embedding rotary_interleaved
#include "interleaved/kernel.hip"
#undef rotary_embedding
#define rotary_embedding rotary_split
#include "split-half/kernel.hip"
#undef rotary_embedding
// The upstream hint is replaced by a plain HIP load; helper bodies are retained.
#define VLLM_LDG(pointer) (*(pointer))
''' + upstream_body() + '''
extern "C" int run_case(int neox,int rows,void* q,void* k,void* cache,void* uq,void* uk,void* pos) {
 if(neox) {
  hipLaunchKernelGGL(rotary_split,dim3(rows),dim3(512),0,0,(__half*)q,(__half*)k,(const __half*)cache);
 } else {
  hipLaunchKernelGGL(rotary_interleaved,dim3(rows),dim3(512),0,0,(__half*)q,(__half*)k,(const __half*)cache);
 }
 hipError_t e=hipGetLastError(); if(e!=hipSuccess)return (int)e;
 if(neox) {
  hipLaunchKernelGGL((vllm::rotary_embedding_kernel<__half,__half,true>),dim3(rows),dim3(512),0,0,
   (const int64_t*)pos,(__half*)uq,(__half*)uk,(const __half*)cache,128,4096,1024,128,32,8,128,0,false);
 } else {
  hipLaunchKernelGGL((vllm::rotary_embedding_kernel<__half,__half,false>),dim3(rows),dim3(512),0,0,
   (const int64_t*)pos,(__half*)uq,(__half*)uk,(const __half*)cache,128,4096,1024,128,32,8,128,0,false);
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
    for layout in native.LAYOUTS:
        case = HERE / "cases" / layout
        contract = native.parse_task((case / "task.json").read_text())
        native.check_reference((case / "reference.py").read_text(), layout)
        tr = native.translate((case / "kernel.hip").read_text(), contract)
        if len(tr.program) != 50 or tr.shared:
            raise ValueError("Native source identity differs")
        shutil.copytree(case, out / layout)
    shutil.copytree(HERE / "upstream", out / "upstream")
    shutil.copyfile(HERE / "provenance.json", out / "provenance.json")
    shutil.copyfile(HERE / "run_gpu.py", out / "run_gpu.py")
    (out / "driver.hip").write_text(driver())
    import numpy as np
    meta = {
        "schema": 1, "seed": 261102028, "numpy": np.__version__,
        "atol": 0.002, "rtol": 0.002, "layouts": list(native.LAYOUTS), "cases": [],
        "upstream_device_body_sha256": hashlib.sha256(upstream_body().encode()).hexdigest(),
        "comparison": "Three upstream device/helper bodies retained verbatim; CUDA includes replaced by HIP, VLLM_LDG becomes plain load. Positions are identity rows, compared with pregathered adaptation.",
        "reference": "Fresh CPU Torch FP32 at explicit cast/product/add/sub sites and independent float64 formula, both starting from exact input FP16 bytes.",
        "whole_kernel_execution_proved": False, "source_certificates": 0,
        "model_calls": 0, "original_paper_fully_reproduced": False,
    }
    streams = {name: (out / (name + ".bin")).open("wb") for name in ("query", "key", "cache")}
    offsets = dict.fromkeys(streams, 0)
    try:
        for rows in (1, 3, 64, 256):
            rng = np.random.default_rng(meta["seed"] + rows)
            for trial in ("normal", "signed-zero", "structured", "cancellation", "wide", "small"):
                record = {"rows": rows, "trial": trial, "offset_bytes": dict(offsets), "sha256": {}}
                for name, heads in (("query", 32), ("key", 8), ("cache", 1)):
                    size = rows * heads * 128
                    i = np.arange(size)
                    if name == "cache":
                        values = (rng.uniform(-1, 1, size) if trial not in ("cancellation", "signed-zero")
                                  else np.full(size, .5 if trial == "cancellation" else 1.))
                    elif trial == "normal":
                        values = rng.normal(0, .7, size)
                    elif trial == "signed-zero":
                        values = np.zeros(size, dtype="<f2")
                        values.view("<u2")[i % 2 == 1] = 0x8000
                    elif trial == "structured":
                        values = ((i * 7) % 129 - 64) / 8.
                    elif trial == "cancellation":
                        # Both layouts have equal paired values, exercising exact cancellation.
                        values = np.full(size, .75)
                    elif trial == "wide":
                        values = rng.uniform(-100, 100, size)
                    else:
                        values = rng.uniform(-.001, .001, size)
                    payload = np.asarray(values, dtype="<f2").tobytes()
                    streams[name].write(payload)
                    record["sha256"][name] = hashlib.sha256(payload).hexdigest()
                    offsets[name] += len(payload)
                meta["cases"].append(record)
    finally:
        for stream in streams.values():
            stream.close()
    (out / "dataset.json").write_text(json.dumps(meta, indent=2) + "\n")
    files = {p.relative_to(out).as_posix(): sha(p) for p in sorted(out.rglob("*")) if p.is_file()}
    (out / "manifest.json").write_text(json.dumps({"schema": 1, "files": files}, indent=2) + "\n")
    print(json.dumps({"status": "native-rope-inputs-frozen", "cases": len(meta["cases"]),
                      "layouts": 2, "input_bytes": offsets, "files": len(files)}))


if __name__ == "__main__":
    main()
