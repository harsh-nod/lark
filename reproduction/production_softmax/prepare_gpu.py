"""Freeze native softmax sources and independent CPU-float64 numerical inputs."""

import argparse
import hashlib
import json
from pathlib import Path
import shutil

HERE = Path(__file__).resolve().parent


DRIVER = """#include <hip/hip_runtime.h>
#include <hip/hip_fp16.h>
#include <cmath>
// Rename entry symbols only; each frozen source is otherwise included verbatim.
#define softmax_forward_kernel7 softmax_original
#include "native_race/kernel.hip"
#undef softmax_forward_kernel7
#define softmax_forward_kernel7 softmax_repaired
#include "native_fixed/kernel.hip"
#undef softmax_forward_kernel7
extern "C" int run_case(int rows,void* input,void* original,void* repaired) {
  hipLaunchKernelGGL(softmax_original,dim3(rows),dim3(1024),0,0,(__half*)original,(const __half*)input);
  hipError_t e=hipGetLastError(); if(e!=hipSuccess)return (int)e;
  hipLaunchKernelGGL(softmax_repaired,dim3(rows),dim3(1024),0,0,(__half*)repaired,(const __half*)input);
  return (int)hipGetLastError();
}
extern "C" int runtime_attribute(int which) {
  hipDeviceProp_t p; if(hipGetDeviceProperties(&p,0)!=hipSuccess)return -1;
  return which==0?p.warpSize:which==1?p.maxThreadsPerBlock:which==2?p.sharedMemPerBlock:-1;
}
"""


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    for name in ("native_race", "native_fixed"):
        shutil.copytree(HERE / "cases" / name, out / name)
    shutil.copytree(HERE / "upstream", out / "upstream")
    for name in ("provenance.json", "rewrites.json", "run_gpu.py"):
        shutil.copyfile(HERE / name, out / name)
    (out / "driver.hip").write_text(DRIVER)
    import numpy as np

    width, seed, offset = 50257, 261102028, 0
    metadata = {
        "schema": 1, "seed": seed, "numpy": np.__version__, "width": width,
        "atol": 2 ** -24, "rtol": 0.002, "cases": [],
        "reference": "CPU float64 stable softmax of exactly promoted FP16 inputs, rounded to FP16 once at the end",
        "source_intermediate_storage": "FP16 exponentials in out, FP32 unrounded sum accumulation, FP16 final output",
        "original_paper_fully_reproduced": False, "source_certificates": 0, "model_calls": 0,
    }
    with (out / "input.bin").open("wb") as inputs, (out / "expected.bin").open("wb") as expected:
        for rows in (1, 3, 64, 255):
            n = rows * width
            index = np.arange(n, dtype=np.int64)
            entry = {"rows": rows, "elements": n, "trials": []}
            for trial in range(6):
                if trial == 0:
                    rng = np.random.default_rng(seed + rows)
                    a = rng.normal(0, 2, n).astype("<f2")
                    label = "seeded-normal"
                elif trial == 1:
                    a = np.where(index % 2, -0., 0.).astype("<f2")
                    label = "signed-zero-uniform"
                elif trial == 2:
                    a = np.full(n, -8, dtype="<f2")
                    label = "all-negative-constant"
                elif trial == 3:
                    a = (((index * 17) % 257 - 128) / 8).astype("<f2")
                    label = "structured-dyadic"
                elif trial == 4:
                    a = np.full(n, -8, dtype="<f2").reshape(rows, width)
                    a[:, -1] = 8
                    a = a.reshape(-1)
                    label = "last-cell-maximum"
                else:
                    a = np.where(index % 2, -20, 20).astype("<f2")
                    label = "wide-alternating"
                x = a.astype(np.float64).reshape(rows, width)
                values = np.exp(x - x.max(axis=1, keepdims=True))
                reference = (values / values.sum(axis=1, keepdims=True)).astype("<f2").reshape(-1)
                assert np.isfinite(reference).all()
                inputs.write(a.tobytes())
                expected.write(reference.tobytes())
                entry["trials"].append({"trial": trial, "family": label, "offset_elements": offset,
                                        "input_sha256": hashlib.sha256(a.tobytes()).hexdigest(),
                                        "expected_sha256": hashlib.sha256(reference.tobytes()).hexdigest()})
                offset += n
            metadata["cases"].append(entry)
    (out / "dataset.json").write_text(json.dumps(metadata, indent=2) + "\n")
    manifest = {str(p.relative_to(out)): sha(p) for p in sorted(out.rglob("*")) if p.is_file()}
    (out / "manifest.json").write_text(json.dumps({"schema": 1, "files": manifest}, indent=2) + "\n")
    print(json.dumps({"paired_trials": 24, "elements_per_method": offset, "source_certificates": 0}))


if __name__ == "__main__":
    main()
