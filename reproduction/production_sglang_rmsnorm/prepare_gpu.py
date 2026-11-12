"""Freeze SGLang RMSNorm inputs for original, repaired and upstream-body HIP methods.

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
from lark_kernels import native_sglang_rmsnorm as native

HERE = Path(__file__).resolve().parent


def sha(path):
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for data in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(data)
    return h.hexdigest()


from gpu_comparison import upstream_body


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    out = args.output.resolve()
    if out.is_relative_to(ROOT):
        raise ValueError("Fresh numerical input directory outside checkout required")
    import subprocess
    subprocess.run([sys.executable, str(HERE / "gpu_comparison.py"), "--output", str(out)], check=True)
    for name in ("run_gpu.py", "audit_gpu.py", "gpu_comparison.py"):
        shutil.copyfile(HERE / name, out / name)

    import numpy as np
    import torch
    torch.set_num_threads(1)
    metadata = {
        "schema": 1, "methods": ["original", "fixed", "upstream"], "seed": 261102028, "torch": torch.__version__, "numpy": np.__version__,
        "atol": .002, "rtol": .002, "cases": [],
        "upstream_template_body_sha256": hashlib.sha256(upstream_body().encode()).hexdigest(),
        "comparison_helpers": "Explicit HIP aligned half2 vectors, logical32 XOR, rsqrtf, half2 conversion, plain float pair and PDL=false no-ops; selected template body retained verbatim; no CUDA helper/compiler-equivalence proof",
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
                                   * tw).half().numpy().astype("<f2", copy=False).reshape(-1)
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
    manifest = {"files": {p.relative_to(out).as_posix(): sha(p) for p in sorted(out.rglob("*")) if p.is_file() and p.name != "manifest.json"},
                "generator_sha256": sha(Path(__file__))}
    (out / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(json.dumps({"status": "prepared", "trials": 24, "outputs_per_method": offset}), flush=True)


if __name__ == "__main__":
    main()
