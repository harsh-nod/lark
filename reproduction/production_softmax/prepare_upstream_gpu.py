"""Recreate the pinned upstream benchmark's full8192x50257 input before FP16 storage.

The exact C rand helpers and outlier loop are retained. C library/compiler
identity and all generated stream hashes are recorded. This is an independently
selected upstream benchmark, not the authors' missing adapted experiment.
"""

import argparse
import hashlib
import json
from pathlib import Path
import platform
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from reproduction.production_softmax.prepare_gpu import DRIVER, HERE, sha  # noqa: E402


def function(text, signature):
    start = text.index(signature)
    brace = text.index("{", start)
    end, depth = brace + 1, 1
    while depth:
        depth += (text[end] == "{") - (text[end] == "}")
        end += 1
    return text[start:end]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    for name in ("native_race", "native_fixed"):
        shutil.copytree(HERE / "cases" / name, out / name)
        task = json.loads((out / name / "task.json").read_text())
        task["launch"]["grid"] = 8192
        for buffer in task["buffers"]:
            buffer["shape"][0] = 8192
        (out / name / "task.json").write_text(json.dumps(task, indent=2) + "\n")
    shutil.copytree(HERE / "upstream", out / "upstream")
    for name in ("provenance.json", "rewrites.json", "run_gpu.py"):
        shutil.copyfile(HERE / name, out / name)
    (out / "driver.hip").write_text(DRIVER)
    helper = (HERE / "upstream/common.h").read_text()
    random_float = function(helper, "float* make_random_float(size_t N)")
    random_int = function(helper, "int* make_random_int(size_t N, int V)")
    upstream = (HERE / "upstream/softmax_forward.cu").read_text()
    for literal in ("int B = 8;", "int T = 1024;", "int V = 50257;", "srand(0);",
                    "inp[j * V + outliers[j*3 + k]] *= 20;"):
        if literal not in upstream:
            raise ValueError("Pinned benchmark setup changed")
    generator = "#include <stdlib.h>\n#include <stdio.h>\n" + random_float + "\n" + random_int + "\n" + r'''
int main(int argc,char** argv) {
  if(argc!=3)return 1;
  const int B=8,T=1024,V=50257;
  srand(0);
  float* inp=make_random_float((size_t)B*T*V);
  if(!inp)return 2;
  const int* outliers=make_random_int(B*T*3,V);
  if(!outliers)return 3;
  for(int k=0;k<3;++k) {
    for(int j=0;j<B*T;++j) {
      inp[j*V+outliers[j*3+k]]*=20;
    }
  }
  FILE* f=fopen(argv[1],"wb");if(!f)return 4;
  if(fwrite(inp,sizeof(float),(size_t)B*T*V,f)!=(size_t)B*T*V)return 5;
  fclose(f);
  f=fopen(argv[2],"wb");if(!f)return 6;
  if(fwrite(outliers,sizeof(int),B*T*3,f)!=(size_t)B*T*3)return 7;
  fclose(f);
  free(inp);free((void*)outliers);return 0;
}
'''
    (out / "input-generator.c").write_text(generator)
    command = ["cc", "-O2", "-std=c11", "-ffp-contract=off", str(out / "input-generator.c"), "-o", str(out / "input-generator")]
    subprocess.run(command, check=True, capture_output=True)
    fp32 = out / "upstream-fp32-input.bin"
    subprocess.run([str(out / "input-generator"), str(fp32), str(out / "outlier-indices.bin")], check=True, timeout=180)
    if sys.byteorder != "little":
        raise ValueError("Current generator snapshot requires little-endian host bytes")
    import numpy as np

    rows, width = 8192, 50257
    raw = np.memmap(fp32, dtype="<f4", mode="r", shape=(rows, width))
    input_hash, expected_hash = hashlib.sha256(), hashlib.sha256()
    with (out / "input.bin").open("wb") as inputs, (out / "expected.bin").open("wb") as expected:
        for begin in range(0, rows, 16):
            half = raw[begin:begin+16].astype("<f2")
            x = half.astype(np.float64)
            exp = np.exp(x - x.max(axis=1, keepdims=True))
            ref = (exp / exp.sum(axis=1, keepdims=True)).astype("<f2")
            a, b = half.tobytes(), ref.tobytes()
            inputs.write(a)
            expected.write(b)
            input_hash.update(a)
            expected_hash.update(b)
    metadata = {
        "schema": 1, "seed": 0, "numpy": np.__version__, "width": width,
        "atol": 2 ** -24, "rtol": 0.002,
        "reference": "CPU float64 stable softmax of exactly promoted FP16 inputs, rounded to FP16 once at the end",
        "source_intermediate_storage": "FP16 exponentials in out, FP32 unrounded sum accumulation, FP16 final output",
        "upstream_benchmark": {"B": 8, "T": 1024, "V": 50257, "srand": 0,
                               "outliers_per_row": 3, "outlier_operation": "multiply selected FP32 inputs by20 before FP16 conversion"},
        "generator_compiler": subprocess.check_output(["cc", "--version"], text=True),
        "generator_command": command, "c_library": platform.libc_ver(),
        "generator_sha256": sha(out / "input-generator.c"), "generator_binary_sha256": sha(out / "input-generator"),
        "upstream_fp32_stream_sha256": sha(fp32), "outlier_indices_sha256": sha(out / "outlier-indices.bin"),
        "cases": [{"rows": rows, "elements": rows * width, "trials": [{"trial": 0, "family": "pinned-upstream-srand0-three-outliers",
                    "offset_elements": 0, "input_sha256": input_hash.hexdigest(), "expected_sha256": expected_hash.hexdigest()}]}],
        "original_paper_fully_reproduced": False, "source_certificates": 0, "model_calls": 0,
    }
    (out / "dataset.json").write_text(json.dumps(metadata, indent=2) + "\n")
    # The source, compiler identity and stream hash reproduce the large FP32
    # precursor. The frozen GPU input uses only its FP16 conversion.
    del raw
    fp32.unlink()
    (out / "input-generator").unlink()
    (out / "manifest.json").write_text(json.dumps({"schema": 1, "files": {
        str(p.relative_to(out)): sha(p) for p in sorted(out.rglob("*")) if p.is_file()}}, indent=2) + "\n")
    print(json.dumps({"paired_trials": 1, "rows": rows, "elements_per_method": rows * width,
                      "upstream_input_generator_retained": True, "source_certificates": 0}))


if __name__ == "__main__":
    main()
