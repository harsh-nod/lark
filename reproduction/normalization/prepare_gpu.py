"""Prepare exact certified-source normalization probes and CPU PyTorch expected outputs."""

import argparse
import hashlib
import json
import math
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from lark_kernels import certificate
from reproduction.matrix.bundle import load_dataset
from reproduction.nonlinear.gpu_bundle import wrapper_source, validate_bundle


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--cpu", type=Path, required=True)
    p.add_argument("--output", type=Path, required=True)
    p.add_argument("--lean", required=True)
    args = p.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    import torch

    torch.set_num_threads(1)
    generator = torch.Generator().manual_seed(261102028)
    index, rows = {}, []
    with (args.output / "tensors.f16").open("wb") as binary:

        def packed(tensor):
            payload = tensor.contiguous().numpy().tobytes()
            start = binary.tell()
            binary.write(payload)
            return {
                "offset": start,
                "bytes": len(payload),
                "sha256": hashlib.sha256(payload).hexdigest(),
            }

        for family in ("rms", "layer", "softmax"):
            cert = args.cpu / "baselines" / family / "hip"
            certificate.check(cert, lean=args.lean)
            report = json.loads((cert / "report.json").read_text())
            row = {"key": family, "dtype": "float16", "rtol": 0.01, "atol": 0.01, "trials": []}
            index[family] = {
                "status": "verified",
                "profile": report["model_profile"],
                "normalization_kind": report["normalization_kind"],
                "elements": report["elements"],
                "model_hashes": report["model_hashes"],
                "theorem_sha256": sha(cert / "Main.lean"),
            }
            for name, file in [
                ("source", "kernel.cu"),
                ("reference", "reference.py"),
                ("task", "task.json"),
            ]:
                row[name + "_text"] = (cert / file).read_text()
                row[name + "_sha256"] = index[family][name + "_sha256"] = sha(cert / file)
            task = json.loads(row["task_text"])
            env = {}
            exec(compile(row["reference_text"], "reference.py", "exec"), env)
            for trial in range(10):
                inputs, buffers = [], []
                for b in task["buffers"]:
                    size = math.prod(b["shape"])
                    buffer = {"role": b["role"], "dtype": b["dtype"], "size": size}
                    if b["role"] == "input":
                        if trial < 6:
                            x = torch.randn(b["shape"], generator=generator) * 0.25
                        elif trial == 6:
                            x = torch.zeros(b["shape"])
                        elif trial == 7:
                            x = torch.full(b["shape"], 0.125)
                        elif trial == 8:
                            x = torch.tensor([-0.125, 0.125]).repeat(size // 2).reshape(b["shape"])
                        else:
                            x = torch.rand(b["shape"], generator=generator) * 0.5 - 0.25
                        x = x.half()
                        inputs.append(x)
                        buffer["packed"] = packed(x)
                    buffers.append(buffer)
                expected = env["reference"](*inputs)
                row["trials"].append(
                    {"trial": trial, "buffers": buffers, "expected_packed": packed(expected)}
                )
            rows.append(row)
    wrapper = wrapper_source(rows)
    data = {
        "schema": 1,
        "reference": "CPU PyTorch " + torch.__version__,
        "seed": 261102028,
        "model_calls": 0,
        "runner_sha256": sha(Path(__file__)),
        "cases": rows,
        "tensor_data_sha256": sha(args.output / "tensors.f16"),
        "wrapper_sha256": hashlib.sha256(wrapper.encode()).hexdigest(),
    }
    (args.output / "cases.json").write_text(json.dumps(data, indent=2) + "\n")
    (args.output / "certificate-index.json").write_text(json.dumps(index, indent=2) + "\n")
    (args.output / "certified.hip").write_text(wrapper)
    validate_bundle(load_dataset(args.output), index, wrapper)
    print("Prepared 30 full-size normalization trials with binary FP16 probes")


if __name__ == "__main__":
    main()
