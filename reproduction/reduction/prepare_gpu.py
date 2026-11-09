"""Prepare full-size matrix/vector inputs bound to the checked HIP certificate."""

import argparse
import hashlib
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from lark_kernels import certificate
from reproduction.nonlinear.gpu_bundle import wrapper_source, validate_bundle


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--cpu", type=Path, required=True)
    p.add_argument("--output", type=Path, required=True)
    p.add_argument("--lean", required=True)
    args = p.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    import torch

    torch.set_num_threads(1)
    cert = args.cpu / "baselines/hip"
    certificate.check(cert, lean=args.lean)
    report = json.loads((cert / "report.json").read_text())
    row = {"key": "gemv", "dtype": "float16", "rtol": 0.01, "atol": 0.01, "trials": []}
    index = {
        "gemv": {
            "status": "verified",
            "profile": report["model_profile"],
            "matrix_shape": report["matrix_shape"],
            "model_hashes": report["model_hashes"],
            "theorem_sha256": sha(cert / "Main.lean"),
        }
    }
    for key, file in [
        ("source", "kernel.cu"),
        ("reference", "reference.py"),
        ("task", "task.json"),
    ]:
        row[key + "_text"] = (cert / file).read_text()
        row[key + "_sha256"] = index["gemv"][key + "_sha256"] = sha(cert / file)
    task = json.loads(row["task_text"])
    env = {}
    exec(compile(row["reference_text"], "reference.py", "exec"), env)
    generator = torch.Generator().manual_seed(261102028)
    for trial in range(10):
        inputs = []
        buffers = []
        for b in task["buffers"]:
            size = b["shape"][0] * b["shape"][1]
            data = None
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
                data = x.flatten().tolist()
            buffers.append({"role": b["role"], "dtype": b["dtype"], "size": size, "values": data})
        expected = env["reference"](*inputs).flatten().tolist()
        row["trials"].append({"trial": trial, "buffers": buffers, "expected": expected})
    wrapper = wrapper_source([row])
    dataset = {
        "schema": 1,
        "reference": "CPU PyTorch " + torch.__version__,
        "cases": [row],
        "seed": 261102028,
        "model_calls": 0,
        "wrapper_sha256": hashlib.sha256(wrapper.encode()).hexdigest(),
        "runner_sha256": sha(Path(__file__)),
    }
    validate_bundle(dataset, index, wrapper)
    (args.output / "cases.json").write_text(json.dumps(dataset) + "\n")
    (args.output / "certified.hip").write_text(wrapper)
    (args.output / "certificate-index.json").write_text(json.dumps(index, indent=2) + "\n")
    print("Prepared ten [512,1024] certified-source GPU trials")


if __name__ == "__main__":
    main()
