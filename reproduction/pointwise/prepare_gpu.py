"""Bind CPU PyTorch trials to the exact full-length HIP certificates."""

import argparse
import hashlib
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from lark_kernels import certificate
from reproduction.nonlinear.gpu_bundle import wrapper_source, validate_bundle

ROOT = Path(__file__).resolve().parent


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--cpu", required=True, type=Path)
    p.add_argument("--output", required=True, type=Path)
    p.add_argument("--lean", required=True)
    args = p.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    import torch

    torch.set_num_threads(1)
    dataset = {
        "schema": 1,
        "reference": "CPU PyTorch " + torch.__version__,
        "seed": 261102028,
        "cases": [],
        "model_calls": 0,
        "runner_sha256": sha(Path(__file__)),
    }
    index = {}
    for family in ("relu", "silu", "gelu"):
        cert = args.cpu / "baselines/hip" / family
        certificate.check(cert, lean=args.lean)
        record = json.loads((cert / "report.json").read_text())
        row = {"key": family, "dtype": "float16", "rtol": 0.01, "atol": 0.01, "trials": []}
        index[family] = {
            "status": "verified",
            "theorem_sha256": sha(cert / "Main.lean"),
            "model_hashes": record["model_hashes"],
            "elements": record["elements"],
            "profile": record["model_profile"],
        }
        for key, filename in [
            ("source", "kernel.cu"),
            ("reference", "reference.py"),
            ("task", "task.json"),
        ]:
            row[key + "_text"] = (cert / filename).read_text()
            row[key + "_sha256"] = index[family][key + "_sha256"] = sha(cert / filename)
        task = json.loads(row["task_text"])
        n = record["elements"]
        env = {}
        # These are our committed fixtures, never arbitrary verifier input.
        exec(compile(row["reference_text"], "reference.py", "exec"), env)
        generator = torch.Generator(device="cpu").manual_seed(dataset["seed"])
        for trial in range(10):
            if trial < 6:
                x = torch.randn(n, generator=generator) * 0.25
            elif trial == 6:
                x = torch.zeros(n)
            elif trial == 7:
                x = torch.full((n,), 0.125)
            elif trial == 8:
                x = torch.tensor([-0.125, 0.125]).repeat(n // 2)
            else:
                x = torch.rand(n, generator=generator) * 0.5 - 0.25
            x = x.half()
            expected = env["reference"](x)
            row["trials"].append(
                {
                    "trial": trial,
                    "expected": expected.tolist(),
                    "buffers": [
                        {
                            "role": b["role"],
                            "dtype": b["dtype"],
                            "size": n,
                            "values": x.tolist() if b["role"] == "input" else None,
                        }
                        for b in task["buffers"]
                    ],
                }
            )
        dataset["cases"].append(row)
    wrapper = wrapper_source(dataset["cases"])
    dataset["wrapper_sha256"] = hashlib.sha256(wrapper.encode()).hexdigest()
    validate_bundle(dataset, index, wrapper)
    (args.output / "cases.json").write_text(json.dumps(dataset) + "\n")
    (args.output / "certificate-index.json").write_text(json.dumps(index, indent=2) + "\n")
    (args.output / "certified.hip").write_text(wrapper)
    print("Prepared 30 full-length exact-source GPU trials after Lean rechecks")


if __name__ == "__main__":
    main()
