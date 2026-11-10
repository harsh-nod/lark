"""CPU PyTorch probes bound to the two certified FFN sources and their wiring."""

import argparse
import hashlib
import json
import math
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from lark_kernels import certificate
from reproduction.matrix.bundle import load_dataset
from reproduction.feedforward.bundle import buffers, wrapper_source, validate_bundle


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
    cert = args.cpu / "baselines/hip"
    certificate.check(cert, lean=args.lean)
    report = json.loads((cert / "report.json").read_text())
    row = {"key": "ffn", "dtype": "float16", "rtol": 0.01, "atol": 0.01, "trials": []}
    names = ("up.cu", "down.cu", "up-task.json", "down-task.json", "reference.py")
    for name in names:
        row[name] = (cert / name).read_text()
    index = {
        "ffn": {
            "status": "verified",
            "profile": report["model_profile"],
            "ffn_dimensions": report["ffn_dimensions"],
            "model_hashes": report["model_hashes"],
            "theorem_sha256": sha(cert / "Main.lean"),
            "source_hashes": {name: sha(cert / name) for name in names},
        }
    }
    gen = torch.Generator().manual_seed(261102028)
    env = {}
    exec(compile(row["reference.py"], "reference.py", "exec"), env)
    with (args.output / "tensors.f16").open("wb") as f:

        def packed(x):
            payload = x.contiguous().numpy().tobytes()
            offset = f.tell()
            f.write(payload)
            return {
                "offset": offset,
                "bytes": len(payload),
                "sha256": hashlib.sha256(payload).hexdigest(),
            }

        for trial in range(10):
            inputs, allocated = [], []
            for declared in buffers(row):
                size = math.prod(declared["shape"])
                b = {"role": declared["role"], "dtype": "float16", "size": size}
                if declared["role"] == "input":
                    if trial < 6:
                        x = torch.randn(declared["shape"], generator=gen) * 0.25
                    elif trial == 6:
                        x = torch.zeros(declared["shape"])
                    elif trial == 7:
                        x = torch.full(declared["shape"], 0.125)
                    elif trial == 8:
                        x = (
                            torch.tensor([-0.125, 0.125])
                            .repeat(size // 2)
                            .reshape(declared["shape"])
                        )
                    else:
                        x = torch.rand(declared["shape"], generator=gen) * 0.5 - 0.25
                    x = x.half()
                    inputs.append(x)
                    b["packed"] = packed(x)
                allocated.append(b)
            hidden = (inputs[0].float() @ inputs[1].float()).relu().half()
            final = env["reference"](*inputs)
            expected = torch.cat((hidden.flatten(), final.flatten()))
            row["trials"].append(
                {"trial": trial, "buffers": allocated, "expected_packed": packed(expected)}
            )
    wrapper = wrapper_source(row)
    data = {
        "schema": 1,
        "reference": "CPU PyTorch " + torch.__version__,
        "seed": 261102028,
        "model_calls": 0,
        "runner_sha256": sha(Path(__file__)),
        "cases": [row],
        "tensor_data_sha256": sha(args.output / "tensors.f16"),
        "wrapper_sha256": hashlib.sha256(wrapper.encode()).hexdigest(),
    }
    (args.output / "cases.json").write_text(json.dumps(data, indent=2) + "\n")
    (args.output / "certificate-index.json").write_text(json.dumps(index, indent=2) + "\n")
    (args.output / "certified.hip").write_text(wrapper)
    validate_bundle(load_dataset(args.output), index, wrapper)
    print("Prepared ten FFN trials, checking every intermediate and final output")


if __name__ == "__main__":
    main()
