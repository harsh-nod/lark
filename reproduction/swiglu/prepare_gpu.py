"""CPU PyTorch FP32/FP16 expectations for all four certified SwiGLU stages."""

import argparse
import hashlib
import json
import math
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from lark_kernels import certificate, swiglu
from reproduction.swiglu.bundle import (
    TOLERANCES,
    buffers,
    load_dataset,
    wrapper_source,
    validate_bundle,
)


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
    row = {"key": "swiglu", "tolerances": TOLERANCES, "trials": []}
    for name in swiglu.SOURCE_FILES:
        row[name] = (cert / name).read_text()
    index = {
        "swiglu": {
            "status": "verified",
            "profile": report["model_profile"],
            "swiglu_dimensions": report["swiglu_dimensions"],
            "model_hashes": report["model_hashes"],
            "theorem_sha256": sha(cert / "Main.lean"),
            "source_hashes": {n: sha(cert / n) for n in swiglu.SOURCE_FILES},
        }
    }
    gen = torch.Generator().manual_seed(261102028)
    env = {}
    exec(compile(row["reference.py"], "reference.py", "exec"), env)
    with (args.output / "tensors.bin").open("wb") as f:

        def packed(x):
            raw = x.contiguous().numpy().tobytes()
            offset = f.tell()
            f.write(raw)
            return {"offset": offset, "bytes": len(raw), "sha256": hashlib.sha256(raw).hexdigest()}

        for trial in range(10):
            inputs, allocated = [], []
            for e in buffers(row):
                size = math.prod(e["shape"])
                b = {"role": e["role"], "dtype": e["dtype"], "size": size}
                if b["role"] == "input":
                    if trial < 6:
                        x = torch.randn(e["shape"], generator=gen) * 0.25
                    elif trial == 6:
                        x = torch.zeros(e["shape"])
                    elif trial == 7:
                        x = torch.full(e["shape"], 0.125)
                    elif trial == 8:
                        x = torch.tensor([-0.125, 0.125]).repeat(size // 2).reshape(e["shape"])
                    else:
                        x = torch.rand(e["shape"], generator=gen) * 0.5 - 0.25
                    x = x.half()
                    inputs.append(x)
                    b["packed"] = packed(x)
                allocated.append(b)
            gate = inputs[0].float() @ inputs[1].float()
            up = inputs[0].float() @ inputs[2].float()
            hidden = (torch.nn.functional.silu(gate) * up).half()
            final = env["reference"](*inputs)
            for b, x in zip(allocated[4:], (gate, up, hidden, final)):
                b["expected_packed"] = packed(x)
            row["trials"].append({"trial": trial, "buffers": allocated})
    wrapper = wrapper_source(row)
    data = {
        "schema": 1,
        "reference": "CPU PyTorch " + torch.__version__,
        "seed": 261102028,
        "model_calls": 0,
        "runner_sha256": sha(Path(__file__)),
        "cases": [row],
        "tensor_data_sha256": sha(args.output / "tensors.bin"),
        "wrapper_sha256": hashlib.sha256(wrapper.encode()).hexdigest(),
    }
    (args.output / "cases.json").write_text(json.dumps(data, indent=2) + "\n")
    (args.output / "certificate-index.json").write_text(json.dumps(index, indent=2) + "\n")
    (args.output / "certified.hip").write_text(wrapper)
    validate_bundle(load_dataset(args.output), index, wrapper)
    print("Prepared ten mixed FP32/FP16 SwiGLU trials with all intermediates checked")


if __name__ == "__main__":
    main()
