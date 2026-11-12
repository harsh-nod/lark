"""Check source changes against complete finite cached SGLang execution."""

import argparse
import hashlib
import json
from pathlib import Path

from run_symbolic import HERE, execute, native
from lark_kernels.ir import Refusal


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    case = HERE / "cases/native_fixed"
    source = (case / "kernel.hip").read_text()
    task = native.parse_task((case / "task.json").read_text())
    mutations = {
        "unguarded-partial-store": source.replace("if (lane == 0) {\npartial[warp] = sum;\n}", "partial[warp] = sum;", 1),
        "wrong-pair-grouping": source.replace("sum = sum + pair_square;", "sum = (sum + xx) + yy;"),
        "wrong-first-xor": source.replace("__shfl_xor(sum, 16, 32)", "__shfl_xor(sum, 8, 32)", 1),
        "missing-first-barrier": source.replace("__syncthreads();", "", 1),
        "broadcast-inverse-slot": source.replace("float inverse = partial[warp];", "float inverse = partial[0];"),
        "wrong-weight-cache-index": source.replace("__half2float(weight_values[output_slot])", "__half2float(weight_values[0])"),
        "late-input-reload": source.replace("__half2float(input_values[output_slot])",
            "__half2float(input[row * 16384 + (output_iteration * 1024 + tid) * 8 + output_pair * 2])"),
        "aliased-output-store": source.replace("output[store_address]", "output[row * 16384]"),
        "wrong-mean": source.replace("block_sum / 16384.0f", "block_sum / 8192.0f"),
        "wrong-epsilon": source.replace("0.00001f", "0.0001f"),
    }
    before, after = source.rsplit("__syncthreads();", 1)
    mutations["missing-second-barrier"] = before + after
    checks = []
    for name, changed in mutations.items():
        if changed == source:
            raise ValueError("Vacuous mutation " + name)
        try:
            execute(changed, task, True)
        except Refusal as error:
            if error.code not in {"finite-source-order", "finite-footprint", "uninitialized"}:
                raise
            (out / (name + ".hip")).write_text(changed)
            (out / (name + ".log")).write_text(str(error) + "\n")
            checks.append({"name": name, "accepted": False, "code": error.code})
        else:
            raise ValueError("Changed source accepted " + name)
    report = {"schema": 1, "status": "finite-sglang-source-controls-rejected",
              "controls": len(checks), "checks": checks, "source_certificates": 0,
              "whole_kernel_execution_proved": False, "source_reference_equality_proved": False,
              "original_paper_fully_reproduced": False, "model_calls": 0, "gpu_trials": 0}
    (out / "results.json").write_text(json.dumps(report, indent=2) + "\n")
    (out / "manifest.json").write_text(json.dumps({p.name: hashlib.sha256(p.read_bytes()).hexdigest()
        for p in sorted(out.iterdir()) if p.is_file()}, indent=2) + "\n")
    print(json.dumps({k: v for k, v in report.items() if k != "checks"}), flush=True)


if __name__ == "__main__":
    main()
