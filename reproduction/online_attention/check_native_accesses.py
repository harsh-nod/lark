"""Value-erased finite access preflight of the full native 128x256 source.

This does not evaluate tensor values or prove universal execution/trace erasure.
The independent Lean footprint theorem is conditional on its access predicate.
"""

import argparse
import hashlib
import json
from pathlib import Path
import sys
import time

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from lark_kernels import native_attention as native  # noqa: E402
from lark_kernels.ir import Refusal  # noqa: E402

CASE = Path(__file__).resolve().parent / "cases/native_fp16"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    source = (CASE / "kernel.hip").read_text()
    task = native.parse_task((CASE / "task.json").read_text())
    records = []
    for name, candidate, expected in (
        ("baseline", source, None),
        ("missing-load-barrier", source.replace("    __syncthreads();", "", 1), "native-attention-footprint"),
        ("wrong-tile-store-owner", source.replace("kj[lane * 256 + load_x]", "kj[load_x]"), "native-attention-footprint"),
        ("missing-output-initialization", source.replace(
            "out[base + (init_i * 32 + lane) * 256 + init_x] = __float2half(0.0f);", ""), "uninitialized"),
    ):
        (out / (name + ".hip")).write_text(candidate)
        tr = native.translate(candidate, task)
        started = time.monotonic()
        machine = native.AccessPreflight(task, tr)
        try:
            machine.run()
            outputs = machine.initialized_output_slots()
            if expected is not None:
                raise ValueError("Incorrect source passed access preflight: " + name)
            if outputs != 32768 or any(t.pc != 90 or t.epoch != [0, 8, 0] for t in machine.threads):
                raise ValueError("Incomplete native launch in finite preflight")
            for method, expected_code in ((machine.outputs, "values-erased"), (machine.race, "trace-erased")):
                try:
                    method()
                except Refusal as error:
                    if error.code != expected_code:
                        raise
                else:
                    raise ValueError("Erased preflight exposed unavailable values or an unchecked RF result")
            record = {"name": name, "status": "completed", "output_slots_initialized": outputs,
                      "erased_value_and_trace_apis_refuse": True,
                      "accesses": machine.total_accesses, "access_counts": machine.access_counts}
        except Refusal as error:
            if expected != error.code:
                raise
            record = {"name": name, "status": "refused", "code": error.code, "message": error.detail,
                      "accesses_before_refusal": machine.total_accesses}
        record["seconds"] = time.monotonic() - started
        records.append(record)
        print(json.dumps(record), flush=True)
    report = {"status": "passed", "cases": records, "full_shape": [1, 128, 256],
              "source_sha256": hashlib.sha256(source.encode()).hexdigest(),
              "values_erased": True, "data_equivalence_checked": False,
              "universal_execution_or_trace_erasure_proved": False,
              "source_certificates": 0, "gpu_trials": 0, "model_calls": 0,
              "original_paper_fully_reproduced": False}
    (out / "results.json").write_text(json.dumps(report, indent=2) + "\n")
    (out / "manifest.json").write_text(json.dumps(
        {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(out.iterdir()) if p.is_file()},
        indent=2) + "\n")


if __name__ == "__main__":
    main()
