"""Export and freshly recheck native RMSNorm certificates and IR identity controls."""

import argparse
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from lark_kernels import native_rmsnorm_certificate as native  # noqa: E402
from lark_kernels.certificate import check  # noqa: E402


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--lean")
    parser.add_argument("--timeout", type=float, default=600)
    args = parser.parse_args()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    case = Path(__file__).resolve().parent / "cases/weighted_16384"
    cases = []
    for rows in (1, 3, 64, 255):
        task = json.loads((case / "task.json").read_text())
        task["buffers"][0]["shape"][0] = rows
        task["buffers"][1]["shape"][0] = rows
        task["launch"]["grid"] = rows
        task_path = output / f"task-rows-{rows}.json"
        task_path.write_text(json.dumps(task, indent=2) + "\n")
        destination = output / "certificates" / f"rows-{rows}"
        report = native.verify(case / "kernel.hip", case / "reference.py", task_path, destination,
                               lean=args.lean, timeout=args.timeout)
        if report["status"] != "verified":
            raise RuntimeError(report["axiom_audit"])
        log = check(destination, lean=args.lean, timeout=args.timeout)
        (output / f"recheck-rows-{rows}.log").write_text(log)
        cases.append({"rows": rows, "certificate": str(destination.relative_to(output)),
                      "status": "verified", "fresh_recheck": True, "output_elements": rows * 16384})
        print(json.dumps(cases[-1]), flush=True)
    source = (case / "kernel.hip").read_text()
    changes = {
        "wrong-final-offset": source.replace("__shfl_down(variance, 8, 16)", "__shfl_down(variance, 4, 16)"),
        "removed-first-barrier": source.replace("  __syncthreads();", "", 1),
        "wrong-weight-index": source.replace("weight[outVector * 8 + outComponent]", "weight[0]"),
        "unguarded-partial-store": source.replace("if (lane == 0) { partials[warp] = variance; }", "partials[warp] = variance;"),
    }
    controls = []
    for name, changed in changes.items():
        directory = output / "controls" / name
        directory.mkdir(parents=True)
        kernel = directory / "kernel.hip"
        kernel.write_text(changed)
        report = native.verify(kernel, case / "reference.py", case / "task.json", directory / "export",
                               lean=args.lean, timeout=args.timeout)
        log = report["axiom_audit"]
        if report["status"] != "unproved" or "program_data" not in log or "decide" not in log or "maximum" in log or "Stack overflow" in log:
            raise RuntimeError("Unexpected source-identity control result: " + name + "\n" + log)
        controls.append({"name": name, "accepted": False, "claim": "IR identity only"})
        print(json.dumps(controls[-1]), flush=True)
    report = {
        "status": "passed", "model_profile": native.PROFILE,
        "certificates": len(cases), "fresh_rechecks": len(cases),
        "whole_launch_proved": True, "canonical_real_reference_proved": True,
        "formal_shape_domain": {"rows_min": 1, "rows_max": 255, "width": 16384,
                                "block": 1024, "physical_warp": 64, "vector": 8},
        "cases": cases, "source_identity_controls": controls,
        "model_calls": 0, "original_paper_fully_reproduced": False,
        "ieee_equivalence_or_error_bound": False, "full_upstream_api": False,
        "scope": native.SCOPE,
    }
    (output / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    files = {str(p.relative_to(output)): hashlib.sha256(p.read_bytes()).hexdigest()
             for p in sorted(output.rglob("*")) if p.is_file()}
    (output / "manifest.json").write_text(json.dumps(files, indent=2) + "\n")
    print(json.dumps(report), flush=True)


if __name__ == "__main__":
    main()
