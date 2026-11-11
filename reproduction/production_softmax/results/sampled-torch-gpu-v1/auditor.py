"""Compare actual GPU streams directly with the declared FP32 Torch reference."""

import argparse
import ast
import json
from pathlib import Path
import shutil

from audit_gpu import manifest, sha


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--mi350", type=Path, required=True)
    parser.add_argument("--mi350-2", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    data, out = args.input.resolve(), args.output.resolve()
    manifest(data, True)
    reference = '''import torch


def reference(inp):
    return torch.softmax(inp.float(), dim=1).half()
'''
    for case in ("native_race", "native_fixed"):
        if ast.dump(ast.parse((data / case / "reference.py").read_text())) != ast.dump(ast.parse(reference)):
            raise ValueError("Reference AST differs")
    groups = {}
    for host, folder in (("mi350", args.mi350), ("mi350-2", args.mi350_2)):
        manifest(folder)
        for method in ("racy-output", "fixed-output"):
            p = folder / (method + ".bin")
            groups.setdefault(sha(p), {"path": p, "streams": []})["streams"].append(host + ":" + method)
    import numpy as np
    import torch

    torch.set_num_threads(1)
    metadata = json.loads((data / "dataset.json").read_text())
    inputs = np.memmap(data / "input.bin", dtype="<f2", mode="r")
    width = metadata["width"]
    outputs = {h: np.memmap(g["path"], dtype="<f2", mode="r") for h, g in groups.items()}
    counts = {h: {"elements_compared": 0, "failed": 0, "nonfinite": 0,
                  "bit_differences": 0, "max_abs_error": 0.} for h in groups}
    for case in metadata["cases"]:
        rows, n = case["rows"], case["elements"]
        for trial in case["trials"]:
            offset = trial["offset_elements"]
            half = inputs[offset:offset+n].reshape(rows, width)
            for begin in range(0, rows, 16):
                a = np.array(half[begin:begin+16], copy=True)
                target = torch.softmax(torch.from_numpy(a).float(), dim=1).half().numpy()
                ref = target.astype(np.float64)
                for h, values in outputs.items():
                    actual_half = values[offset+begin*width:offset+(begin+a.shape[0])*width].reshape(a.shape)
                    actual = actual_half.astype(np.float64)
                    finite = np.isfinite(actual)
                    absolute = np.abs(actual - ref)
                    counter = counts[h]
                    counter["elements_compared"] += a.size
                    counter["failed"] += int((~finite | (absolute > metadata["atol"] + metadata["rtol"] * np.abs(ref))).sum())
                    counter["nonfinite"] += int((~finite).sum())
                    counter["bit_differences"] += int((actual_half.view("<u2") != target.view("<u2")).sum())
                    counter["max_abs_error"] = max(counter["max_abs_error"], float(absolute.max()))
    passed = all(c["failed"] == 0 and c["nonfinite"] == 0 for c in counts.values())
    out.mkdir(parents=True, exist_ok=False)
    report = {
        "schema": 1, "status": "declared-torch-reference-comparisons-passed" if passed else "declared-torch-reference-mismatch",
        "torch": torch.__version__, "numpy": np.__version__, "input_manifest_sha256": sha(data / "manifest.json"),
        "atol": metadata["atol"], "rtol": metadata["rtol"],
        "unique_output_streams": {h: {"streams": g["streams"], **counts[h]} for h, g in groups.items()},
        "reference_source_executed": False, "closed_reference_ast_checked": True,
        "source_certificates": 0, "formal_reference_equivalence_proved": False,
        "ieee_equivalence_proved": False, "original_paper_fully_reproduced": False,
        "scope": "Every actual GPU output value is compared directly with the closed Torch FP32 softmax/FP16 output specification. Byte-identical streams are compared once per SHA256 and explicitly mapped to their four host/method names. This is finite numerical evidence.",
    }
    (out / "results.json").write_text(json.dumps(report, indent=2) + "\n")
    shutil.copyfile(Path(__file__), out / "auditor.py")
    (out / "manifest.json").write_text(json.dumps({p.name: sha(p) for p in sorted(out.iterdir()) if p.is_file()}, indent=2) + "\n")
    print(json.dumps({"status": report["status"], "unique_streams": len(groups), "counts": counts}))
    if not passed:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
