"""Check the closed Torch reference against the independent float64 formula/data."""

import argparse
import ast
import hashlib
import json
from pathlib import Path
import shutil

from audit_gpu import manifest, sha


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    data, out = args.input.resolve(), args.output.resolve()
    manifest(data, True)
    reference = '''import torch


def reference(inp):
    return torch.softmax(inp.float(), dim=1).half()
'''
    for name in ("native_race", "native_fixed"):
        if ast.dump(ast.parse((data / name / "reference.py").read_text())) != ast.dump(ast.parse(reference)):
            raise ValueError("Closed reference AST differs")
    import numpy as np
    import torch

    torch.set_num_threads(1)
    metadata = json.loads((data / "dataset.json").read_text())
    inputs = np.memmap(data / "input.bin", dtype="<f2", mode="r")
    expected = np.memmap(data / "expected.bin", dtype="<f2", mode="r")
    counts = {"elements": 0, "float64_formula_failures": 0, "expected_half_bit_differences": 0,
              "torch_float64_half_bit_differences": 0, "torch_float32_half_bit_differences": 0,
              "torch_float32_tolerance_failures": 0, "max_float64_abs_error": 0.}
    for case in metadata["cases"]:
        rows, width, n = case["rows"], metadata["width"], case["elements"]
        for trial in case["trials"]:
            offset = trial["offset_elements"]
            a, b = inputs[offset:offset+n], expected[offset:offset+n]
            if hashlib.sha256(a.tobytes()).hexdigest() != trial["input_sha256"] or hashlib.sha256(b.tobytes()).hexdigest() != trial["expected_sha256"]:
                raise ValueError("Input/gold trial hash differs")
            a, b = a.reshape(rows, width), b.reshape(rows, width)
            for begin in range(0, rows, 16):
                half = np.array(a[begin:begin+16], copy=True)
                x = half.astype(np.float64)
                exp = np.exp(x - x.max(axis=1, keepdims=True))
                numpy64 = exp / exp.sum(axis=1, keepdims=True)
                tensor = torch.from_numpy(half)
                torch64 = torch.softmax(tensor.double(), dim=1).numpy()
                torch32 = torch.softmax(tensor.float(), dim=1).half().numpy()
                gold = np.asarray(b[begin:begin+16])
                absolute = np.abs(torch64 - numpy64)
                counts["elements"] += gold.size
                counts["float64_formula_failures"] += int((absolute > 1e-15 + 1e-12 * np.abs(numpy64)).sum())
                counts["expected_half_bit_differences"] += int((numpy64.astype("<f2").view("<u2") != gold.view("<u2")).sum())
                counts["torch_float64_half_bit_differences"] += int((torch64.astype("<f2").view("<u2") != gold.view("<u2")).sum())
                counts["torch_float32_half_bit_differences"] += int((torch32.view("<u2") != gold.view("<u2")).sum())
                counts["torch_float32_tolerance_failures"] += int((np.abs(torch32.astype(np.float64) - gold.astype(np.float64)) >
                    metadata["atol"] + metadata["rtol"] * np.abs(gold.astype(np.float64))).sum())
                counts["max_float64_abs_error"] = max(counts["max_float64_abs_error"], float(absolute.max()))
    passed = (counts["float64_formula_failures"] == 0 and counts["expected_half_bit_differences"] == 0
              and counts["torch_float32_tolerance_failures"] == 0)
    out.mkdir(parents=True, exist_ok=False)
    report = {"schema": 1, "status": "closed-torch-reference-numerically-checked" if passed else "reference-mismatch",
              "numpy": np.__version__, "torch": torch.__version__, "input_manifest_sha256": sha(data / "manifest.json"),
              "float64_atol": 1e-15, "float64_rtol": 1e-12, "counts": counts,
              "reference_source_executed": False, "closed_reference_ast_checked": True,
              "formal_reference_equivalence_proved": False, "original_paper_fully_reproduced": False,
              "scope": "Finite CPU cross-check of NumPy float64 stable softmax against Torch float64, expected FP16 bytes against their regenerated formula, and the declared FP32 Torch AST interpretation under the recorded FP16 tolerance. No reference source is executed and no universal interpretation/IEEE theorem is claimed."}
    (out / "results.json").write_text(json.dumps(report, indent=2) + "\n")
    shutil.copyfile(Path(__file__), out / "checker.py")
    (out / "manifest.json").write_text(json.dumps({p.name: sha(p) for p in sorted(out.iterdir()) if p.is_file()}, indent=2) + "\n")
    print(json.dumps({"status": report["status"], "counts": counts}))
    if not passed:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
