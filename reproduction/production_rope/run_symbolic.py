"""Finite complete-source Q/K execution, value comparison and trace ownership.

This is an untrusted independent preflight, not a universal execution theorem.
"""

import argparse
from dataclasses import replace
import gzip
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from lark_kernels import native_rope as native
from lark_kernels.ir import node

HERE = Path(__file__).resolve().parent


def expected(layout, buffer, offset):
    width = (4096, 1024)[buffer]
    row, col = divmod(offset, width)
    head, component = divmod(col, 128)
    if layout == "split-half":
        j, imaginary = component % 64, component >= 64
        x, y = head * 128 + j, head * 128 + j + 64
    else:
        j, imaginary = component // 2, bool(component % 2)
        x, y = head * 128 + j * 2, head * 128 + j * 2 + 1
    load = lambda b, i: node("un", "fromHalf", node("input", b, i))
    xf, yf = load(buffer, row * width + x), load(buffer, row * width + y)
    c, s = load(2, row * 128 + j), load(2, row * 128 + j + 64)
    mul = lambda a, b: node("bin", "mul", a, b)
    value = (node("bin", "add", mul(yf, c), mul(xf, s)) if imaginary else
             node("bin", "sub", mul(xf, c), mul(yf, s)))
    return node("un", "toHalf", value)


def check(case, rows, *, source=None):
    raw = json.loads((case / "task.json").read_text())
    raw["launch"]["grid"] = rows
    for b in raw["buffers"]:
        b["shape"][0] = rows
    contract = native.parse_task(json.dumps(raw))
    native.check_reference((case / "reference.py").read_text(), contract.rotary_layout)
    text = source if source is not None else (case / "kernel.hip").read_text()
    tr = native.translate(text, contract)
    machine = native.AccessPreflight(contract, tr).run()
    writes = set()
    for a in machine.trace:
        if a.epoch != (0, 0, 0):
            raise ValueError("Unexpected synchronization epoch")
        if a.write:
            if a.location in writes:
                raise ValueError("Output cell written more than once")
            writes.add(a.location)
    if len(machine.trace) != rows * 15360 or len(writes) != rows * 5120:
        raise ValueError("Incomplete native traversal")
    values = machine.outputs()
    wanted = [expected(contract.rotary_layout, b, i) for b, width in ((0, 4096), (1, 1024))
              for i in range(rows * width)]
    if values != wanted:
        raise ValueError("Full output differs from independent source-order reference")
    if any(machine.memory[("global", 0, 2, i)] != node("input", 2, i) for i in range(rows * 128)):
        raise ValueError("Read-only gathered cache changed")
    if any(t.pc != 49 for t in machine.threads):
        raise ValueError("Incomplete native halt")
    records = [[a.thread, list(a.location), a.write, list(a.epoch)] for a in machine.trace]
    trace = (json.dumps(records, separators=(",", ":")) + "\n").encode()
    output = (json.dumps([v.data() for v in values], separators=(",", ":")) + "\n").encode()
    return {"layout": contract.rotary_layout, "rows": rows, "instructions": len(tr.program),
            "outputs": len(values), "accesses": len(records), "unique_writes": len(writes),
            "all_threads_halt_pc": 49, "all_epochs": [0, 0, 0],
            "all_actual_accesses_classified": True, "cache_unchanged": True,
            "trace_sha256": hashlib.sha256(trace).hexdigest(),
            "output_expression_sha256": hashlib.sha256(output).hexdigest()}, trace, output


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    results, controls = [], []
    for kind in native.LAYOUTS:
        case = HERE / "cases" / kind
        for rows in (1, 3):
            result, trace, output = check(case, rows)
            prefix = f"{kind}-{rows}"
            (out / (prefix + "-trace.json.gz")).write_bytes(gzip.compress(trace, mtime=0))
            (out / (prefix + "-outputs.json.gz")).write_bytes(gzip.compress(output, mtime=0))
            results.append(result)
        text = (case / "kernel.hip").read_text()
        changes = {
            "overlapping-pairs": ("int qx = qr;", "int qx = 0;") if kind == "split-half" else
                                  ("int qx = 2 * qr;", "int qx = 0;"),
            "wrong-stride": ("qi = qi + 512;", "qi = qi + 511;"),
            "wrong-cache-half": ("int qcb = qca + 64;", "int qcb = qca + 63;"),
            "wrong-subtraction": ("float qox = qxc - qys;", "float qox = qys - qxc;"),
            "missing-second-store": ("    query[qb] = __float2half(qoy);\n", ""),
        }
        for name, (before, after) in changes.items():
            if text.count(before) != 1:
                raise ValueError("Ambiguous symbolic control")
            try:
                check(case, 1, source=text.replace(before, after))
            except (ValueError, native.Refusal) as error:
                controls.append({"layout": kind, "name": name, "accepted": False, "reason": str(error)})
            else:
                raise ValueError("Bad source accepted: " + name)
    report = {"schema": 1, "status": "finite-native-rope-source-values-and-traces-checked",
              "cases": results, "false_sources_rejected": controls,
              "complete_native_launch_theorem": False, "source_certificates": 0,
              "model_calls": 0, "gpu_trials": 0, "original_paper_fully_reproduced": False}
    (out / "results.json").write_text(json.dumps(report, indent=2) + "\n")
    (out / "manifest.json").write_text(json.dumps({p.name: hashlib.sha256(p.read_bytes()).hexdigest()
                                                   for p in sorted(out.iterdir())}, indent=2) + "\n")
    print(json.dumps({"status": report["status"], "cases": len(results),
                      "outputs": sum(r["outputs"] for r in results),
                      "accesses": sum(r["accesses"] for r in results), "false_sources_rejected": len(controls)}))


if __name__ == "__main__":
    main()
