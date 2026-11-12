"""Finite actual native-MFMA AWQ dataflow/traffic checks; no Lean certificate."""

import argparse
from collections import Counter
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import shutil
import sys
import time

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from lark_kernels import native_awq_gemm as native  # noqa: E402
from lark_kernels.ir import Refusal, node  # noqa: E402
from reproduction.production_awq_gemm.symbolic_reference import expression_hashes, output_expression  # noqa: E402

HERE = Path(__file__).resolve().parent
CASES = ("m17_k32_n64", "m17_k32_n128", "m33_k64_n192", "m33_k64_n256")


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n")


def expected_traffic(shape):
    rows = (shape.m+15)//16
    return {("global", 0, False): shape.m*shape.k*shape.column_tiles,
            ("global", 1, False): rows*shape.k*shape.n,
            ("global", 2, True): shape.m*shape.n,
            ("shared", 0, False): shape.grid*shape.k*16,
            ("shared", 0, True): shape.grid*shape.k*16,
            ("shared", 1, False): shape.grid*shape.k*shape.tile_n,
            ("shared", 1, True): shape.grid*shape.k*shape.tile_n}


def check_case(case, out):
    task = native.parse_task((case/"task.json").read_text())
    shape = native.shape_of(task)
    source = (case/"kernel.hip").read_text()
    native.check_reference((case/"reference.py").read_text())
    assert source == native.kernel_source(shape)
    tr = native.translate(source, task)
    before = time.monotonic()
    machine = native.Machine(task, tr).run()
    assert machine.race() is None
    actual = machine.outputs()
    digest = hashlib.sha256()
    for offset, value in enumerate(actual):
        row, col = divmod(offset, shape.n)
        expected = output_expression(shape.m, shape.k, shape.n, row, col)
        assert value == expected, (row, col)
        # Hash one anchored expression at a time to keep the audit's peak
        # memory bounded independently of the number of output cells.
        digest.update(bytes.fromhex(expression_hashes([value])[0]))
    actual_traffic = Counter((a.location[0], a.location[2], a.write) for a in machine.trace)
    assert dict(actual_traffic) == expected_traffic(shape), actual_traffic
    assert all(machine.cut(t) == "halt" for t in range(len(machine.threads)))
    assert all(thread.epoch == [0, 2*(shape.k//32), 0] for thread in machine.threads)
    for b in (0, 1):
        assert all(machine.memory[("global", 0, b, i)] == node("input", b, i)
                   for i in range(task.buffers[b].size))
    writes = Counter(a.location[3] for a in machine.trace if a.location[:3] == ("global", 0, 2) and a.write)
    assert writes == Counter(range(shape.m*shape.n))
    out.mkdir()
    for name in ("kernel.hip", "task.json", "reference.py"):
        shutil.copyfile(case/name, out/name)
    write(out/"translation.json", tr.data())
    result = {"case": case.name, "shape": [shape.m, shape.k, shape.n], "tile_n": shape.tile_n,
              "grid": shape.grid, "block": 64, "physical_warp": 64, "fuel": list(task.fuel),
              "instructions": len(tr.program), "matrix_sites_per_k32": sum(i.op == "mfma" for i in tr.program),
              "source_sha256": sha(case/"kernel.hip"), "task_sha256": sha(case/"task.json"),
              "outputs_matched": len(actual), "events": len(machine.trace),
              "output_expression_sha256": digest.hexdigest(), "actual_trace_conflicts": 0,
              "one_writer_per_output": True, "input_buffers_unchanged": True, "all_threads_halted": True,
              "block_epochs": 2*(shape.k//32), "seconds": time.monotonic()-before,
              "traffic": [{"space": k[0], "buffer": k[1], "write": k[2], "events": v}
                          for k, v in sorted(actual_traffic.items())]}
    write(out/"results.json", result)
    return result


def check_mutants(out):
    base = HERE/"cases/m33_k64_n192"
    task = native.parse_task((base/"task.json").read_text())
    shape = native.shape_of(task)
    source = (base/"kernel.hip").read_text()
    mutations = {
        "wrong-matrix-right-operand": source.replace("(left0, right0_0, acc0,", "(left0, left0, acc0,", 1),
        "missing-reuse-barrier": source.replace("    __syncthreads();\n", "", 1),
        "missing-staging-barrier": "".join(source.rsplit("    __syncthreads();\n", 1)),
        "wrong-k-trip-count": source.replace("while (kTile < 2)", "while (kTile < 1)", 1),
        "aliased-output-columns": source.replace(
            "+ 0 + lane % 16] = __float2half(acc0[0]);",
            "+ 0 + lane % 8] = __float2half(acc0[0]);", 1),
        "erased-output-half-conversion": source.replace("__float2half(acc0[0])", "acc0[0]", 1),
    }
    records = []
    for name, changed in mutations.items():
        assert changed != source, name
        (out/(name+".hip")).write_text(changed)
        before = time.monotonic()
        gate, diagnostic = None, None
        try:
            tr = native.translate(changed, task)
            machine = native.Machine(task, tr).run()
            conflict = machine.race()
            if conflict:
                gate, diagnostic = "actual-trace-conflict", str(conflict)
            elif any(thread.epoch != [0, 2*(shape.k//32), 0] for thread in machine.threads):
                gate, diagnostic = "changed-barrier-schedule", "Actual final block epochs differ"
            else:
                actual = machine.outputs()
                for i, value in enumerate(actual):
                    row, col = divmod(i, shape.n)
                    if value != output_expression(shape.m, shape.k, shape.n, row, col):
                        gate, diagnostic = "source-order-output-mismatch", f"Dense row{row} column{col} differs"
                        break
        except Refusal as error:
            gate, diagnostic = "frontend-or-execution-refusal", str(error)
        assert gate is not None, "Changed source accepted: " + name
        assert "fuel" not in diagnostic.lower(), "A fuel failure is not a semantic rejection"
        records.append({"name": name, "accepted": False, "gate": gate, "diagnostic": diagnostic,
                        "seconds": time.monotonic()-before, "timed_out": False})
    return records


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    out = args.output.resolve()
    assert not any((p/".git").exists() for p in (out, *out.parents)), "Output must be outside Git"
    out.mkdir(parents=True, exist_ok=False)
    cases = [check_case(HERE/"cases"/name, out/name) for name in CASES]
    controls = out/"controls"
    controls.mkdir()
    mutations = check_mutants(controls)
    write(out/"controls.json", mutations)
    result = {"schema": 1, "status": "native-awq-typed-matrix-finite-dataflow-and-traffic-checked",
              "checked_at_utc": datetime.now(timezone.utc).isoformat(), "cases": cases,
              "finite_native_launches": len(cases), "outputs_matched": sum(c["outputs_matched"] for c in cases),
              "trace_events": sum(c["events"] for c in cases), "semantic_controls_rejected": len(mutations),
              "source_certificates": 0, "whole_kernel_execution_proved": False,
              "actual_whole_trace_race_freedom_proved": False, "source_reference_equality_proved": False,
              "ieee_equivalence_proved": False, "original_paper_fully_reproduced": False,
              "gpu_trials": 0, "model_calls": 0}
    shutil.copyfile(Path(__file__), out/"checker.py")
    shutil.copyfile(HERE/"symbolic_reference.py", out/"symbolic_reference.py")
    write(out/"results.json", result)
    write(out/"manifest.json", {str(p.relative_to(out)): sha(p) for p in sorted(out.rglob("*")) if p.is_file()})
    print(json.dumps({k: result[k] for k in ("status", "finite_native_launches", "outputs_matched", "trace_events", "semantic_controls_rejected")}))


if __name__ == "__main__":
    main()
