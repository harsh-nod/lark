"""Finite native fused normalization/rotation execution and independent DAG values.

The reference here preserves the source reduction tree. Dense Torch reference
equality and universal launch/race freedom remain separate proof obligations.
"""

import argparse
from functools import lru_cache
import gzip
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from lark_kernels import native_qknorm_rope as native
from lark_kernels.ir import Node, literal, node

HERE = Path(__file__).resolve().parent


def expected_values(layout, rows):
    load = lambda b, i: node("un", "fromHalf", node("input", b, i))
    binop = lambda op, x, y: node("bin", op, x, y)

    @lru_cache(None)
    def tree(row, head, lane, stage):
        if stage:
            return binop("add", tree(row, head, lane, stage - 1),
                         tree(row, head, lane ^ (1 << (5 - stage)), stage - 1))
        total = literal(0)
        for i in range(4):
            x = load(1, row * 6144 + head * 128 + lane * 4 + i)
            total = binop("add", total, binop("mul", x, x))
        return total

    @lru_cache(None)
    def normalized(row, head, col):
        total = tree(row, head, col // 4, 5)
        mean = binop("div", total, literal(128))
        scale = node("un", "rsqrt", binop("add", mean, literal("0.00001")))
        x = load(1, row * 6144 + head * 128 + col)
        w = load(2 if head < 32 else 3, col)
        return binop("mul", x, binop("mul", scale, w))

    values = []
    for row in range(rows):
        for head in range(40):
            for col in range(128):
                if layout == "interleaved":
                    j = col // 2
                    x, y = normalized(row, head, j * 2), normalized(row, head, j * 2 + 1)
                    c, s = load(4, row * 128 + j), load(4, row * 128 + j + 64)
                    value = (binop("add", binop("mul", x, s), binop("mul", y, c)) if col % 2 else
                             binop("sub", binop("mul", x, c), binop("mul", y, s)))
                else:
                    j = col % 64
                    own = normalized(row, head, col)
                    peer = normalized(row, head, col ^ 64)
                    if col < 64:
                        peer = binop("sub", literal(0), peer)
                    c, s = load(4, row * 128 + j), load(4, row * 128 + j + 64)
                    value = binop("add", binop("mul", own, c), binop("mul", peer, s))
                values.append(node("un", "toHalf", value))
    return values


def expression_graph(values):
    """Lossless canonical DAG, avoiding repeated expansion of reduction trees."""
    seen, interned, vertices = {}, {}, []

    def visit(value):
        if id(value) in seen:
            return seen[id(value)]
        args = tuple(("ref", visit(a)) if isinstance(a, Node) else ("value", a) for a in value.args)
        key = value.op, args
        if key not in interned:
            interned[key] = len(vertices)
            vertices.append([value.op, *[["ref", a] if kind == "ref" else a for kind, a in args]])
        seen[id(value)] = interned[key]
        return interned[key]

    roots = [visit(value) for value in values]
    return (json.dumps({"schema": 1, "format": "postorder-IR-DAG", "vertices": vertices, "outputs": roots},
                       separators=(",", ":")) + "\n").encode()


def check(case, rows, *, source=None):
    raw = json.loads((case / "task.json").read_text())
    raw["launch"]["grid"] = rows * 5
    for b in raw["buffers"]:
        if len(b["shape"]) > 1:
            b["shape"][0] = rows
    contract = native.parse_task(json.dumps(raw))
    native.check_reference((case / "reference.py").read_text(), contract.rotary_layout)
    source = source if source is not None else (case / "kernel.hip").read_text()
    tr = native.translate(source, contract)
    machine = native.AccessPreflight(contract, tr).run()
    writes = set()
    for access in machine.trace:
        buffer = access.location[2]
        epoch = 0 if contract.rotary_layout == "interleaved" or buffer in (1, 2, 3) else 2 if buffer == 0 else 1
        if access.epoch != (0, 0, epoch):
            raise ValueError("Native synchronization epoch differs")
        if access.write:
            if access.location in writes:
                raise ValueError("Output written more than once")
            writes.add(access.location)
    expected_accesses = rows * (20480 if contract.rotary_layout == "interleaved" else 25600)
    if len(machine.trace) != expected_accesses or len(writes) != rows * 5120:
        raise ValueError("Incomplete native fused traversal")
    actual = machine.outputs()
    wanted = expected_values(contract.rotary_layout, rows)
    if actual != wanted:
        raise ValueError("Fused output differs from independent source-order tree and rotation")
    for bi, b in enumerate(contract.task.buffers):
        if b.role == "input" and any(machine.memory[("global", 0, bi, i)] != node("input", bi, i) for i in range(b.size)):
            raise ValueError("Read-only source buffer changed")
    if any(t.pc != len(tr.program) - 1 for t in machine.threads):
        raise ValueError("Incomplete native halt")
    trace = (json.dumps([[a.thread, list(a.location), a.write, list(a.epoch)] for a in machine.trace],
                        separators=(",", ":")) + "\n").encode()
    graph = expression_graph(actual)
    return {"layout": contract.rotary_layout, "rows": rows, "outputs": len(actual),
            "instructions": len(tr.program), "accesses": len(machine.trace), "unique_writes": len(writes),
            "halt_pc": len(tr.program) - 1, "all_actual_accesses_classified": True,
            "all_input_buffers_unchanged": True, "finite_trace_race_free": True,
            "trace_sha256": hashlib.sha256(trace).hexdigest(), "output_graph_sha256": hashlib.sha256(graph).hexdigest()}, trace, graph


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    results, controls = [], []
    for layout in native.LAYOUTS:
        case = HERE / "cases" / layout
        for rows in (1, 3):
            result, trace, graph = check(case, rows)
            name = f"{layout}-{rows}"
            (out / (name + "-trace.json.gz")).write_bytes(gzip.compress(trace, mtime=0))
            (out / (name + "-outputs-dag.json.gz")).write_bytes(gzip.compress(graph, mtime=0))
            results.append(result)
        source = (case / "kernel.hip").read_text()
        changes = {
            "wrong-reduction-mask": ("peer = __shfl_xor(ss, 16, 32);", "peer = __shfl_xor(ss, 8, 32);"),
            "wrong-logical-width": ("peer = __shfl_xor(ss, 16, 32);", "peer = __shfl_xor(ss, 16, 16);"),
            "wrong-weight-buffer": ("weight0 = __half2float(k_weight[w0]);", "weight0 = __half2float(q_weight[w0]);"),
            "missing-normalization": ("float n0 = x0 * scaledWeight0;", "float n0 = x0;"),
            "wrong-cache-half": ("int sa0 = ca0 + 64;", "int sa0 = ca0 + 63;"),
            "missing-output": ("  output[out3] = __float2half(o3);\n", ""),
        }
        if layout == "split-half":
            changes["wrong-rotation-peer"] = ("float p0 = __shfl_xor(n0, 16, 32);", "float p0 = __shfl_xor(n0, 8, 32);")
            changes["missing-negation"] = ("p0 = -p0;", "p0 = p0;")
        else:
            changes["wrong-rotation-sign"] = ("float o0 = xc0 - ys0;", "float o0 = xc0 + ys0;")
        for name, (before, after) in changes.items():
            if source.count(before) != 1:
                raise ValueError("Ambiguous source control: " + name)
            try:
                check(case, 1, source=source.replace(before, after))
            except (ValueError, native.Refusal) as error:
                controls.append({"layout": layout, "name": name, "accepted": False, "reason": str(error)})
            else:
                raise ValueError("Changed source accepted: " + name)
    report = {"schema": 1, "status": "finite-native-fused-qknorm-rope-source-values-and-traces-checked",
              "cases": results, "false_sources_rejected": controls, "complete_native_launch_theorem": False,
              "dense_reference_equivalence_proved": False, "source_certificates": 0, "model_calls": 0,
              "gpu_trials": 0, "original_paper_fully_reproduced": False}
    (out / "results.json").write_text(json.dumps(report, indent=2) + "\n")
    (out / "manifest.json").write_text(json.dumps({p.name: hashlib.sha256(p.read_bytes()).hexdigest()
                                                 for p in sorted(out.iterdir()) if p.is_file()}, indent=2) + "\n")
    print(json.dumps({"status": report["status"], "outputs": sum(c["outputs"] for c in results),
                      "accesses": sum(c["accesses"] for c in results), "false_sources": len(controls)}))


if __name__ == "__main__":
    main()
