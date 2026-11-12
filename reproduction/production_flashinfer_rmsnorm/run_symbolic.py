"""Execute finite native traces against an independently indexed expression DAG.

Interned shallow tuples compare exact expression structure without expanding
the reduction DAG at every output. This is untrusted finite Python evidence,
not a universal theorem or a certificate. No input source is executed as Python.
"""

import argparse
from dataclasses import asdict
import gzip
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from lark_kernels import native_flashinfer_rmsnorm as native, partition_collective
from lark_kernels.ir import Refusal

HERE = Path(__file__).resolve().parent


class Arena:
    def __init__(self):
        self.nodes, self.lookup = [], {}

    def add(self, *key):
        if key not in self.lookup:
            self.lookup[key] = len(self.nodes)
            self.nodes.append(key)
        return self.lookup[key]


class Machine(partition_collective.Machine):
    def __init__(self, task, translation):
        super().__init__(task, translation)
        self.arena = Arena()
        self.memory = {loc: self.arena.add(value.op, *value.args)
                       for loc, value in self.memory.items()}

    def expr(self, t, n):
        op, a = n.op, n.args
        if op == "lit":
            return self.arena.add(op, *a)
        if op == "reg":
            if a[0] not in self.threads[t].regs:
                raise Refusal("uninitialized", f"thread {t}: register {a[0]}")
            return self.threads[t].regs[a[0]]
        if op == "bin":
            return self.arena.add(op, a[0], self.expr(t, a[1]), self.expr(t, a[2]))
        if op == "un":
            return self.arena.add(op, a[0], self.expr(t, a[1]))
        if op == "load":
            loc = self.location(t, *a)
            if loc not in self.memory:
                raise Refusal("uninitialized", f"thread {t}: load {loc}")
            self.access(t, loc, False)
            return self.memory[loc]
        raise Refusal("internal", f"unknown expression {op}")

    def access(self, t, loc, write):
        space, owner, b, offset = loc
        epoch = self.threads[t].epoch
        lane, row = t % 1024, t // 1024
        good = False
        if epoch[0] == epoch[2] == 0:
            if space == "global" and owner == 0:
                if b == 0:
                    r, col = divmod(offset, native.WIDTH)
                    good = (write and epoch[1] == 2 and r == row
                            and (col // 8) % 1024 == lane)
                elif b == 1:
                    good = not write and epoch[1] in (0, 2)
                elif b == 2:
                    good = not write and epoch[1] == 2
            elif space == "shared" and owner == row and b == 0:
                good = (
                    (epoch[1] == 0 and write and lane % 32 == 0 and offset == lane // 32)
                    or (epoch[1] == 1 and not write and lane < 32 and offset == lane)
                    or (epoch[1] == 1 and write and lane == 0 and offset == 0)
                    or (epoch[1] == 2 and not write and offset == 0)
                )
        if not good:
            raise Refusal("finite-footprint", f"unexpected access {t, loc, write, tuple(epoch)}")
        super().access(t, loc, write)


def independent_outputs(arena, rows):
    add = lambda x, y: arena.add("bin", "add", x, y)
    mul = lambda x, y: arena.add("bin", "mul", x, y)
    zero = arena.add("lit", 0, 1)

    def from_half(b, i):
        return arena.add("un", "fromHalf", arena.add("input", b, i))

    def reduce32(values):
        for offset in (16, 8, 4, 2, 1):
            old = values
            values = [add(old[t], old[t // 32 * 32 + (t % 32 ^ offset)])
                      for t in range(len(old))]
        return values

    outputs = []
    for row in range(rows):
        sums = []
        for t in range(1024):
            acc = zero
            for iteration in range(2):
                for component in range(8):
                    col = (iteration * 1024 + t) * 8 + component
                    x = from_half(1, row * native.WIDTH + col)
                    acc = add(acc, mul(x, x))
            sums.append(acc)
        reduced = reduce32(sums)
        partials = [reduced[w * 32] for w in range(32)]
        total = reduce32(partials)[0]
        mean = arena.add("bin", "div", total, arena.add("lit", 16384, 1))
        scale = arena.add("un", "rsqrt", add(mean, arena.add("lit", 1, 100000)))
        for col in range(native.WIDTH):
            x = from_half(1, row * native.WIDTH + col)
            biased_weight = add(zero, from_half(2, col))
            outputs.append(arena.add("un", "toHalf", mul(mul(x, scale), biased_weight)))
    return outputs


def execute(source, task):
    tr = native.translate(source, task)
    machine = Machine(task, tr).run()
    expected = independent_outputs(machine.arena, task.grid)
    actual = [machine.memory.get(("global", 0, 0, i)) for i in range(len(expected))]
    if actual != expected:
        first = next(i for i, (a, b) in enumerate(zip(actual, expected)) if a != b)
        raise Refusal("finite-source-order", f"output {first} differs from independent expression")
    if any(t.pc != len(tr.program) - 1 or t.epoch != [0, 2, 0] for t in machine.threads):
        raise Refusal("finite-halt", "unexpected halt or barrier epochs")
    if len(machine.trace) != task.grid * 66625:
        raise Refusal("finite-trace", "unexpected complete trace length")
    for b in (1, 2):
        for i in range(task.buffers[b].size):
            if machine.memory[("global", 0, b, i)] != machine.arena.add("input", b, i):
                raise Refusal("finite-readonly", "input or weight changed")
    return machine, tr, actual


def compressed(path, value):
    data = (json.dumps(value, separators=(",", ":")) + "\n").encode()
    path.write_bytes(gzip.compress(data, mtime=0))
    return {"file": path.name, "uncompressed_bytes": len(data),
            "sha256": hashlib.sha256(path.read_bytes()).hexdigest()}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    case = HERE / "cases/native_16384"
    raw_task = json.loads((case / "task.json").read_text())
    source = (case / "kernel.hip").read_text()
    native.check_reference((case / "reference.py").read_text())
    checks = []
    for rows in (1, 3):
        data = json.loads(json.dumps(raw_task))
        data["buffers"][0]["shape"][0] = data["buffers"][1]["shape"][0] = rows
        data["launch"]["grid"] = rows
        task = native.parse_task(json.dumps(data))
        machine, tr, outputs = execute(source, task)
        directory = out / f"rows-{rows}"
        directory.mkdir()
        streams = [compressed(directory / "expressions.json.gz", machine.arena.nodes),
                   compressed(directory / "outputs.json.gz", outputs),
                   compressed(directory / "trace.json.gz", [asdict(a) for a in machine.trace])]
        checks.append({"rows": rows, "outputs": len(outputs), "accesses": len(machine.trace),
                       "expression_nodes": len(machine.arena.nodes), "instructions": len(tr.program),
                       "halt_pc": len(tr.program) - 1, "streams": streams})
        print(json.dumps(checks[-1]), flush=True)
    mutations = {
        "wrong-first-xor": source.replace("__shfl_xor(sum, 16, 32)", "__shfl_xor(sum, 8, 32)", 1),
        "missing-first-barrier": source.replace("__syncthreads();", "", 1),
        "unguarded-partial-store": source.replace("if (lane == 0) { partial[warp] = sum; }", "partial[warp] = sum;"),
        "aliased-output-store": source.replace("output[output_address]", "output[row * 16384]"),
        "wrong-weight-index": source.replace("weight[output_column]", "weight[0]"),
        "wrong-mean": source.replace("total / 16384.0f", "total / 8192.0f"),
        "wrong-epsilon": source.replace("0.00001f", "0.0001f"),
        "missing-weight-product": source.replace("__float2half(result)", "__float2half(normalized)"),
    }
    # Remove the last barrier explicitly, without touching its first occurrence.
    before, after = source.rsplit("__syncthreads();", 1)
    mutations["missing-second-barrier"] = before + after
    negatives = []
    task = native.parse_task(json.dumps(raw_task))
    for name, changed in mutations.items():
        if changed == source:
            raise ValueError("Mutation did not change source: " + name)
        try:
            execute(changed, task)
        except Refusal as error:
            if error.code not in {"finite-source-order", "finite-footprint", "uninitialized"}:
                raise
            (out / (name + ".log")).write_text(str(error) + "\n")
            (out / (name + ".hip")).write_text(changed)
            negatives.append({"name": name, "accepted": False, "code": error.code})
        else:
            raise ValueError("Changed source unexpectedly matched: " + name)
    result = {"schema": 1, "status": "finite-symbolic-native-flashinfer-rmsnorm-checked",
              "checks": checks, "negative_controls": negatives,
              "total_outputs": sum(c["outputs"] for c in checks),
              "total_accesses": sum(c["accesses"] for c in checks),
              "finite_source_order_expression_equality": True,
              "source_certificates": 0, "whole_kernel_execution_proved": False,
              "actual_trace_race_freedom_proved": False, "source_reference_equality_proved": False,
              "model_calls": 0, "gpu_trials": 0, "original_paper_fully_reproduced": False,
              "source_sha256": hashlib.sha256(source.encode()).hexdigest(),
              "runner_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    (out / "results.json").write_text(json.dumps(result, indent=2) + "\n")
    (out / "manifest.json").write_text(json.dumps({p.relative_to(out).as_posix():
        hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(out.rglob('*')) if p.is_file()}, indent=2) + "\n")
    print(json.dumps({"status": result["status"], "outputs": result["total_outputs"],
                      "accesses": result["total_accesses"], "negative_controls": len(negatives)}), flush=True)


if __name__ == "__main__":
    main()
