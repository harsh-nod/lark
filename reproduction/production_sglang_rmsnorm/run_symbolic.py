"""Finite complete original/repaired SGLang executions with literal DAGs.

The complete caches, pair grouping, shared inverse slots and original conflicting
stores are retained. This is finite Python evidence, not a source certificate.
"""

import argparse
from collections import defaultdict
from dataclasses import asdict
import gzip
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from lark_kernels import native_sglang_rmsnorm as native
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


class Machine(native.Machine):
    def __init__(self, task, translation, guarded):
        super().__init__(task, translation)
        self.guarded = guarded
        self.arena = Arena()
        self.memory = {loc: self.arena.add(value.op, *value.args)
                       for loc, value in self.memory.items()}

    def expr(self, t, n):
        op, args = n.op, n.args
        if op == "lit":
            return self.arena.add(op, *args)
        if op == "reg":
            if args[0] not in self.threads[t].regs:
                raise Refusal("uninitialized", "scalar register unavailable")
            return self.threads[t].regs[args[0]]
        if op == "bin":
            return self.arena.add(op, args[0], self.expr(t, args[1]), self.expr(t, args[2]))
        if op == "un":
            return self.arena.add(op, args[0], self.expr(t, args[1]))
        if op == "load":
            location = self.location(t, *args)
            if location not in self.memory:
                raise Refusal("uninitialized", "memory cell unavailable")
            self.access(t, location, False)
            return self.memory[location]
        raise Refusal("internal", "unknown expression " + op)

    def access(self, t, location, write):
        space, owner, buffer, offset = location
        grid_epoch, block_epoch, warp_epoch = self.threads[t].epoch
        row, tid = divmod(t, 1024)
        good = False
        if grid_epoch == warp_epoch == 0:
            if space == "global" and owner == 0:
                if buffer == 0:
                    output_row, col = divmod(offset, native.WIDTH)
                    good = (write and block_epoch == 2 and output_row == row
                            and col // 8 % 1024 == tid)
                elif buffer in (1, 2):
                    good = not write and block_epoch == 0
            elif space == "local" and owner == t:
                if buffer == 0:
                    good = block_epoch == 0 or (block_epoch == 2 and not write)
                elif buffer == 1:
                    good = (block_epoch == 0 and write) or (block_epoch == 2 and not write)
                elif buffer == 2:
                    good = block_epoch == 2
            elif space == "shared" and owner == row and buffer == 0:
                good = (
                    (block_epoch == 0 and write and offset == tid // 32
                     and (not self.guarded or tid % 32 == 0))
                    or (block_epoch == 1 and tid < 32 and offset == tid)
                    or (block_epoch == 2 and not write and offset == tid // 32)
                )
        if not good:
            raise Refusal("finite-footprint", str((t, location, write, tuple(self.threads[t].epoch))))
        super().access(t, location, write)


def independent_outputs(arena, rows, guarded):
    add = lambda x, y: arena.add("bin", "add", x, y)
    mul = lambda x, y: arena.add("bin", "mul", x, y)
    zero = arena.add("lit", 0, 1)

    def half_input(buffer, index):
        return arena.add("un", "fromHalf", arena.add("input", buffer, index))

    def reduce32(values):
        for mask in (16, 8, 4, 2, 1):
            old = values
            values = [add(old[lane], old[lane // 32 * 32 + (lane % 32 ^ mask)])
                      for lane in range(len(old))]
        return values

    outputs = []
    for row in range(rows):
        thread_sums = []
        for tid in range(1024):
            accumulator = zero
            for iteration in range(2):
                for pair in range(4):
                    col = (iteration * 1024 + tid) * 8 + 2 * pair
                    x = half_input(1, row * native.WIDTH + col)
                    y = half_input(1, row * native.WIDTH + col + 1)
                    accumulator = add(accumulator, add(mul(x, x), mul(y, y)))
            thread_sums.append(accumulator)
        reduced = reduce32(thread_sums)
        # The pinned sequential source model retains the final lane's original
        # unguarded write. This does not resolve the source's unordered WW race.
        writer_lane = 0 if guarded else 31
        partials = [reduced[32 * warp + writer_lane] for warp in range(32)]
        totals = reduce32(partials)
        inverses = [arena.add("un", "rsqrt", add(
            arena.add("bin", "div", total, arena.add("lit", native.WIDTH, 1)),
            arena.add("lit", 1, 100000))) for total in totals]
        for col in range(native.WIDTH):
            x = half_input(1, row * native.WIDTH + col)
            weight = half_input(2, col)
            warp = (col // 8 % 1024) // 32
            outputs.append(arena.add("un", "toHalf", mul(mul(x, inverses[warp]), weight)))
    return outputs


def conflicting_pairs(machine):
    buckets = defaultdict(list)
    for access in machine.trace:
        buckets[access.location].append(access)
    count, first = 0, None
    for accesses in buckets.values():
        if len({a.thread for a in accesses}) <= 1 or not any(a.write for a in accesses):
            continue
        for index, a in enumerate(accesses):
            for b in accesses[index + 1:]:
                if a.thread == b.thread or not (a.write or b.write) or a.epoch[0] != b.epoch[0]:
                    continue
                if a.thread // 1024 == b.thread // 1024:
                    if a.epoch[1] != b.epoch[1]:
                        continue
                    if (a.thread % 1024) // 64 == (b.thread % 1024) // 64 and a.epoch[2] != b.epoch[2]:
                        continue
                count += 1
                if first is None:
                    first = (a, b)
    return count, first


def execute(source, task, guarded):
    translation = native.translate(source, task)
    machine = Machine(task, translation, guarded).run()
    expected = independent_outputs(machine.arena, task.grid, guarded)
    outputs = [machine.memory.get(("global", 0, 0, i)) for i in range(len(expected))]
    if outputs != expected:
        raise Refusal("finite-source-order", "literal output DAG differs from independently indexed source operations")
    if any(t.pc != len(translation.program) - 1 or t.epoch != [0, 2, 0] for t in machine.threads):
        raise Refusal("finite-halt", "unexpected halt or synchronization epochs")
    expected_accesses = (164960 if guarded else 165952) * task.grid
    if len(machine.trace) != expected_accesses:
        raise Refusal("finite-trace", "unexpected access count " + str(len(machine.trace)))
    for buffer in (1, 2):
        for index in range(task.buffers[buffer].size):
            if machine.memory[("global", 0, buffer, index)] != machine.arena.add("input", buffer, index):
                raise Refusal("finite-readonly", "input or weight changed")
    count, first = conflicting_pairs(machine)
    if count != (0 if guarded else 15872 * task.grid):
        raise Refusal("finite-race", "unexpected conflicting-pair count " + str(count))
    return machine, translation, outputs, count, first


def compressed(path, value):
    blob = (json.dumps(value, separators=(",", ":")) + "\n").encode()
    path.write_bytes(gzip.compress(blob, mtime=0))
    return {"file": path.name, "uncompressed_bytes": len(blob),
            "sha256": hashlib.sha256(path.read_bytes()).hexdigest()}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    checks = []
    for variant, guarded in (("native_original", False), ("native_fixed", True)):
        case = HERE / "cases" / variant
        source = (case / "kernel.hip").read_text()
        native.check_reference((case / "reference.py").read_text())
        for rows in (1, 3):
            data = json.loads((case / "task.json").read_text())
            data["launch"]["grid"] = rows
            for buffer in data["buffers"][:2]:
                buffer["shape"][0] = rows
            task = native.parse_task(json.dumps(data))
            machine, translation, outputs, count, first = execute(source, task, guarded)
            directory = out / f"{variant}-rows-{rows}"
            directory.mkdir()
            streams = [compressed(directory / "expressions.json.gz", machine.arena.nodes),
                       compressed(directory / "outputs.json.gz", outputs),
                       compressed(directory / "trace.json.gz", [asdict(a) for a in machine.trace])]
            check = {"variant": variant, "rows": rows, "outputs": len(outputs),
                     "accesses": len(machine.trace), "expression_nodes": len(machine.arena.nodes),
                     "instructions": len(translation.program), "halt_pc": len(translation.program) - 1,
                     "conflicting_pairs": count,
                     "first_conflict": [asdict(a) for a in first] if first else None, "streams": streams}
            checks.append(check)
            print(json.dumps({k: v for k, v in check.items() if k != "streams"}), flush=True)
    result = {"schema": 1, "status": "finite-sglang-original-and-guarded-repair-source-checked",
              "checks": checks, "literal_source_order_outputs_compared": sum(c["outputs"] for c in checks),
              "accesses_checked": sum(c["accesses"] for c in checks), "source_certificates": 0,
              "whole_kernel_execution_proved": False, "source_reference_equality_proved": False,
              "original_paper_fully_reproduced": False, "model_calls": 0, "gpu_trials": 0}
    (out / "results.json").write_text(json.dumps(result, indent=2) + "\n")
    (out / "manifest.json").write_text(json.dumps({str(p.relative_to(out)): hashlib.sha256(p.read_bytes()).hexdigest()
        for p in sorted(out.rglob("*")) if p.is_file()}, indent=2) + "\n")
    print(json.dumps({k: v for k, v in result.items() if k != "checks"}), flush=True)


if __name__ == "__main__":
    main()
