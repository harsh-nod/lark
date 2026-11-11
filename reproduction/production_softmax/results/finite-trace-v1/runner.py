"""Replay every access of the complete native softmax sources, erasing values.

Control depends only on integer indices. This is finite source-execution and
trace evidence, not a universal Lean execution or numerical correctness theorem.
"""

import argparse
from collections import Counter
from dataclasses import asdict
import gzip
import hashlib
import json
from pathlib import Path
import shutil
import sys
import time

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from lark_kernels import native_softmax as native  # noqa: E402
from lark_kernels.ir import Refusal  # noqa: E402
from lark_kernels.machine import Access  # noqa: E402
from reproduction.production_softmax.prepare import source  # noqa: E402

HERE = Path(__file__).resolve().parent


def ordered(task, a, b):
    if a.epoch[0] != b.epoch[0]:
        return True
    if a.thread // task.block == b.thread // task.block:
        if a.epoch[1] != b.epoch[1]:
            return True
        if a.thread % task.block // 64 == b.thread % task.block // 64:
            return a.epoch[2] != b.epoch[2]
    return False


def good(a):
    space, owner, buffer, offset = a.location
    t, epoch = a.thread, a.epoch[1]
    if space == "local":
        return owner == t
    if space == "global":
        if buffer == 1:
            return owner == 0 and not a.write
        row, col = divmod(offset, native.WIDTH)
        return buffer == 0 and owner == 0 and t == row * native.BLOCK + col % native.BLOCK
    if space == "shared" and owner == t // native.BLOCK and buffer in (0, 1):
        tid = t % native.BLOCK
        return ((a.write and epoch == 2 * buffer and tid % 32 == 0 and offset == tid // 32)
                or (epoch == 2 * buffer + 1 and tid == 0 and (not a.write or offset == 0))
                or (epoch == 2 * buffer + 2 and not a.write and offset == 0))
    return False


class Replay(native.Machine):
    def __init__(self, task, translation, stream):
        super().__init__(task, translation)
        self.stream = stream
        self.events = 0
        self.counts = Counter()
        self.bad = 0
        self.first_race = None
        self.buckets = {}
        self.canonical = {}

    def expr(self, t, n):
        op, args = n.op, n.args
        if op == "bin":
            self.expr(t, args[1])
            self.expr(t, args[2])
        elif op == "un":
            self.expr(t, args[1])
        elif op != "lit":
            super().expr(t, n)  # Checks register/memory initialization and records loads.
        return 0

    def access(self, t, loc, write):
        a = Access(t, loc, write, tuple(self.threads[t].epoch))
        self.events += 1
        self.stream.write((json.dumps([self.events, t, list(loc), write, list(a.epoch), self.threads[t].pc],
                                      separators=(",", ":")) + "\n").encode())
        self.counts[f"{loc[0]}:{loc[2]}:{'write' if write else 'read'}:epoch{a.epoch[1]}"] += 1
        if not good(a):
            self.bad += 1
        if loc[0] != "local":
            readers, writers = self.buckets.setdefault(loc, ({}, {}))
            candidates = [*readers.values(), *writers.values()] if write else writers.values()
            if self.first_race is None:
                for b, index in candidates:
                    if a.thread != b.thread and not ordered(self.task, a, b):
                        self.first_race = {"earlier": index, "later": self.events,
                                           "earlier_access": asdict(b), "later_access": asdict(a)}
                        break
            (writers if write else readers).setdefault((t, a.epoch), (a, self.events))
        if loc == ("global", 0, 0, 50256) and a.epoch == (0, 4, 0):
            key = "reader" if t == 0 and not write else "writer" if t == 80 and write else None
            if key and key not in self.canonical:
                self.canonical[key] = {
                    "event": self.events, "access": asdict(a), "pc": self.threads[t].pc,
                    "indices": dict(self.threads[t].indices), "initialized_scalar_registers": sorted(self.threads[t].regs),
                }

    def outputs(self):
        raise Refusal("values-erased", "this replay records addresses, not scalar output values")

    def race(self):
        raise Refusal("finite-evidence", "use the explicitly scoped finite trace witness")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    out = args.output.resolve()
    if any((p / ".git").exists() for p in (out, *out.parents)):
        raise ValueError("Use a fresh output outside Git")
    out.mkdir(parents=True, exist_ok=False)
    records = []
    for name, guarded in (("native_race", False), ("native_fixed", True)):
        case = HERE / "cases" / name
        code = (case / "kernel.hip").read_text()
        assert code == source(guarded)
        task = native.parse_task((case / "task.json").read_text())
        tr = native.translate(code, task)
        trace = out / (name + "-trace.jsonl.gz")
        before = time.monotonic()
        with trace.open("wb") as raw:
            with gzip.GzipFile(fileobj=raw, mode="wb", mtime=0, filename="") as stream:
                replay = Replay(task, tr, stream)
                replay.run()
        assert all(t.pc == len(tr.program) - 1 and t.epoch == [0, 4, 0] for t in replay.threads)
        if guarded:
            assert replay.first_race is None and replay.bad == 0
        else:
            assert replay.first_race is not None and replay.bad > 0
            assert set(replay.canonical) == {"reader", "writer"}
        missing = sum(("global", 0, 0, i) not in replay.memory for i in range(native.WIDTH))
        assert missing == 0
        record = {
            "case": name, "seconds": time.monotonic() - before, "instructions": len(tr.program),
            "accesses": replay.events, "counts": dict(sorted(replay.counts.items())),
            "footprint_classification_failures": replay.bad, "all_threads_halted": True,
            "final_block_epoch": 4, "missing_output_cells": missing,
            "first_conflict": replay.first_race, "canonical_witness": replay.canonical,
            "source_sha256": hashlib.sha256(code.encode()).hexdigest(),
            "trace_file": trace.name, "trace_sha256": hashlib.sha256(trace.read_bytes()).hexdigest(),
        }
        (out / (name + "-translation.json")).write_text(json.dumps(tr.data(), indent=2) + "\n")
        (out / (name + ".json")).write_text(json.dumps(record, indent=2) + "\n")
        records.append(record)
        print(json.dumps({k: record[k] for k in ("case", "accesses", "footprint_classification_failures", "seconds")}), flush=True)
    result = {
        "schema": 1, "status": "full-native-softmax-finite-access-replay-checked", "rows": 1,
        "width": native.WIDTH, "block": native.BLOCK, "physical_warp": 64, "logical_warp": 32,
        "records": records, "source_certificates": 0, "whole_kernel_lean_execution_proved": False,
        "whole_kernel_universal_race_freedom_proved": False, "canonical_source_equivalence_proved": False,
        "scalar_values_evaluated": False, "gpu_trials": 0, "model_calls": 0,
        "original_paper_fully_reproduced": False,
        "scope": "Every address of both complete source variants is replayed at one50257-column row. Integer control, bounds, initialization, cuts and native shuffle cohorts are checked; scalar values are erased. The original conflicts, while the guarded repair's finite trace has no conflicting pair and every access satisfies its sufficient ownership/epoch classification. This is not a universal Lean whole-launch proof.",
    }
    (out / "results.json").write_text(json.dumps(result, indent=2) + "\n")
    shutil.copyfile(Path(__file__), out / "runner.py")
    (out / "manifest.json").write_text(json.dumps({p.name: hashlib.sha256(p.read_bytes()).hexdigest()
                                                   for p in sorted(out.iterdir()) if p.is_file()}, indent=2) + "\n")


if __name__ == "__main__":
    main()
