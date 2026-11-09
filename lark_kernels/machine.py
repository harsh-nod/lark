"""Untrusted symbolic preflight and located diagnostics. Lean alone certifies."""

from __future__ import annotations

from dataclasses import dataclass, field

from .frontend import Translation
from .ir import Node, Refusal, Task, node


@dataclass(frozen=True)
class Access:
    thread: int
    location: tuple[str, int, int, int]
    write: bool
    epoch: tuple[int, int, int]


@dataclass
class Thread:
    pc: int = 0
    indices: dict[int, int] = field(default_factory=dict)
    regs: dict[int, Node] = field(default_factory=dict)
    epoch: list[int] = field(default_factory=lambda: [0, 0, 0])


class Machine:
    def __init__(self, task: Task, translation: Translation):
        self.task, self.translation = task, translation
        self.threads = [Thread() for _ in range(task.grid * task.block)]
        self.memory: dict[tuple, Node] = {}
        self.trace: list[Access] = []
        for b, buf in enumerate(task.buffers):
            if buf.role == "input":
                for i in range(buf.size):
                    self.memory[("global", 0, b, i)] = node("input", b, i)

    def ix(self, t: int, n: Node) -> int:
        op, a = n.op, n.args
        if op == "const":
            return a[0]
        if op == "tid":
            return t % self.task.block
        if op == "bid":
            return t // self.task.block
        if op == "bdim":
            return self.task.block
        if op == "ivar":
            if a[0] not in self.threads[t].indices:
                raise Refusal("uninitialized", f"thread {t}: index register {a[0]}")
            return self.threads[t].indices[a[0]]
        x, y = self.ix(t, a[0]), self.ix(t, a[1])
        if op in {"div", "mod"} and (y <= 0 or x < 0):
            raise Refusal("arithmetic", f"thread {t}: negative division operand or zero divisor")
        if op in {"lt", "le", "eq", "ne"}:
            return {"lt": x < y, "le": x <= y, "eq": x == y, "ne": x != y}[op]
        v = {
            "add": lambda: x + y,
            "sub": lambda: x - y,
            "mul": lambda: x * y,
            "div": lambda: x // y,
            "mod": lambda: x % y,
        }[op]()
        # Hardware signed overflow is outside this frontend's accepted profile.
        if not 0 <= v < 2**31:
            raise Refusal(
                "integer-overflow", f"thread {t}: {v} leaves the nonnegative int32 profile"
            )
        return v

    def location(self, t, space, b, ix, write=False):
        i = self.ix(t, ix)
        if space == "global":
            owner, size = 0, self.task.buffers[b].size
            if write and self.task.buffers[b].role == "input":
                raise Refusal("signature", f"write to input buffer {b}")
        else:
            owner, size = t // self.task.block, self.translation.shared[b][1]
        if not 0 <= i < size:
            raise Refusal("bounds", f"thread {t}: {space} buffer {b} offset {i}, size {size}")
        return space, owner, b, i

    def access(self, t, loc, write):
        self.trace.append(Access(t, loc, write, tuple(self.threads[t].epoch)))

    def expr(self, t: int, n: Node):
        op, a = n.op, n.args
        if op == "lit":
            return n
        if op == "reg":
            if a[0] not in self.threads[t].regs:
                raise Refusal("uninitialized", f"thread {t}: scalar register {a[0]}")
            return self.threads[t].regs[a[0]]
        if op == "bin":
            return node("bin", a[0], self.expr(t, a[1]), self.expr(t, a[2]))
        if op == "un":
            return node("un", a[0], self.expr(t, a[1]))
        if op == "load":
            loc = self.location(t, *a)
            if loc not in self.memory:
                raise Refusal("uninitialized", f"thread {t}: load from {loc}")
            self.access(t, loc, False)
            return self.memory[loc]
        raise Refusal("internal", f"bad expression {op}")

    def cut(self, t):
        pc = self.threads[t].pc
        if not 0 <= pc < len(self.translation.program):
            raise Refusal("control", f"thread {t}: invalid program counter {pc}")
        i = self.translation.program[pc]
        return "halt" if i.op == "halt" else i.args[0] if i.op == "barrier" else None

    def lane(self, t):
        thread = self.threads[t]
        for _ in range(self.task.fuel[0]):
            if self.cut(t):
                return
            i = self.translation.program[thread.pc]
            op, a = i.op, i.args
            pc = thread.pc + 1
            if op == "idx":
                thread.indices[a[0]] = self.ix(t, a[1])
            elif op == "set":
                thread.regs[a[0]] = self.expr(t, a[1])
            elif op == "store":
                loc = self.location(t, a[0], a[1], a[2], True)
                value = self.expr(t, a[3])
                self.access(t, loc, True)
                self.memory[loc] = value
            elif op == "branch":
                if not self.ix(t, a[0]):
                    pc = a[1]
            elif op == "jump":
                pc = a[0]
            else:
                raise Refusal("internal", f"bad instruction {op}")
            thread.pc = pc
        raise Refusal("fuel", f"thread {t}: lane fuel exhausted")

    def converged(self, ts):
        pcs = {self.threads[t].pc for t in ts}
        if len(pcs) != 1:
            raise Refusal(
                "convergence", f"threads {ts} park at different program counters {sorted(pcs)}"
            )
        return self.cut(ts[0])

    def resume(self, ts, cut):
        level = {"grid": 0, "block": 1, "warp": 2}[cut]
        for t in ts:
            self.threads[t].pc += 1
            self.threads[t].epoch[level] += 1

    def warp(self, ts):
        for _ in range(self.task.fuel[1]):
            for t in ts:
                self.lane(t)
            c = self.converged(ts)
            if c != "warp":
                return
            self.resume(ts, c)
        raise Refusal("fuel", "warp fuel exhausted")

    def block(self, b):
        ts = list(range(b * self.task.block, (b + 1) * self.task.block))
        for _ in range(self.task.fuel[2]):
            for w in range(0, len(ts), self.task.warp):
                self.warp(ts[w : w + self.task.warp])
            c = self.converged(ts)
            if c in {"halt", "grid"}:
                return
            if c != "block":
                raise Refusal("convergence", "invalid block cut")
            self.resume(ts, c)
        raise Refusal("fuel", "block fuel exhausted")

    def race(self):
        for i, a in enumerate(self.trace):
            for b in self.trace[i + 1 :]:
                if a.thread == b.thread or a.location != b.location or not (a.write or b.write):
                    continue
                if a.epoch[0] != b.epoch[0]:
                    continue
                if a.thread // self.task.block == b.thread // self.task.block:
                    if a.epoch[1] != b.epoch[1]:
                        continue
                    if (a.thread % self.task.block) // self.task.warp == (
                        b.thread % self.task.block
                    ) // self.task.warp:
                        if a.epoch[2] != b.epoch[2]:
                            continue
                return a, b
        return None

    def run(self):
        for _ in range(self.task.fuel[3]):
            for b in range(self.task.grid):
                self.block(b)
            ts = list(range(len(self.threads)))
            c = self.converged(ts)
            if c == "halt":
                return self
            if c != "grid":
                raise Refusal("convergence", "invalid grid cut")
            self.resume(ts, c)
        raise Refusal("fuel", "grid fuel exhausted")

    def outputs(self):
        out = []
        for id, b in enumerate(self.task.buffers):
            if b.role == "output":
                for i in range(b.size):
                    loc = ("global", 0, id, i)
                    if loc not in self.memory:
                        raise Refusal(
                            "uninitialized-output", f"output {b.name}[{i}] was not written"
                        )
                    out.append(self.memory[loc])
        return out


def preflight(task, translation, spec):
    m = Machine(task, translation).run()
    race = m.race()
    if race:
        a, b = race
        raise Refusal(
            "race",
            f"threads {a.thread} ({'write' if a.write else 'read'}) and "
            f"{b.thread} ({'write' if b.write else 'read'}) conflict at {a.location}",
        )
    if m.outputs() != spec:
        raise Refusal(
            "equivalence", "symbolic output differs from reference; no certificate issued"
        )
    return m
