"""Development model for complete logical partitions inside native wave64.

This module is groundwork for native RMSNorm. It is not a registered
certificate profile and does not certify a kernel by running Python.
"""

from . import collective
from .ir import Refusal


def translate(source, task):
    if task.language != "hip" or task.warp != 64 or task.block % 64:
        raise Refusal("partition-geometry", "native wave64 blocks are required")
    result = collective.Reader(source, task).read()
    if result.readback() != source:
        raise Refusal("readback", "partition source does not reconstruct byte for byte")
    return result


def native_base(task, thread):
    return thread // task.block * task.block + (thread % task.block // 64) * 64


def complete_partitions(task, threads, width):
    members = set(threads)
    for thread in threads:
        base = native_base(task, thread) + (thread % task.block % 64 // width) * width
        if any(base + lane not in members for lane in range(width)):
            return False
    return True


class Machine(collective.Machine):
    def shuffle(self, threads):
        if (
            self.task.warp != 64
            or self.task.block % 64
            or not threads
            or len(threads) != len(set(threads))
            or len(threads) > 64
        ):
            raise Refusal("partition-geometry", "nonempty distinct native-wave cohort required")
        first = threads[0]
        if any(
            self.threads[t].pc != self.threads[first].pc
            or native_base(self.task, t) != native_base(self.task, first)
            for t in threads
        ):
            raise Refusal("partition-cohort", "cohort must share a native wave and instruction")
        instruction = self.translation.program[self.threads[first].pc]
        if instruction.op != "shuffle":
            raise Refusal("partition-cohort", "cohort is not at a shuffle")
        kind, dest, src, selector, width = instruction.args
        if width not in collective.WIDTHS or not complete_partitions(self.task, threads, width):
            raise Refusal("partition-incomplete", "cohort omits a logical-partition lane")
        values = []
        for thread in threads:
            selected = collective.source_lane(
                kind, width, thread % self.task.block % 64, self.ix(thread, selector)
            )
            peer = native_base(self.task, thread) + selected
            if peer not in threads or src not in self.threads[peer].regs:
                raise Refusal("shuffle-uninitialized", "shuffle source lane/register unavailable")
            values.append((thread, self.threads[peer].regs[src]))
        # All reads complete before any register or PC update.
        for thread, value in values:
            self.threads[thread].regs[dest] = value
            self.threads[thread].pc += 1

    def warp(self, threads):
        for _ in range(self.task.fuel[1]):
            for thread in threads:
                self.lane(thread)
            active = [t for t in threads if self.cut(t) == "shuffle"]
            if active:
                pc = self.threads[active[0]].pc
                cohort = [t for t in threads if self.threads[t].pc == pc]
                self.shuffle(cohort)
            else:
                cut = self.converged(threads)
                if cut == "warp":
                    self.resume(threads, cut)
                else:
                    return
        raise Refusal("fuel", "partition warp fuel exhausted")
