import json
from pathlib import Path
import shutil
import subprocess
import unittest

from lark_kernels import collective, native_rmsnorm, partition_collective
from lark_kernels.ir import Refusal, Task, node

ROOT = Path(__file__).resolve().parents[1]


def task(block=64, half=False):
    dtype = "float16" if half else "float32"
    return Task.parse(
        json.dumps(
            {
                "name": "partition",
                "language": "hip",
                "entry": "partition",
                "buffers": [
                    {"name": "input", "role": "input", "dtype": dtype, "shape": [block]},
                    {"name": "output", "role": "output", "dtype": dtype, "shape": [block]},
                ],
                "launch": {"grid": 1, "block": block, "warp": 64},
                "fuel": [32, 8, 1, 1],
            }
        )
    )


def kernel(body, half=False):
    scalar = "__half" if half else "float"
    load = "__half2float(input[lane])" if half else "input[lane]"
    store = "__float2half(x)" if half else "x"
    return f"""extern "C" __global__ void partition(const {scalar}* input, {scalar}* output) {{
  int lane = threadIdx.x;
  float x = {load};
  {body}
  output[lane] = {store};
}}
"""


class PartitionMachineTests(unittest.TestCase):
    def test_native_contract_keeps_default_bounded_capacity(self):
        raw = (ROOT / "reproduction/production_rmsnorm/cases/weighted_16384/task.json").read_text()
        with self.assertRaises(Refusal):
            Task.parse(raw)
        parsed = native_rmsnorm.parse_task(raw)
        self.assertEqual((parsed.grid, parsed.block, parsed.buffers[0].size), (1, 1024, 16384))

    def test_native_contract_rejects_launch_and_boolean_aliases(self):
        raw = json.loads(
            (ROOT / "reproduction/production_rmsnorm/cases/weighted_16384/task.json").read_text()
        )
        for key in ("grid", "block", "boolean", "shape", "fuel"):
            data = json.loads(json.dumps(raw))
            if key == "grid":
                data["launch"]["grid"] = 2
            elif key == "block":
                data["launch"]["block"] = 256
            elif key == "boolean":
                data["launch"]["grid"] = True
            elif key == "shape":
                data["buffers"][0]["shape"][0] = True
            else:
                data["fuel"][3] = True
            with self.subTest(change=key), self.assertRaises(Refusal):
                native_rmsnorm.parse_task(json.dumps(data))

    def test_partial_partition_snapshot_and_inactive_lanes(self):
        source = kernel("if (lane < 16) { x = __shfl_up(x, 1, 16); }")
        t = task()
        tr = partition_collective.translate(source, t)
        m = partition_collective.Machine(t, tr).run()
        expected = [node("input", 0, max(0, i - 1) if i < 16 else i) for i in range(64)]
        self.assertEqual(m.outputs(), expected)
        self.assertIsNone(m.race())
        self.assertEqual(len(m.trace), 128)
        self.assertTrue(all(th.epoch == [0, 0, 0] for th in m.threads))
        # The old pinned profile still refuses the divergent physical wave.
        with self.assertRaises(Refusal):
            collective.Machine(t, tr).run()

    def test_two_distinct_logical_partitions_at_different_instructions(self):
        source = kernel("""if (lane < 16) { x = __shfl_up(x, 1, 16); }
  if (lane >= 16) { if (lane < 32) { x = __shfl(x, 0, 16); } }""")
        t = task()
        m = partition_collective.Machine(t, partition_collective.translate(source, t)).run()
        expected = [
            node("input", 0, max(0, i - 1) if i < 16 else 16 if i < 32 else i) for i in range(64)
        ]
        self.assertEqual(m.outputs(), expected)
        self.assertEqual(len(m.trace), 128)

    def test_existing_uniform_wave_has_identical_state_and_trace(self):
        source = kernel("x = __shfl_xor(x, 1, 64);")
        t = task()
        tr = collective.translate(source, t)
        old = collective.Machine(t, tr).run()
        new = partition_collective.Machine(t, tr).run()
        self.assertEqual(new.outputs(), old.outputs())
        self.assertEqual(new.trace, old.trace)
        self.assertEqual([th.epoch for th in new.threads], [th.epoch for th in old.threads])

    def test_explicit_half_storage_conversions_are_retained(self):
        source = kernel("if (lane < 16) { x = __shfl_up(x, 1, 16); }", half=True)
        t = task(half=True)
        m = partition_collective.Machine(t, partition_collective.translate(source, t)).run()
        expected = [
            node(
                "un",
                "toHalf",
                node("un", "fromHalf", node("input", 0, max(0, i - 1) if i < 16 else i)),
            )
            for i in range(64)
        ]
        self.assertEqual(m.outputs(), expected)

    def test_incomplete_partitions_are_refused(self):
        for body in (
            "if (lane < 15) { x = __shfl_up(x, 1, 16); }",
            "if (lane < 16) { x = __shfl_up(x, 1, 64); }",
        ):
            t = task()
            with self.subTest(body=body), self.assertRaises(Refusal):
                partition_collective.Machine(
                    t, partition_collective.translate(kernel(body), t)
                ).run()

    def test_duplicate_and_cross_wave_cohorts_are_refused(self):
        t = task(block=128)
        source = kernel("if (lane < 16) { x = __shfl_up(x, 1, 16); }")
        m = partition_collective.Machine(t, partition_collective.translate(source, t))
        for i in range(128):
            m.lane(i)
        with self.assertRaises(Refusal):
            m.shuffle(list(range(16)) * 2)
        for i in range(64, 80):
            m.threads[i].pc = m.threads[0].pc
        with self.assertRaises(Refusal):
            m.shuffle(list(range(16)) + list(range(64, 80)))

    def test_failed_gather_performs_no_partial_register_or_pc_updates(self):
        t = task()
        source = kernel("if (lane < 16) { x = __shfl_up(x, 1, 16); }")
        m = partition_collective.Machine(t, partition_collective.translate(source, t))
        for i in range(64):
            m.lane(i)
        m.threads[5].regs.pop(0)
        before = [(th.pc, dict(th.regs), list(th.epoch)) for th in m.threads]
        trace = list(m.trace)
        with self.assertRaises(Refusal):
            m.shuffle(list(range(16)))
        self.assertEqual(before, [(th.pc, dict(th.regs), list(th.epoch)) for th in m.threads])
        self.assertEqual(trace, m.trace)


@unittest.skipUnless(shutil.which("lean") and shutil.which("lake"), "Lean 4.19.0 required")
class PartitionLeanTests(unittest.TestCase):
    def test_lean_symbolic_cohort_and_guard_checks(self):
        built = subprocess.run(
            ["lake", "build", "+Lark.PartitionCollective", "+Lark.ReductionFootprint"],
            cwd=ROOT / "lean",
            capture_output=True,
            text=True,
            timeout=120,
        )
        self.assertEqual(built.returncode, 0, built.stdout + built.stderr)
        for name in ("PartitionChecks.lean", "ReductionFootprintChecks.lean"):
            checked = subprocess.run(
                ["lake", "env", "lean", str(ROOT / "tests/lean" / name)],
                cwd=ROOT / "lean",
                capture_output=True,
                text=True,
                timeout=120,
            )
            self.assertEqual(checked.returncode, 0, checked.stdout + checked.stderr)
            self.assertNotIn("sorryAx", checked.stdout + checked.stderr)
            self.assertNotIn("error:", checked.stdout + checked.stderr)


if __name__ == "__main__":
    unittest.main()
