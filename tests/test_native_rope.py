"""Native mutable RoPE contracts, exact finite traversal and refusals."""

import copy
import json
from pathlib import Path
import unittest

from lark_kernels import native_rope as native
from lark_kernels.ir import Refusal
from reproduction.production_rope import run_symbolic

CASES = Path(__file__).resolve().parents[1] / "reproduction/production_rope/cases"


class NativeRopeTests(unittest.TestCase):
    def raw(self, layout="interleaved"):
        return json.loads((CASES / layout / "task.json").read_text())

    def test_complete_native_q_and_k_values_for_both_layouts(self):
        for layout in native.LAYOUTS:
            with self.subTest(layout=layout):
                result, _, _ = run_symbolic.check(CASES / layout, 1)
                self.assertEqual(result["outputs"], 5120)
                self.assertEqual(result["accesses"], 15360)
                self.assertEqual(result["unique_writes"], 5120)
                self.assertEqual(result["all_threads_halt_pc"], 49)

    def test_native_pair_inputs_are_read_before_either_store(self):
        for layout in native.LAYOUTS:
            case = CASES / layout
            contract = native.parse_task((case / "task.json").read_text())
            machine = native.AccessPreflight(contract, native.translate((case / "kernel.hip").read_text(), contract)).run()
            per_thread = [[] for _ in range(512)]
            for a in machine.trace:
                per_thread[a.thread].append(a)
            for events in per_thread:
                self.assertEqual(len(events), 30)
                for start in range(0, 30, 6):
                    c, s, x, y, ox, oy = events[start:start + 6]
                    self.assertEqual([a.write for a in (c, s, x, y, ox, oy)], [False] * 4 + [True] * 2)
                    self.assertEqual(c.location[2], 2)
                    self.assertEqual(s.location[2], 2)
                    self.assertEqual(x.location, ox.location)
                    self.assertEqual(y.location, oy.location)
                    self.assertNotEqual(x.location, y.location)

    def test_mutable_initialization_is_required(self):
        case = CASES / "interleaved"
        contract = native.parse_task((case / "task.json").read_text())
        tr = native.translate((case / "kernel.hip").read_text(), contract)
        with self.assertRaisesRegex(Refusal, "uninitialized"):
            native.collective.Machine(contract.task, tr).run()

    def test_aliasing_pairs_are_rejected_by_actual_access_check(self):
        case = CASES / "interleaved"
        source = (case / "kernel.hip").read_text().replace("int qx = 2 * qr;", "int qx = 0;")
        with self.assertRaisesRegex(Refusal, "footprint"):
            run_symbolic.check(case, 1, source=source)

    def test_arithmetic_change_rejected_by_independent_output_formula(self):
        case = CASES / "split-half"
        source = (case / "kernel.hip").read_text().replace("float qoy = qyc + qxs;", "float qoy = qyc - qxs;")
        with self.assertRaisesRegex(ValueError, "independent source-order"):
            run_symbolic.check(case, 1, source=source)

    def test_native_parameter_bounds_without_allocating_symbolic_inputs(self):
        raw = self.raw()
        for rows in (1, 3, 256, 65535):
            raw["launch"]["grid"] = rows
            for b in raw["buffers"]:
                b["shape"][0] = rows
            task = native.parse_task(json.dumps(raw)).task
            self.assertEqual(task.grid, rows)
            self.assertLess(task.buffers[0].size, 2**31)

    def test_wrong_signature_geometry_types_and_unknown_fields_refused(self):
        changes = [
            lambda d: d.update(unchecked_aliases=True),
            lambda d: d.update(rotary_layout="unknown"),
            lambda d: d["launch"].update(block=1),
            lambda d: d["launch"].update(grid=True),
            lambda d: d["launch"].update(warp=32),
            lambda d: d["fuel"].__setitem__(1, True),
            lambda d: d["buffers"][0]["shape"].__setitem__(0, True),
            lambda d: d["buffers"][1].update(role="input"),
            lambda d: d["buffers"][1].update(name="query"),
            lambda d: d["buffers"][2].update(dtype="float32"),
            lambda d: d["buffers"][2]["shape"].__setitem__(1, 64),
            lambda d: d["buffers"][0]["shape"].__setitem__(0, 65536),
        ]
        for change in changes:
            raw = self.raw()
            change(raw)
            with self.subTest(raw=raw), self.assertRaises(Refusal):
                native.parse_task(json.dumps(raw))

    def test_reference_branch_and_cache_operand_changes_refused(self):
        for layout in native.LAYOUTS:
            baseline = native.canonical_reference(layout)
            for changed in (baseline.replace("y * c + x * s", "y * c - x * s"),
                            baseline.replace("return rotate(query, cache), rotate(key, cache)",
                                             "return rotate(query, cache), key")):
                with self.subTest(layout=layout), self.assertRaisesRegex(Refusal, "reference"):
                    native.check_reference(changed, layout)


if __name__ == "__main__":
    unittest.main()
