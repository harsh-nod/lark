"""Actual full-size PTX source binding and constructor-boundary controls."""

import json
import os
from pathlib import Path
import shutil
import tarfile
import tempfile
import unittest

from lark_kernels import ptx_pointwise as reader
from lark_kernels import ptx_pointwise_certificate as checker
from lark_kernels.ir import Refusal

ROOT = Path(__file__).resolve().parents[1]
PACKET = ROOT / "reproduction/ptx/results/full-size-compilation-v1/raw.tar.gz"
LEAN = os.environ.get("LARK_LEAN") or shutil.which("lean")


def inputs():
    with tarfile.open(PACKET) as archive:
        paths = ("cases/relu/kernel/kernel.ptx", "cases/relu/original/reference.py",
                 "cases/relu/original/task.json")
        return {name: archive.extractfile(path).read()
                for name, path in zip(checker.INPUTS, paths, strict=True)}


def prepare(data):
    return reader.prepare(*(data[name].decode() for name in checker.INPUTS))


class PtxPointwiseReaderTests(unittest.TestCase):
    def test_actual_full_size_source_and_contract_are_preserved(self):
        data = inputs()
        task, translation, _ = prepare(data)
        self.assertEqual(translation.readback().encode(), data["kernel.ptx"])
        self.assertEqual(len(translation.instructions), 15)
        self.assertEqual((task.grid, task.block, task.warp), (16384, 1, 32))
        self.assertEqual(task.fuel, (4, 1, 1, 1))
        self.assertTrue(all(b.dtype == "float16" for b in task.buffers))
        self.assertEqual(translation.instructions[6], ["addPointerS64", 6, 4, 5])
        self.assertEqual(translation.instructions[10], ["binary", 2, "max", 1, 3])

    def test_source_mutation_changes_the_actual_formal_program(self):
        data = inputs()
        before = prepare(data)[1]
        data["kernel.ptx"] = data["kernel.ptx"].replace(b"max.f32", b"add.rn.f32")
        after = prepare(data)[1]
        self.assertNotEqual(before.instructions, after.instructions)
        self.assertEqual(after.instructions[10], ["binary", 2, "add", 1, 3])
        self.assertNotEqual(before.lean_program(), after.lean_program())

    def test_comments_stay_data_and_trailing_declarations_are_refused(self):
        data = inputs()
        data["kernel.ptx"] = b"// set_option maxHeartbeats 0; sorry\n" + data["kernel.ptx"]
        args = prepare(data)
        self.assertEqual(args[1].readback().encode(), data["kernel.ptx"])
        self.assertNotIn("sorry", reader.render(*args))
        data["kernel.ptx"] += b"\n.visible .entry hidden() { ret; }\n"
        with self.assertRaisesRegex(Refusal, "trailing declarations"):
            prepare(data)

    def test_register_type_and_name_aliasing_are_refused(self):
        data = inputs()
        data["kernel.ptx"] = data["kernel.ptx"].replace(b".reg .b16", b".reg .b32")
        with self.assertRaisesRegex(Refusal, "prefix/type differs"):
            prepare(data)
        data = inputs()
        data["kernel.ptx"] = data["kernel.ptx"].replace(b"%rd7", b"%rd07")
        with self.assertRaisesRegex(Refusal, "undeclared"):
            prepare(data)

    def test_constructor_text_and_boolean_operands_cannot_enter_lean(self):
        for value in (["ret\nset_option maxHeartbeats 0"], ["blockId", True],
                      ["binary", 2, "max\naxiom h : False", 1, 3],
                      ["literal", 3, 0, 0], [["ret"]]):
            with self.subTest(value=value), self.assertRaises(Refusal):
                reader.lean_instruction(value)

    def test_geometry_and_fuel_are_not_weakened_for_ptx(self):
        for key, value in (("launch", {"grid": 16384, "block": 2, "warp": 32}),
                           ("fuel", [1000, 1, 1, 1])):
            data = inputs()
            task = json.loads(data["contract.json"])
            task[key] = value
            data["contract.json"] = json.dumps(task).encode()
            with self.subTest(key=key), self.assertRaises(Refusal):
                prepare(data)


@unittest.skipUnless(LEAN, "Lean4.19.0 is needed")
class PtxPointwiseProofTests(unittest.TestCase):
    def test_full_size_source_bound_export_and_fresh_source_only_replay(self):
        with tempfile.TemporaryDirectory(prefix="lark-ptx-pointwise-proof-") as temporary:
            root = Path(temporary)
            recording, replay = root / "recording", root / "replay"
            first = checker.export_bytes(inputs(), recording, LEAN)
            self.assertEqual(first["status"], "verified-source-bound-finite-PTX")
            self.assertEqual(first["elements"], 16384)
            self.assertEqual(len(first["axiom_audits"]), 6)
            self.assertEqual(len(first["library_axiom_audits"]), 22)
            result = checker.check_export(recording, replay, LEAN)
            self.assertEqual(result["status"], "fresh-source-only-PTX-proof-replay-passed")
            self.assertTrue(result["main_regenerated_identically"])
            self.assertEqual(result["owned_modules_freshly_compiled"], 3)
            self.assertFalse(result["old_owned_olean_cache_used"])
            self.assertEqual((recording / "Main.lean").read_bytes(), (replay / "Main.lean").read_bytes())
            self.assertEqual(result["fresh_export_manifest_sha256"],
                             checker.sha((replay / "proof-export-manifest.json").read_bytes()))
            checker.check_inventory(replay)

            altered = inputs()
            altered["kernel.ptx"] = altered["kernel.ptx"].replace(b"max.f32", b"add.rn.f32")
            negative = root / "wrong-arithmetic"
            negative.mkdir()
            (negative / "Main.lean").write_text(reader.render(*prepare(altered)))
            environment = os.environ.copy()
            environment["LEAN_PATH"] = str(recording / "modules")
            actual_lean, _ = checker.toolchain(LEAN)
            check, log = checker.run_lean(actual_lean, ["Main.lean"], negative, environment,
                                           negative / "Main.log")
            self.assertNotEqual(check["exit_code"], 0)
            self.assertFalse(check["timed_out"])
            self.assertIn("error:", log)
            self.assertIn("LarkPtxCertificate.source_program", log)
            self.assertNotIn("maximum recursion", log)
            self.assertNotIn("maximum number of heartbeats", log)

            report = checker.read(recording / "results.json")
            report["elements"] = 16385
            checker.write(recording / "results.json", report)
            checker.manifest(recording)
            refused = root / "must-not-be-created"
            with self.assertRaisesRegex(Refusal, "task/program scope differs"):
                checker.check_export(recording, refused, LEAN)
            self.assertFalse(refused.exists())


if __name__ == "__main__":
    unittest.main()
