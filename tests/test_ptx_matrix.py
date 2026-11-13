"""Actual compiled GEMM, complete proof/replay and coherently rehashed refusals."""

import copy
import json
import os
from pathlib import Path
import re
import shutil
import tarfile
import tempfile
import unittest

from lark_kernels import ptx_matrix as reader
from lark_kernels import ptx_matrix_certificate as checker
from lark_kernels.ir import Refusal

ROOT = Path(__file__).resolve().parents[1]
PACKET = ROOT / "reproduction/ptx/results/full-size-compilation-v1/raw.tar.gz"
LEAN = os.environ.get("LARK_LEAN") or shutil.which("lean")


def inputs():
    paths = ("cases/gemm/kernel/kernel.ptx", "cases/gemm/original/reference.py",
             "cases/gemm/original/task.json")
    with tarfile.open(PACKET) as archive:
        return {name: archive.extractfile(path).read()
                for name, path in zip(checker.INPUTS, paths, strict=True)}


def prepare(data):
    return reader.prepare_certificate(*(data[name].decode() for name in checker.INPUTS))


class PtxMatrixReaderTests(unittest.TestCase):
    def test_actual_full_size_source_branch_and_contract_are_preserved(self):
        data = inputs()
        task, translation, body = prepare(data)
        self.assertEqual(checker.sha(data["kernel.ptx"]),
                         "896f2337328f9bb0b62975117174405f0eab90560fe91c672beb31094e86c74c")
        self.assertEqual(translation.readback().encode(), data["kernel.ptx"])
        self.assertEqual(len(translation.instructions), 171)
        self.assertEqual(translation.labels, {"$L__BB0_1": 47})
        self.assertEqual(translation.instructions[164], ["branch", 1, 47])
        self.assertEqual(translation.instructions[47], ["addSigned64", 27, 47, ["reg", 19]])
        self.assertEqual(translation.instructions[-1], ["ret"])
        self.assertEqual([b.shape for b in task.buffers], [(64, 256), (256, 512), (64, 512)])
        self.assertTrue(all(b.dtype == "float16" for b in task.buffers))
        self.assertEqual((task.grid, task.block, task.warp), (32768, 1, 32))
        self.assertEqual(task.fuel, (1030, 1, 1, 1))
        self.assertIn("LarkPtxMatrix.Gemm.Correct ops program (spec ops)", reader.render(task, translation, body))

    def test_wrong_reference_operator_or_module_cannot_reach_the_fixed_specification(self):
        for altered in (b"import torch\ndef reference(a,b): return (a.float()+b.float()).half()\n",
                        b"import torch\ndef reference(a,b): return (b.float() @ a.float()).half()\n",
                        inputs()["reference.py"] + b"\nprint('side effect')\n"):
            with self.subTest(reference=altered), self.assertRaises(Refusal):
                prepare({**inputs(), "reference.py": altered})
        body = prepare(inputs())[2]
        body[1][1][1][1] = False
        with self.assertRaises(Refusal):
            reader.lean_reference(body)

    def test_labels_trailing_code_and_physical_register_aliases_are_refused(self):
        source = inputs()["kernel.ptx"]
        changes = (
            source.replace(b"$L__BB0_1;", b"$L__missing;"),
            source.replace(b"$L__BB0_1:", b"$L__BB0_1:\n$L__BB0_1:"),
            source + b"\n.visible .entry hidden() { ret; }\n",
            source.replace(b"%rd17", b"%rd017"),
            source.replace(b".reg .b64", b".reg .b32"),
        )
        for altered in changes:
            with self.subTest(source=altered[-100:]), self.assertRaises(Refusal):
                prepare({**inputs(), "kernel.ptx": altered})

    def test_comments_are_data_and_source_changes_reach_the_formal_program(self):
        data = inputs()
        data["kernel.ptx"] = b"// sorry; native_decide; set_option maxHeartbeats 0\n" + data["kernel.ptx"]
        prepared = prepare(data)
        self.assertEqual(prepared[1].readback().encode(), data["kernel.ptx"])
        self.assertNotIn("sorry", reader.render(*prepared))
        changed = {**data, "kernel.ptx": data["kernel.ptx"].replace(b"mul.rn.f32", b"add.rn.f32", 1)}
        self.assertNotEqual(prepare(changed)[1].instructions, prepared[1].instructions)
        self.assertNotEqual(reader.render(*prepare(changed)), reader.render(*prepared))

    def test_constructor_injection_boolean_and_zero_denominator_are_refused(self):
        for instruction in (["ret\naxiom h : False"], ["blockId", True], ["branch", 1, False],
                            ["addSigned32", 6, 6, ["imm", True]],
                            ["addSigned64", 17, 17, ["imm", 2**63]],
                            ["literalFloat", 68, 0, 0],
                            ["binaryFloat", 36, "mul\nsorry", 4, 5]):
            with self.subTest(instruction=instruction), self.assertRaises(Refusal):
                reader.lean_instruction(instruction)

    def test_shapes_geometry_and_cuda_fuel_are_not_changed_for_ptx(self):
        for field, value in (("fuel", [1031, 1, 1, 1]),
                             ("launch", {"grid": 32768, "block": 2, "warp": 32}),
                             ("launch", {"grid": 32768, "block": 1, "warp": 64})):
            data = inputs()
            contract = json.loads(data["contract.json"])
            contract[field] = value
            with self.subTest(field=field, value=value), self.assertRaises(Refusal):
                prepare({**data, "contract.json": json.dumps(contract).encode()})
        data = inputs()
        contract = json.loads(data["contract.json"])
        contract["buffers"][0]["shape"][0] = 32
        contract["buffers"][2]["shape"][0] = 32
        contract["launch"]["grid"] = 16384
        with self.assertRaises(Refusal):
            prepare({**data, "contract.json": json.dumps(contract).encode()})


@unittest.skipUnless(LEAN, "Lean4.19.0 is needed")
class PtxMatrixProofTests(unittest.TestCase):
    def test_full_size_export_fresh_replay_lean_refusal_and_rehashed_tampering(self):
        with tempfile.TemporaryDirectory(prefix="lark-ptx-matrix-proof-") as temporary:
            root = Path(temporary)
            recording, replay = root / "recording", root / "replay"
            first = checker.export_bytes(inputs(), recording, LEAN)
            self.assertEqual(first["status"], "verified-source-bound-full-PTX-GEMM")
            self.assertEqual(first["owned_Lean_modules_freshly_compiled"], 5)
            self.assertEqual(first["source_bound_development_proofs"], 1)
            self.assertEqual(len(first["axiom_audits"]), 6)
            self.assertEqual(len(first["library_axiom_audits"]), 169)
            result = checker.check_export(recording, replay, LEAN)
            self.assertEqual(result["status"], "fresh-source-only-PTX-GEMM-proof-replay-passed")
            self.assertEqual(result["owned_modules_freshly_compiled"], 5)
            self.assertFalse(result["old_owned_olean_cache_used"])
            self.assertEqual((recording / "Main.lean").read_bytes(), (replay / "Main.lean").read_bytes())
            checker.check_inventory(replay)

            altered = inputs()
            altered["kernel.ptx"] = altered["kernel.ptx"].replace(b"mul.rn.f32", b"add.rn.f32", 1)
            negative = root / "wrong-product"
            negative.mkdir()
            main = reader.render(*prepare(altered))
            (negative / "Main.lean").write_text(main)
            lean, _ = checker.toolchain(LEAN)
            check, log = checker.run_lean(lean, ["Main.lean"], negative,
                dict(os.environ, LEAN_PATH=str(recording / "modules")), negative / "Main.log")
            line = next(i+1 for i, text in enumerate(main.splitlines()) if text.startswith("theorem source_program "))
            self.assertNotEqual(check["exit_code"], 0)
            self.assertFalse(check["timed_out"])
            self.assertIn(str(line), re.findall(r"Main\.lean:([0-9]+):[0-9]+: error:", log))
            self.assertNotIn("Stack overflow", log)
            self.assertNotIn("maximum number of heartbeats", log)

            pristine = {p.relative_to(recording): p.read_bytes() for p in recording.rglob("*") if p.is_file()}

            def restore():
                for path, content in pristine.items():
                    (recording / path).write_bytes(content)

            def refuse(name, mutate):
                restore()
                report = checker.read(recording / "results.json")
                mutate(report)
                checker.write(recording / "results.json", report)
                checker.manifest(recording)
                destination = root / ("refused-" + name)
                with self.subTest(tampering=name), self.assertRaises(Refusal):
                    checker.check_export(recording, destination, LEAN)
                self.assertFalse(destination.exists())

            for name, fields in [
                ("boolean-proof-count", {"source_bound_development_proofs": True}),
                ("old-owned-cache", {"old_owned_olean_cache_used": True}),
                ("nvidia-overclaim", {"nvidia_execution": True}),
                ("changed-proof-budget", {"limits": {**checker.LIMITS, "maxHeartbeats": 4000000}}),
                ("boolean-CUDA-fuel", {"unchanged_CUDA_contract_fuel": [1030, True, 1, 1]}),
                ("boolean-launch", {"launch": {"grid": 32768, "block": True, "warp": 32}}),
            ]:
                refuse(name, lambda report, fields=copy.deepcopy(fields): report.update(fields))

            def altered_reference(report):
                body = checker.read(recording / "reference-ast.json")
                body[1][1][1][1] = False
                checker.write(recording / "reference-ast.json", body)
                report["reference_ast_sha256"] = checker.sha((recording / "reference-ast.json").read_bytes())
            refuse("rehashed-reference-index", altered_reference)

            def altered_main(report):
                p = recording / "Main.lean"
                p.write_text(p.read_text().replace("by decide", "by sorry", 1))
                report["main_sha256"] = checker.sha(p.read_bytes())
            refuse("rehashed-proof-body", altered_main)

            def captured_python(report):
                name = "python/ptx_matrix_certificate.py"
                p = recording / "owned-sources" / name
                p.write_text(p.read_text() + "\nraise AssertionError('captured Python executed')\n")
                bindings = checker.read(recording / "source-bindings.json")
                bindings[name] = checker.sha(p.read_bytes())
                checker.write(recording / "source-bindings.json", bindings)
                report["source_bindings_sha256"] = checker.sha((recording / "source-bindings.json").read_bytes())
            refuse("rehashed-captured-Python", captured_python)

            def forbidden_axiom(report):
                p = recording / "Main.log"
                p.write_text(p.read_text().replace("Classical.choice", "sorryAx", 1))
                report["main_check"]["log_sha256"] = checker.sha(p.read_bytes())
                report["axiom_audits"]["LarkPtxMatrixCertificate.launch"] = ["propext", "sorryAx", "Quot.sound"]
            refuse("rehashed-forbidden-axiom", forbidden_axiom)
            restore()


if __name__ == "__main__":
    unittest.main()
