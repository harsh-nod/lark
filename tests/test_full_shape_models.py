import contextlib
import http.server
import io
import json
import os
from pathlib import Path, PurePosixPath
import shutil
import sys
import tarfile
import tempfile
import threading
import unittest
from types import SimpleNamespace
from unittest.mock import patch

from reproduction.local_models import full_shape, full_shape_run as run

ROOT = Path(__file__).resolve().parents[1]
LEAN = os.environ.get("LARK_LEAN") or shutil.which("lean")
PROJECT = os.environ.get("LARK_REAL_PROJECT")


class FullShapeProtocolTests(unittest.TestCase):
    def test_full_cohort_completion_requires_every_finished_case(self):
        expected = [case[0] for case in full_shape.benchmark.CASES]
        report = {"status": "in-progress", "selected_cases": expected, "cases": []}
        self.assertFalse(run.cohort_complete(report))
        report["cases"] = [{"case": name, "status": "budget-exhausted"} for name in expected]
        self.assertFalse(run.cohort_complete(report))
        report["status"] = "finished"
        self.assertTrue(run.cohort_complete(report))
        report["cases"][-1]["status"] = "runtime-uncertain"
        self.assertFalse(run.cohort_complete(report))
        report["cases"][-1] = {"case": expected[0], "status": "verified-proof"}
        self.assertFalse(run.cohort_complete(report))

    def test_source_reads_cannot_reach_controls_renderers_or_other_paths(self):
        libraries = {"Lark/Owned.lean": b"namespace Owned\ndef value := 1\nend Owned\n"}
        result = run.read_library(
            {"path": "Lark/Owned.lean", "start_line": 2, "line_count": 1}, libraries
        )
        self.assertEqual(result["text"], "2: def value := 1")
        for path in ("../sdk-positive/Main.lean", "/tmp/secret", "lark_kernels/certificate.py"):
            with self.subTest(path=path), self.assertRaises(ValueError):
                run.read_library({"path": path, "start_line": 1, "line_count": 1}, libraries)
        for start, count in ((True, 1), (0, 1), (1, 121), (1, True), (4, 1)):
            with self.subTest(start=start, count=count), self.assertRaises(ValueError):
                run.read_library(
                    {"path": "Lark/Owned.lean", "start_line": start, "line_count": count},
                    libraries,
                )

    def test_ambiguous_json_and_fourth_slot_executors_are_refused(self):
        with self.assertRaisesRegex(ValueError, "Duplicate"):
            run.parse_action('{"read_library":{},"read_library":{}}')
        proofs = {name: "by rfl" for name in full_shape.SLOTS}
        run.parse_action(json.dumps({"proofs": proofs}))
        for text in ("by sorry", 'by rfl\nrun_meta Lean.logInfo "unreachable"'):
            with self.subTest(text=text), self.assertRaises(ValueError):
                run.parse_action(json.dumps({"proofs": {**proofs, "segmentation": text}}))

    def test_context_compaction_preserves_the_entire_fixed_task(self):
        request = {"immutable_main": "full shape 16384", "proof_slots": list(full_shape.SLOTS)}
        args = SimpleNamespace(url="unused", model="unused", server={"max_model_len": 65536})
        excerpt = {"path": "Lark/Owned.lean", "start_line": 1, "end_line": 1, "text": "old hint"}
        with tempfile.TemporaryDirectory() as temporary:
            with patch.object(run, "tokenize", side_effect=[(60000, 65536), (100, 65536)]):
                messages, kept, changes = run.fit_messages(
                    args, request, {}, [excerpt], "feedback", "", {}, Path(temporary)
                )
        self.assertEqual(kept, [])
        self.assertEqual(len(changes), 1)
        state = json.loads(
            messages[1]["content"].split("\n", 1)[1].split("\nPrevious response", 1)[0]
        )
        self.assertEqual(state["fixed_task"], request)


@unittest.skipUnless(
    LEAN and PROJECT, "Lean and a configured source-checked import project are required"
)
class FullShapeStubIntegrationTests(unittest.TestCase):
    def test_library_read_syntax_refusal_and_two_real_proof_checks(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            prepared = root / "prepared"
            prepared.mkdir()
            archive = (
                ROOT
                / "reproduction/local_models/results/full-shape-preparation-v2/preparation.tar.gz"
            )
            with tarfile.open(archive) as bundle:
                for member in bundle:
                    name = PurePosixPath(member.name)
                    self.assertTrue(member.isfile())
                    self.assertFalse(name.is_absolute())
                    self.assertNotIn("..", name.parts)
                    destination = prepared / name
                    destination.parent.mkdir(parents=True, exist_ok=True)
                    destination.write_bytes(bundle.extractfile(member).read())
            run.verify_preparation(prepared)
            block = (prepared / "cases/relu/sdk-block.lean.txt").read_text()
            known = {n: s["sdk_positive_control"] for n, s in full_shape.proof_spans(block).items()}
            bad = {**known, "segmentation_data": known["segmentation_data"] + "\nopen Nat"}
            actions = [
                {"read_library": {"path": "Lark/Pointwise.lean", "start_line": 1, "line_count": 4}},
                {"proofs": bad},
                {"proofs": known},
            ]
            seen = []
            model = "zai-org/GLM-5.3-Flash"

            class Handler(http.server.BaseHTTPRequestHandler):
                tokenize_error = False

                def do_GET(self):
                    value = {"data": [{"id": model}]} if self.path == "/v1/models" else {}
                    self.send_response(200)
                    self.end_headers()
                    self.wfile.write(json.dumps(value).encode())

                def do_POST(self):
                    request = json.loads(self.rfile.read(int(self.headers["Content-Length"])))
                    if self.path == "/tokenize":
                        if Handler.tokenize_error:
                            self.send_error(503, "test tokenizer unavailable")
                            return
                        value = {"count": 100, "max_model_len": 65536, "tokens": [0] * 100}
                    else:
                        seen.append(request)
                        value = {
                            "model": model,
                            "usage": {
                                "prompt_tokens": 2,
                                "completion_tokens": 3,
                                "total_tokens": 5,
                            },
                            "choices": [
                                {
                                    "finish_reason": "stop",
                                    "message": {"content": json.dumps(actions[len(seen) - 1])},
                                }
                            ],
                        }
                    self.send_response(200)
                    self.end_headers()
                    self.wfile.write(json.dumps(value).encode())

                def log_message(self, *args):
                    pass

            server = http.server.HTTPServer(("127.0.0.1", 0), Handler)
            thread = threading.Thread(target=server.serve_forever, daemon=True)
            thread.start()
            try:
                url = f"http://127.0.0.1:{server.server_port}/v1/chat/completions"
                record = root / "server.json"
                record.write_text(
                    json.dumps(
                        {
                            "status": "ready",
                            "model": model,
                            "revision": "test-stub",
                            "endpoint": url,
                            "max_model_len": 65536,
                            "test_stub": True,
                        }
                    )
                )
                arguments = [
                    "full_shape_run.py",
                    "--prepared",
                    str(prepared),
                    "--lean",
                    str(LEAN),
                    "--server-record",
                    str(record),
                    "--url",
                    url,
                    "--model",
                    model,
                    "--output",
                    str(root / "run"),
                    "--case",
                    "relu",
                ]
                with (
                    patch.object(sys, "argv", arguments),
                    self.assertRaisesRegex(ValueError, "explicit test-only"),
                ):
                    run.main()
                self.assertEqual(seen, [])
                with (
                    patch.object(sys, "argv", arguments + ["--allow-test-stub"]),
                    contextlib.redirect_stdout(io.StringIO()),
                ):
                    run.main()
                report = json.loads((root / "run/results.json").read_text())
                self.assertEqual(report["status"], "finished")
                self.assertEqual(report["request_attempts"], 3)
                self.assertEqual(report["model_inference_calls"], 0)
                self.assertEqual(report["verified_model_proofs"], 0)
                self.assertTrue(report["test_stub"])
                case = report["cases"][0]
                self.assertEqual(case["library_reads"], 1)
                self.assertEqual(case["syntax_checks"], 2)
                self.assertEqual(case["proof_checks"], 1)
                self.assertEqual(
                    [c["status"] for c in case["calls"]],
                    ["library-read", "invalid-proposal", "verified-proof"],
                )
                fixed = json.loads((root / "run/cases/relu/fixed-request.json").read_text())
                self.assertTrue(
                    all(
                        s["sdk_positive_control"] == "by fail"
                        for s in full_shape.proof_spans(fixed["immutable_main"]).values()
                    )
                )
                first_state = json.loads(
                    seen[0]["messages"][1]["content"]
                    .split("\n", 1)[1]
                    .split("\nPrevious response", 1)[0]
                )
                self.assertEqual(first_state["fixed_task"], fixed)
                winner = root / "run/cases/relu/call-03"
                main = (winner / "proof-check/Main.lean").read_text()
                self.assertEqual(main, full_shape.render(block, known))
                self.assertEqual(main, (winner / "independent-recheck/Main.lean").read_text())
                Handler.tokenize_error = True
                failed_arguments = list(arguments)
                failed_arguments[failed_arguments.index("--output") + 1] = str(
                    root / "tokenizer-failure"
                )
                with (
                    patch.object(sys, "argv", failed_arguments + ["--allow-test-stub"]),
                    contextlib.redirect_stdout(io.StringIO()),
                    self.assertRaises(SystemExit),
                ):
                    run.main()
                failed = json.loads((root / "tokenizer-failure/results.json").read_text())
                self.assertEqual(failed["status"], "runtime-uncertain")
                self.assertEqual(failed["request_attempts"], 0)
                self.assertEqual(failed["model_inference_calls"], 0)
                self.assertEqual(failed["cases"][0]["calls"][0]["http_status"], 503)
                self.assertEqual(len(seen), 3)
                self.assertTrue(
                    (root / "tokenizer-failure/cases/relu/call-01/http-error-body.bin").is_file()
                )
            finally:
                server.shutdown()
                server.server_close()
                thread.join()
