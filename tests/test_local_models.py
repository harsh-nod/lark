import http.server
import argparse
import contextlib
import io
import json
import os
from pathlib import Path
import shutil
import tempfile
import threading
import unittest
import urllib.error

from reproduction.local_models import client

LEAN = os.environ.get("LARK_LEAN") or shutil.which("lean")


class LocalClientTests(unittest.TestCase):
    def test_remote_urls_credentials_and_unexpected_paths_are_refused(self):
        for url in [
            "https://api.openai.com/v1/chat/completions",
            "http://127.0.0.1.example.com/v1/chat/completions",
            "http://user:secret@127.0.0.1/v1/chat/completions",
            "http://127.0.0.1/v1/chat/completions?target=cloud",
            "http://127.0.0.1/other",
        ]:
            with self.subTest(url=url), self.assertRaises(ValueError):
                client.endpoint(url)

    def test_json_proposals_have_only_the_two_fixed_fields(self):
        expected = {"segments": [], "proofs": {}}
        self.assertEqual(client.proposal("```json\n" + json.dumps(expected) + "\n```"), expected)
        for data in [[], {"segments": []}, {**expected, "new_statement": "True"}]:
            with self.subTest(data=data), self.assertRaises(ValueError):
                client.proposal(json.dumps(data))

    def test_local_request_and_usage_are_recorded_and_redirects_are_refused(self):
        class Handler(http.server.BaseHTTPRequestHandler):
            redirect = False

            def do_POST(self):
                request = json.loads(self.rfile.read(int(self.headers["Content-Length"])))
                if self.redirect:
                    self.send_response(302)
                    self.send_header("Location", "https://example.com/v1/chat/completions")
                    self.end_headers()
                    return
                self.send_response(200)
                self.end_headers()
                self.wfile.write(
                    json.dumps(
                        {
                            "model": request["model"],
                            "usage": {"prompt_tokens": 2, "completion_tokens": 3},
                            "choices": [{"finish_reason": "stop", "message": {"content": "{}"}}],
                        }
                    ).encode()
                )

            def log_message(self, *args):
                pass

        server = http.server.HTTPServer(("127.0.0.1", 0), Handler)
        thread = threading.Thread(target=server.serve_forever, daemon=True)
        thread.start()
        try:
            with tempfile.TemporaryDirectory() as tmp:
                url = f"http://127.0.0.1:{server.server_port}/v1/chat/completions"
                target = Path(tmp) / "success"
                self.assertEqual(client.call(url, "zai-org/GLM-5.3-Flash", [], target), "{}")
                record = json.loads((target / "receipt.json").read_text())
                self.assertEqual(record["usage"]["completion_tokens"], 3)
                self.assertEqual(record["external_api_spend_usd"], 0)
                Handler.redirect = True
                with self.assertRaises(urllib.error.HTTPError):
                    client.call(url, "zai-org/GLM-5.3-Flash", [], Path(tmp) / "redirect")
                rejected = json.loads((Path(tmp) / "redirect/receipt.json").read_text())
                self.assertEqual(rejected["status"], "error")
        finally:
            server.shutdown()
            server.server_close()
            thread.join()

    @unittest.skipUnless(LEAN, "Lean is needed")
    def test_stub_proposal_gets_an_independently_checked_certificate(self):
        from lark_kernels.certificate import DEFAULT_PROOFS
        from reproduction.local_models.run import ROOT, run_case

        class Handler(http.server.BaseHTTPRequestHandler):
            def do_POST(self):
                request = json.loads(self.rfile.read(int(self.headers["Content-Length"])))
                prompt = json.loads(request["messages"][-1]["content"])
                candidate = {"segments": prompt["proposal"]["segments"], "proofs": DEFAULT_PROOFS}
                response = {
                    "model": request["model"],
                    "usage": {},
                    "choices": [
                        {"finish_reason": "stop", "message": {"content": json.dumps(candidate)}}
                    ],
                }
                self.send_response(200)
                self.end_headers()
                self.wfile.write(json.dumps(response).encode())

            def log_message(self, *args):
                pass

        server = http.server.HTTPServer(("127.0.0.1", 0), Handler)
        thread = threading.Thread(target=server.serve_forever, daemon=True)
        thread.start()
        try:
            with tempfile.TemporaryDirectory() as tmp, contextlib.redirect_stdout(io.StringIO()):
                args = argparse.Namespace(
                    lean=LEAN,
                    attempts=1,
                    model="zai-org/GLM-5.3-Flash",
                    seed=0,
                    temperature=0,
                    max_tokens=100,
                    model_timeout=10,
                    lean_timeout=120,
                    url=f"http://127.0.0.1:{server.server_port}/v1/chat/completions",
                )
                result = run_case(
                    ROOT / "reproduction/nonlinear/cases/float16/relu",
                    Path(tmp) / "case",
                    args,
                    {"revision": "unit-test-stub-not-a-model-run"},
                )
                self.assertEqual(result["status"], "verified")
                self.assertTrue((Path(tmp) / "case/certificate/report.json").exists())
        finally:
            server.shutdown()
            server.server_close()
            thread.join()


if __name__ == "__main__":
    unittest.main()
