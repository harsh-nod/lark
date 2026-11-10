"""Recorded, loopback-only model calls for the offline/free constraint."""

import hashlib
import json
from pathlib import Path
import time
import urllib.error
import urllib.parse
import urllib.request

MODELS = {
    "zai-org/GLM-5.3-Flash",
    "zai-org/GLM-5.3",
    "deepseek-ai/DeepSeek-V4.1-Flash-1017",
}


def endpoint(url):
    parsed = urllib.parse.urlsplit(url)
    if (
        parsed.scheme != "http"
        or parsed.hostname not in {"127.0.0.1", "localhost", "::1"}
        or parsed.username is not None
        or parsed.password is not None
        or parsed.path != "/v1/chat/completions"
        or parsed.query
        or parsed.fragment
    ):
        raise ValueError(
            "Only an explicit loopback HTTP chat endpoint is allowed; hosted APIs are refused"
        )
    return url


class NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, req, fp, code, msg, headers, newurl):
        raise urllib.error.HTTPError(req.full_url, code, "Redirects are refused", headers, fp)


def call(url, model, messages, output, *, seed=0, temperature=0, max_tokens=16384, timeout=600):
    endpoint(url)
    if model not in MODELS:
        raise ValueError("Only the original paper's named open-weight model families are allowed")
    output = Path(output)
    output.mkdir(parents=True, exist_ok=False)
    body = {
        "model": model,
        "messages": messages,
        "temperature": temperature,
        "max_tokens": max_tokens,
        "seed": seed,
        "stream": False,
    }
    if model.startswith("zai-org/"):
        body["reasoning_effort"] = "max"
    encoded = json.dumps(body, ensure_ascii=False).encode("utf-8")
    (output / "request.json").write_bytes(encoded)
    record = {
        "backend": "loopback-vllm",
        "endpoint": url,
        "model": model,
        "request_sha256": hashlib.sha256(encoded).hexdigest(),
        "external_api_spend_usd": 0,
    }
    started = time.monotonic()
    opener = urllib.request.build_opener(urllib.request.ProxyHandler({}), NoRedirect())
    request = urllib.request.Request(
        url, data=encoded, headers={"Content-Type": "application/json"}
    )
    try:
        with opener.open(request, timeout=timeout) as response:
            raw = response.read(64 * 1024 * 1024 + 1)
        if len(raw) > 64 * 1024 * 1024:
            raise ValueError("Oversized model response")
        (output / "response.json").write_bytes(raw)
        data = json.loads(raw)
        if data.get("model") != model:
            raise ValueError("The response model differs from the requested pinned family")
        record.update(
            status="received",
            usage=data.get("usage"),
            response_sha256=hashlib.sha256(raw).hexdigest(),
            finish_reason=data["choices"][0].get("finish_reason"),
        )
        content = data["choices"][0]["message"].get("content")
        if not isinstance(content, str) or not content.strip():
            raise ValueError("Model produced no proof content")
        return content
    except Exception as error:
        record.update(status="error", error=str(error))
        raise
    finally:
        record["elapsed_seconds"] = time.monotonic() - started
        (output / "receipt.json").write_text(json.dumps(record, indent=2) + "\n")


def proposal(content):
    content = content.strip()
    if content.startswith("```"):
        content = content.split("\n", 1)[1].rsplit("```", 1)[0].strip()
    value = json.loads(content)
    if not isinstance(value, dict) or set(value) != {"segments", "proofs"}:
        raise ValueError("Expected exactly the segments and proofs proposal fields")
    return value
