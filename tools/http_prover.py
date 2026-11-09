#!/usr/bin/env python3
"""Opt-in JSON proof provider for a chat-completions-compatible HTTP endpoint."""

import json
import os
import sys
import urllib.request


def main():
    endpoint = os.environ["LARK_PROVER_URL"]
    model = os.environ["LARK_PROVER_MODEL"]
    request = json.load(sys.stdin)
    body = {
        "model": model,
        "messages": [
            {
                "role": "system",
                "content": (
                    "Repair Lean 4 proof proposals for a GPU verifier. Return exactly one JSON object "
                    "with segments and proofs. Preserve the three proof slots in the supplied proposal. "
                    "Do not add assumptions, declarations, sorry, admit, native_decide, or metaprogramming. "
                    "The theorem statements and model are immutable. Segments must flatten to the full program."
                ),
            },
            {"role": "user", "content": json.dumps(request)},
        ],
        "temperature": 0,
    }
    headers = {"Content-Type": "application/json"}
    if os.environ.get("LARK_PROVER_API_KEY"):
        headers["Authorization"] = "Bearer " + os.environ["LARK_PROVER_API_KEY"]
    req = urllib.request.Request(endpoint, data=json.dumps(body).encode(), headers=headers)
    with urllib.request.urlopen(req, timeout=100) as response:
        text = json.load(response)["choices"][0]["message"]["content"].strip()
    if text.startswith("```"):
        text = text.split("\n", 1)[1].rsplit("```", 1)[0].strip()
    proposal = json.loads(text)
    json.dump(proposal, sys.stdout)


if __name__ == "__main__":
    main()
