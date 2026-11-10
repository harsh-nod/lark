"""Poll the owned loopback service and record readiness without making model calls."""

import argparse
from datetime import datetime, timezone
import json
from pathlib import Path
import subprocess
import time
import urllib.request

if __package__:
    from .client import NoRedirect, endpoint
else:
    from client import NoRedirect, endpoint


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--server", required=True, type=Path)
    p.add_argument("--timeout", type=float, default=3600)
    args = p.parse_args()
    record = json.loads(args.server.read_text())
    endpoint(record["endpoint"])
    base = record["endpoint"].removesuffix("/v1/chat/completions")
    opener = urllib.request.build_opener(urllib.request.ProxyHandler({}), NoRedirect())
    started = time.monotonic()
    last = "not checked"
    while time.monotonic() - started < args.timeout:
        inspect = json.loads(
            subprocess.check_output(
                ["docker", "inspect", record["container_name"]],
                text=True,
                timeout=10,
            )
        )[0]
        if inspect["Config"]["Image"] != record["image"] or not inspect["State"]["Running"]:
            raise RuntimeError("Owned model container stopped or differs from the pinned image")
        try:
            with opener.open(base + "/health", timeout=10) as response:
                if response.status != 200:
                    raise RuntimeError("Non-200 health status")
            with opener.open(base + "/v1/models", timeout=10) as response:
                models = json.load(response)
            if record["model"] not in {m["id"] for m in models["data"]}:
                raise RuntimeError("The endpoint serves a different model family")
        except Exception as error:
            last = str(error)
            print(last, flush=True)
            time.sleep(10)
            continue
        record.update(
            status="ready",
            ready_utc=datetime.now(timezone.utc).isoformat(),
            readiness_seconds=time.monotonic() - started,
            api_models=models,
            container_id=inspect["Id"],
        )
        args.server.write_text(json.dumps(record, indent=2) + "\n")
        print("READY: " + record["endpoint"])
        return
    raise RuntimeError("Model readiness timed out: " + last)


if __name__ == "__main__":
    main()
