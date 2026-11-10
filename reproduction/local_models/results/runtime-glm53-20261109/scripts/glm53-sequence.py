"""Finish the authorized local model sequence; only exact owned container IDs may stop."""

from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import os
import subprocess
import sys
import tarfile
import time
import urllib.request

BASE = Path("/tmp/lark-local-models-20261109")
ROOT = Path("/dev/shm/lark-proof-controller-budget-20261109/source")
STATE = BASE / "glm53-sequence-state.json"
FLASH = "7753fabe6905c3fa242fe45c597f9545f770e38bbc8f4df69358ea1f7afd871e"
DEEP = "09808420b738afb3305e2f57f7c06546ea2ecc79e792698db1e68562e75b7bad"
RUNS = [
    "pilot-low-remote-8ad91bc",
    "glm-flash-budget4096-remote",
    "deepseek-budget4096-additional14-remote",
]
record = {
    "schema": 1,
    "status": "waiting",
    "runner_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    "events": [],
    "scope": "Authorized sequential free model experiments. Only completed owned runtimes stop; original readiness records remain historical evidence.",
}


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def save(status, **fields):
    record.update(status=status, **fields)
    record["events"].append(
        {"status": status, "utc": datetime.now(timezone.utc).isoformat()}
    )
    temp = STATE.with_suffix(".tmp")
    temp.write_text(json.dumps(record, indent=2) + "\n")
    temp.replace(STATE)
    print(json.dumps(record["events"][-1]), flush=True)


def load(path):
    try:
        return json.loads(path.read_text())
    except (FileNotFoundError, json.JSONDecodeError):
        return {}


def idle(endpoint):
    opener = urllib.request.build_opener(urllib.request.ProxyHandler({}))
    with opener.open(
        endpoint.removesuffix("/v1/chat/completions") + "/metrics", timeout=10
    ) as response:
        text = response.read().decode()
    values = {}
    for line in text.splitlines():
        if line.startswith("#") or not line.strip():
            continue
        for metric in ("vllm:num_requests_running", "vllm:num_requests_waiting"):
            if line.startswith(metric + "{") or line.startswith(metric + " "):
                values.setdefault(metric, []).append(float(line.rsplit(" ", 1)[1]))
    return len(values) == 2 and all(v == 0 for rows in values.values() for v in rows)


def inspect(cid):
    return json.loads(
        subprocess.check_output(["docker", "inspect", cid], text=True, timeout=20)
    )[0]


def owned_stop(cid, server):
    current = inspect(cid)
    assert current["Id"] == cid == server["container_id"]
    assert current["Config"]["Image"] == server["image"]
    if current["State"]["Running"]:
        assert idle(server["endpoint"]), "Owned endpoint has active or queued requests"
        subprocess.run(
            ["docker", "stop", "--time", "30", cid],
            check=True,
            capture_output=True,
            text=True,
            timeout=90,
        )
    return {
        "container_id": cid,
        "ready_record_sha256": sha(
            BASE / ("server.json" if cid == FLASH else "deepseek-server-v2.json")
        ),
        "stopped_utc": datetime.now(timezone.utc).isoformat(),
        "docker_state": inspect(cid)["State"],
    }


def archive_runs():
    out = BASE / "completed-model-pilots-before-glm53.tar.gz"
    assert not out.exists()
    with tarfile.open(out, "w:gz") as t:
        for name in RUNS:
            assert load(BASE / name / "results.json").get("status") == "finished"
            for p in (BASE / name).rglob("*"):
                if p.is_file():
                    t.add(p, arcname=str(p.relative_to(BASE)), recursive=False)
            for suffix in (".log", "-launch.json"):
                p = BASE / (name + suffix)
                t.add(p, arcname=p.name)
        for n in [
            "additional-cases-source.tar.gz",
            "budget-controller-source.tar.gz",
            "proof-source-8ad91bc.tar.gz",
            "remote-controller-runtime.json",
        ]:
            t.add(BASE / n, arcname=n)
    return sha(out)


def main():
    assert not STATE.exists()
    assert load(BASE / "glm53-validate.json").get("ready") is True
    assert load(BASE / "glm53-estimate.json").get("fit", {}).get("weights_fit") is True
    save("waiting")
    deadline = time.monotonic() + 7200
    flash, deep = load(BASE / "server.json"), load(BASE / "deepseek-server-v2.json")
    assert flash["container_id"] == FLASH and deep["container_id"] == DEEP
    while time.monotonic() < deadline:
        ready = (
            load(BASE / "glm53-checkpoint-verified.json").get("status")
            == "verified-download"
        )
        finished = all(
            load(BASE / n / "results.json").get("status") == "finished" for n in RUNS
        )
        if ready and finished:
            if idle(flash["endpoint"]) and idle(deep["endpoint"]):
                break
        time.sleep(20)
    else:
        raise RuntimeError("Preconditions timed out; no containers stopped")
    save("completed-pilots-archived", pilot_archive_sha256=archive_runs())
    stopped = [owned_stop(DEEP, deep), owned_stop(FLASH, flash)]
    save("completed-owned-runtimes-stopped", stopped=stopped)
    time.sleep(10)
    args = [
        "python3",
        str(BASE / "scripts/serve-glm53.py"),
        "--checkpoint",
        str(BASE / "glm53-checkpoint-verified.json"),
        "--cache",
        "/dev/shm/lark-models-20261109/hub",
        "--spillover",
        "/run/user/9661/lark-glm53-20261109/blobs",
        "--runtime-cache",
        "/dev/shm/lark-glm53-vllm-cache-20261109",
        "--output",
        str(BASE / "glm53-server.json"),
        "--launch",
    ]
    result = subprocess.run(args, capture_output=True, text=True, timeout=180)
    (BASE / "glm53-launch.log").write_text(result.stdout + result.stderr)
    if result.returncode:
        raise RuntimeError("Full GLM launcher failed: see glm53-launch.log")
    save(
        "glm53-started",
        launch_args=args,
        launch_script_sha256=sha(BASE / "scripts/serve-glm53.py"),
    )
    result = subprocess.run(
        [
            "python3",
            str(BASE / "scripts/ready.py"),
            "--server",
            str(BASE / "glm53-server.json"),
            "--timeout",
            "3600",
        ],
        capture_output=True,
        text=True,
        timeout=3630,
    )
    (BASE / "glm53-readiness.log").write_text(result.stdout + result.stderr)
    if result.returncode:
        raise RuntimeError("Full GLM readiness failed: see glm53-readiness.log")
    save("glm53-ready")
    sys.path.insert(0, str(ROOT))
    from reproduction.local_models import client

    answer = client.call(
        "http://127.0.0.1:19084/v1/chat/completions",
        "zai-org/GLM-5.3",
        [
            {
                "role": "user",
                "content": "Reply with exactly LARK_READY and no explanation.",
            }
        ],
        BASE / "glm53-warmup",
        max_tokens=256,
        thinking_token_budget=64,
        reasoning_effort="low",
        timeout=120,
    )
    assert answer.strip() == "LARK_READY", "Warmup acknowledgement mismatch"
    save("glm53-warmup-passed")
    name = "glm53-budget4096-remote"
    args = [
        "python3",
        "-m",
        "reproduction.local_models.run",
        "--url",
        "http://127.0.0.1:19084/v1/chat/completions",
        "--model",
        "zai-org/GLM-5.3",
        "--server-record",
        str(BASE / "glm53-server.json"),
        "--output",
        str(BASE / name),
        "--lean",
        "/dev/shm/lark-proof-controller-20261109/runtime/lean-4.19.0-linux/bin/lean",
        "--attempts",
        "3",
        "--max-tokens",
        "16384",
        "--thinking-token-budget",
        "4096",
        "--reasoning-effort",
        "low",
        "--model-timeout",
        "1800",
        "--lean-timeout",
        "150",
    ]
    for case in ("relu", "silu", "softmax"):
        args += ["--case", "reproduction/nonlinear/cases/float16/" + case]
    env = os.environ.copy()
    env["PYTHONDONTWRITEBYTECODE"] = "1"
    for key in ("LEAN_PATH", "LEAN_SRC_PATH"):
        env.pop(key, None)
    with (BASE / (name + ".log")).open("wb") as f:
        p = subprocess.Popen(
            args,
            cwd=ROOT,
            env=env,
            stdin=subprocess.DEVNULL,
            stdout=f,
            stderr=subprocess.STDOUT,
        )
        (BASE / (name + "-launch.json")).write_text(
            json.dumps(
                {
                    "pid": p.pid,
                    "args": args,
                    "cwd": str(ROOT),
                    "source_bundle_sha256": sha(
                        BASE / "budget-controller-source.tar.gz"
                    ),
                    "server_sha256": sha(BASE / "glm53-server.json"),
                    "started_utc": datetime.now(timezone.utc).isoformat(),
                },
                indent=2,
            )
            + "\n"
        )
        save("glm53-proof-pilot-running", pilot_pid=p.pid)
        code = p.wait()
    if code or load(BASE / name / "results.json").get("status") != "finished":
        raise RuntimeError(
            "Full GLM proof pilot incomplete; runtime retained for diagnosis"
        )
    save("glm53-proof-pilot-finished")


if __name__ == "__main__":
    try:
        main()
    except Exception as error:
        save("failed", error=type(error).__name__ + ": " + str(error))
        raise
