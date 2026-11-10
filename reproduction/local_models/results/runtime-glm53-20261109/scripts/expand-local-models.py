"""Launch disjoint reduced-fixture batches; models only return bounded proof JSON."""

from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import os
import subprocess
import sys
import time

BASE = Path("/tmp/lark-local-models-20261109")
ROOT = Path("/dev/shm/lark-proof-controller-budget-20261109/source")
LEAN = "/dev/shm/lark-proof-controller-20261109/runtime/lean-4.19.0-linux/bin/lean"
EXTRA = sorted(
    p.name
    for p in (ROOT / "reproduction/nonlinear/cases/float16").iterdir()
    if p.name not in ("relu", "silu", "softmax") and (p / "task.json").is_file()
)
assert len(EXTRA) == 14


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def launch(name, model, server_name, cases, attempts):
    server_path = BASE / server_name
    server = json.loads(server_path.read_text())
    assert server["status"] == "ready" and server["model"] == model
    assert not (BASE / name).exists()
    args = [
        "python3",
        "-m",
        "reproduction.local_models.run",
        "--url",
        server["endpoint"],
        "--model",
        model,
        "--server-record",
        str(server_path),
        "--output",
        str(BASE / name),
        "--lean",
        LEAN,
        "--attempts",
        str(attempts),
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
    for case in cases:
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
            start_new_session=True,
        )
    record = {
        "pid": p.pid,
        "args": args,
        "cwd": str(ROOT),
        "server_sha256": sha(server_path),
        "controller_source_sha256": sha(BASE / "budget-controller-source.tar.gz"),
        "additional_cases_sha256": sha(BASE / "additional-cases-source.tar.gz"),
        "launcher_sha256": sha(Path(__file__)),
        "started_utc": datetime.now(timezone.utc).isoformat(),
    }
    (BASE / (name + "-launch.json")).write_text(json.dumps(record, indent=2) + "\n")
    print(json.dumps(record), flush=True)


def full_early():
    launch(
        "glm53-budget4096-half-a-remote",
        "zai-org/GLM-5.3",
        "glm53-server.json",
        EXTRA[:7],
        3,
    )


def full_late():
    deadline = time.monotonic() + 14400
    while time.monotonic() < deadline:
        try:
            done = (
                json.loads(
                    (BASE / "glm53-budget4096-remote/results.json").read_text()
                ).get("status")
                == "finished"
            )
        except (FileNotFoundError, json.JSONDecodeError):
            done = False
        if done:
            launch(
                "glm53-budget4096-half-b-remote",
                "zai-org/GLM-5.3",
                "glm53-server.json",
                EXTRA[7:],
                3,
            )
            return
        time.sleep(20)
    raise RuntimeError(
        "First full-model batch did not finish; deferred batch not launched"
    )


def flash():
    args = [
        "python3",
        str(BASE / "scripts/serve-flash17.py"),
        "--checkpoint",
        str(BASE / "checkpoint-verified.json"),
        "--cache",
        "/dev/shm/lark-models-20261109/hub",
        "--runtime-cache",
        "/dev/shm/lark-flash17-vllm-cache-20261109",
        "--output",
        str(BASE / "flash17-server.json"),
        "--gpu-ids",
        "2,3",
        "--name",
        "lark-glm53-flash-eval17-20261109",
        "--port",
        "19085",
        "--launch",
    ]
    result = subprocess.run(args, capture_output=True, text=True, timeout=180)
    (BASE / "flash17-launch.log").write_text(result.stdout + result.stderr)
    if result.returncode:
        raise RuntimeError(
            "Flash additional-fixture launch refused/failed; inspect flash17-launch.log"
        )
    result = subprocess.run(
        [
            "python3",
            str(BASE / "scripts/ready.py"),
            "--server",
            str(BASE / "flash17-server.json"),
            "--timeout",
            "3600",
        ],
        capture_output=True,
        text=True,
        timeout=3630,
    )
    (BASE / "flash17-readiness.log").write_text(result.stdout + result.stderr)
    if result.returncode:
        raise RuntimeError("Flash additional-fixture runtime not ready")
    sys.path.insert(0, str(ROOT))
    from reproduction.local_models import client

    answer = client.call(
        "http://127.0.0.1:19085/v1/chat/completions",
        "zai-org/GLM-5.3-Flash",
        [
            {
                "role": "user",
                "content": "Reply with exactly LARK_READY and no explanation.",
            }
        ],
        BASE / "flash17-warmup",
        max_tokens=256,
        thinking_token_budget=64,
        reasoning_effort="low",
        timeout=120,
    )
    assert answer.strip() == "LARK_READY"
    for letter, cases in [("a", EXTRA[:7]), ("b", EXTRA[7:])]:
        launch(
            "flash17-budget4096-half-" + letter + "-remote",
            "zai-org/GLM-5.3-Flash",
            "flash17-server.json",
            cases,
            1,
        )


if __name__ == "__main__":
    {"full-early": full_early, "full-late": full_late, "flash": flash}[sys.argv[1]]()
