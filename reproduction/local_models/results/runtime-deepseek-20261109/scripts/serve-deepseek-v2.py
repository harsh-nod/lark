"""Prepare or launch an isolated DeepSeek-V4.1-Flash-1017 endpoint on the checked MI350 host.

Requires a completed checkpoint.py record. Existing containers are never stopped.
The host publishes only a loopback port and the model loader runs offline.
"""

import argparse
import csv
from datetime import datetime, timezone
import grp
import hashlib
import io
import json
from pathlib import Path
import subprocess

IMAGE = (
    "vllm/vllm-openai-rocm@sha256:71a5d125b10a594752014b917a00cb1743387d1be9ee188aa1862af0b143c7dd"
)
MODEL = "deepseek-ai/DeepSeek-V4.1-Flash-1017"


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--checkpoint", required=True, type=Path)
    p.add_argument("--cache", required=True, type=Path)
    p.add_argument("--runtime-cache", required=True, type=Path)
    p.add_argument("--output", required=True, type=Path)
    p.add_argument("--name", default="lark-deepseek-v41-flash-20261109")
    p.add_argument("--gpu-ids", default="2,3,4,5")
    p.add_argument("--port", type=int, default=19082)
    p.add_argument("--launch", action="store_true")
    args = p.parse_args()
    checkpoint = json.loads(args.checkpoint.read_text())
    if (
        checkpoint["status"] != "verified-download"
        or checkpoint["model"] != MODEL
        or checkpoint["revision"] != "1bae0e1088993b9b82de08f59de5be5a34e42170"
    ):
        p.error("a completed, hash-checked DeepSeek-V4.1-Flash-1017 checkpoint is required")
    if args.output.exists() or not 1024 <= args.port <= 65535:
        p.error("fresh output and an unprivileged port are required")
    devices = args.gpu_ids.split(",")
    if len(devices) != 4 or len(set(devices)) != 4 or any(not d.isdecimal() for d in devices):
        p.error("exactly four distinct GPU indices are required")
    data = subprocess.check_output(
        ["rocm-smi", "--showmeminfo", "vram", "--showuse", "--csv"], text=True
    )
    lines = [line for line in data.splitlines() if line.startswith(("device,", "card"))]
    rows = {r["device"]: r for r in csv.DictReader(io.StringIO("\n".join(lines)))}
    for device in devices:
        row = rows["card" + device]
        if int(row["VRAM Total Used Memory (B)"]) > 1024**3 or int(row["GPU use (%)"]) > 5:
            raise RuntimeError("Selected GPU is in use: " + device)
        if int(row["VRAM Total Memory (B)"]) < 240 * 1024**3:
            raise RuntimeError(
                "This launch requires four MI350X-class GPUs with at least 240 GiB each"
            )
    existing = subprocess.check_output(
        ["docker", "ps", "-aq", "--filter", "name=^/" + args.name + "$"], text=True
    )
    if existing.strip():
        raise RuntimeError("Container name already exists; existing services will not be replaced")
    ports = subprocess.check_output(
        ["ss", "-H", "-ltn", "sport", "=", ":" + str(args.port)], text=True
    )
    if ports.strip():
        raise RuntimeError("Port already in use")
    snapshot = Path(checkpoint["path"]).relative_to(args.cache)
    args.runtime_cache.mkdir(parents=True, exist_ok=True)
    env = {
        "HIP_VISIBLE_DEVICES": args.gpu_ids,
        "HF_HUB_OFFLINE": "1",
        "TRANSFORMERS_OFFLINE": "1",
        "VLLM_ENGINE_READY_TIMEOUT_S": "3600",
        "VLLM_ROCM_USE_AITER": "1",
        "VLLM_ROCM_USE_AITER_MOE": "1",
        "AITER_TRITON_LOG_LEVEL": "ERROR",
        "VLLM_USE_BREAKABLE_CUDAGRAPH": "1",
        "VLLM_ROCM_USE_AITER_TRITON_SPARSE_MLA": "1",
        "TRITON_CACHE_DIR": "/runtime-cache/triton",
        "TORCHINDUCTOR_CACHE_DIR": "/runtime-cache/inductor",
        "VLLM_CACHE_ROOT": "/runtime-cache/vllm",
    }

    command = [
        "docker",
        "run",
        "-d",
        "--name",
        args.name,
        "--group-add",
        str(grp.getgrnam("video").gr_gid),
        "--group-add",
        str(grp.getgrnam("render").gr_gid),
        "--cap-add=SYS_PTRACE",
        "--security-opt",
        "seccomp=unconfined",
        "--device",
        "/dev/kfd",
        "--device",
        "/dev/dri",
        "--ipc=host",
        "-p",
        f"127.0.0.1:{args.port}:{args.port}",
        "-v",
        str(args.cache.resolve()) + ":/model-cache:ro",
        "-v",
        str(args.runtime_cache.resolve()) + ":/runtime-cache",
    ]
    for key, value in env.items():
        command += ["--env", key + "=" + value]
    command += [
        IMAGE,
        "--model",
        "/model-cache/" + str(snapshot),
        "--served-model-name",
        MODEL,
        "--host",
        "0.0.0.0",
        "--port",
        str(args.port),
        "--tensor-parallel-size",
        "4",
        "--distributed-executor-backend",
        "mp",
        "--gpu-memory-utilization",
        "0.85",
        "--max-model-len",
        "65536",
        "--max-num-seqs",
        "2",
        "--max-num-batched-tokens",
        "4096",
        "--enforce-eager",
        "--tokenizer-mode",
        "deepseek_v41",
        "--reasoning-parser",
        "deepseek_v41",
        "--tool-call-parser",
        "deepseek_v41",
        "--enable-auto-tool-choice",
        "--moe-backend",
        "aiter",
        "--engram-config",
        '{"cpu_offload":true}',
        "--attention-config",
        '{"indexer_kv_dtype":"mxfp4","indexer_sparse_logits":true}',
        "--block-size",
        "128",
        "--disable-custom-all-reduce",
        "--monokernel",
        "--language-model-only",
    ]
    record = {
        "schema": 1,
        "status": "prepared",
        "container_name": args.name,
        "model": MODEL,
        "revision": checkpoint["revision"],
        "precision": "official native mixed MXFP4/MXFP8 checkpoint; CPU Engram offload, text-only",
        "image": IMAGE,
        "gpu_ids": devices,
        "max_model_len": 65536,
        "tensor_parallel": 4,
        "endpoint": f"http://127.0.0.1:{args.port}/v1/chat/completions",
        "checkpoint_record_sha256": hashlib.sha256(args.checkpoint.read_bytes()).hexdigest(),
        "runner_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "timestamp_utc": datetime.now(timezone.utc).isoformat(),
        "docker_command": command,
        "collectives": "standard RCCL; optional FlyDSL INT4 QuickAllReduce disabled after pinned-image API mismatch",
        "external_api_spend_usd": 0,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(record, indent=2) + "\n")
    if args.launch:
        result = subprocess.run(command, text=True, capture_output=True, timeout=120)
        record.update(
            status="started" if result.returncode == 0 else "launch-failed",
            docker_stdout=result.stdout,
            docker_stderr=result.stderr,
        )
        args.output.write_text(json.dumps(record, indent=2) + "\n")
        if result.returncode:
            raise RuntimeError(result.stderr)
    print(json.dumps(record, indent=2))


if __name__ == "__main__":
    main()
