"""Read-only metadata and capacity checks for free local model experiments.

HTTPS runs on the GPU host, whose certificate store validates Hugging Face and
Docker Hub. No weights, containers or model calls are started by this command.
"""

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import subprocess

MODELS = [
    "zai-org/GLM-5.3-Flash",
    "zai-org/GLM-5.3",
    "deepseek-ai/DeepSeek-V4.1-Flash-1017",
]

REMOTE = r"""
import json, pathlib, subprocess, urllib.request

def fetch(url, headers=None):
    with urllib.request.urlopen(urllib.request.Request(url, headers=headers or {}), timeout=60) as response:
        return json.load(response), response.headers.get("Docker-Content-Digest")

models = []
for model in MODEL_IDS:
    data, _ = fetch("https://huggingface.co/api/models/" + model + "?blobs=true")
    files = [{"name": f["rfilename"], "size": f.get("size"), "lfs": f.get("lfs")}
             for f in data.get("siblings", [])]
    models.append({"model": model, "revision": data["sha"], "gated": data.get("gated"),
        "weight_bytes": sum(f.get("size") or 0 for f in files if f["name"].endswith(".safetensors")),
        "files": files, "parameter_dtypes": data.get("safetensors", {}).get("parameters")})

repo = "vllm/vllm-openai-rocm"
auth, _ = fetch("https://auth.docker.io/token?service=registry.docker.io&scope=repository:" + repo + ":pull")
headers = {"Authorization": "Bearer " + auth["token"],
    "Accept": "application/vnd.oci.image.index.v1+json,application/vnd.docker.distribution.manifest.list.v2+json,application/vnd.docker.distribution.manifest.v2+json,application/vnd.oci.image.manifest.v1+json"}
manifest, digest = fetch("https://registry-1.docker.io/v2/" + repo + "/manifests/nightly", headers)
if "manifests" in manifest:
    image = next(m for m in manifest["manifests"] if m.get("platform", {}).get("architecture") == "amd64")
    manifest, digest = fetch("https://registry-1.docker.io/v2/" + repo + "/manifests/" + image["digest"], headers)
config, _ = fetch("https://registry-1.docker.io/v2/" + repo + "/blobs/" + manifest["config"]["digest"], headers)
image = {"image": repo + "@" + digest,
    "compressed_bytes": sum(l["size"] for l in manifest["layers"]),
    "layers": manifest["layers"], "created": config.get("created"),
    "runtime_environment": [v for v in config.get("config", {}).get("Env", [])
                            if v.startswith(("ROCM", "VLLM", "PYTORCH", "TORCH"))]}

commands = [["rocm-smi", "--showmeminfo", "vram", "--showuse", "--csv"],
    ["df", "-B1", "/tmp", "/dev/shm"], ["free", "-b"],
    ["findmnt", "-n", "-o", "OPTIONS", "/dev/shm"]]
hardware = []
for cmd in commands:
    result = subprocess.run(cmd, capture_output=True, text=True, timeout=30)
    hardware.append({"command": cmd, "exit_code": result.returncode,
                     "stdout": result.stdout, "stderr": result.stderr})
print(json.dumps({"models": models, "image": image, "hardware": hardware}))
"""


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--host", default="mi350")
    p.add_argument("--output", type=Path, required=True)
    args = p.parse_args()
    if args.output.exists():
        raise SystemExit("Refusing to overwrite an earlier preflight")
    script = "MODEL_IDS = " + repr(MODELS) + "\n" + REMOTE
    result = subprocess.run(
        ["ssh", "-q", "-o", "BatchMode=yes", "-o", "ConnectTimeout=10", args.host, "python3", "-"],
        input=script,
        text=True,
        capture_output=True,
        timeout=300,
    )
    if result.returncode:
        raise RuntimeError(result.stderr)
    report = json.loads(result.stdout)
    report.update(
        schema=1,
        host=args.host,
        timestamp_utc=datetime.now(timezone.utc).isoformat(),
        model_calls=0,
        runner_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        scope="Preflight only. Original paper harness and hosted-model equivalence are not established.",
    )
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(
        json.dumps(
            {
                "host": args.host,
                "models": [
                    {
                        "model": m["model"],
                        "revision": m["revision"],
                        "weight_gib": round(m["weight_bytes"] / 2**30, 2),
                        "gated": m["gated"],
                    }
                    for m in report["models"]
                ],
                "image": report["image"]["image"],
            }
        )
    )


if __name__ == "__main__":
    main()
