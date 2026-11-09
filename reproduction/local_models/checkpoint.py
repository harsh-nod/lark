"""Download or validate a pinned public checkpoint, recording every weight hash.

Run on the GPU host with huggingface_hub installed. This makes no model calls.
"""

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import time

MODELS = {
    "zai-org/GLM-5.3-Flash": "46a050bec13002ad29ee795c16e61cf4fa3c4a9c",
    "zai-org/GLM-5.3": "ba32f8c19c8738e2c57c71798c601d477a7bf844",
    "deepseek-ai/DeepSeek-V4.1-Flash-1017": "1bae0e1088993b9b82de08f59de5be5a34e42170",
}


def sha(path):
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(16 * 1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--model", choices=sorted(MODELS), default="zai-org/GLM-5.3-Flash")
    p.add_argument("--cache", type=Path, required=True)
    p.add_argument("--output", type=Path, required=True)
    p.add_argument("--workers", type=int, default=8)
    args = p.parse_args()
    if args.output.exists() or not 1 <= args.workers <= 16:
        p.error("fresh output and 1..16 download workers are required")
    os.environ.setdefault("HF_XET_CHUNK_CACHE_SIZE_BYTES", "0")
    os.environ.setdefault("HF_XET_HIGH_PERFORMANCE", "1")
    # Set HF_HOME in the calling shell so the optional Xet cache is isolated too.
    from huggingface_hub import HfApi, snapshot_download

    revision = MODELS[args.model]
    assert re.fullmatch("[0-9a-f]{40}", revision)
    info = HfApi().model_info(args.model, revision=revision, files_metadata=True)
    if info.sha != revision or info.gated:
        raise RuntimeError("Expected the pinned, ungated public checkpoint")
    started = time.monotonic()
    snapshot = Path(
        snapshot_download(
            args.model,
            revision=revision,
            cache_dir=str(args.cache),
            max_workers=args.workers,
            allow_patterns=[
                "*.safetensors",
                "*.json",
                "*.model",
                "*.txt",
                "*.jinja",
                "*.py",
                "*.md",
                "LICENSE*",
            ],
        )
    )
    record = {
        "schema": 1,
        "model": args.model,
        "revision": revision,
        "path": str(snapshot),
        "timestamp_utc": datetime.now(timezone.utc).isoformat(),
        "download_seconds": time.monotonic() - started,
        "model_calls": 0,
        "runner_sha256": sha(Path(__file__)),
        "weights": [],
        "status": "checking",
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(record, indent=2) + "\n")
    for sibling in info.siblings:
        if not sibling.rfilename.endswith(".safetensors"):
            continue
        path = snapshot / sibling.rfilename
        expected = sibling.lfs.sha256 if sibling.lfs else None
        if not expected or path.stat().st_size != sibling.size:
            raise RuntimeError("Missing LFS digest or wrong weight size: " + sibling.rfilename)
        actual = sha(path)
        if actual != expected:
            raise RuntimeError("Weight SHA-256 mismatch: " + sibling.rfilename)
        record["weights"].append(
            {"file": sibling.rfilename, "bytes": sibling.size, "sha256": actual}
        )
        args.output.write_text(json.dumps(record, indent=2) + "\n")
        print(json.dumps(record["weights"][-1]), flush=True)
    if not record["weights"]:
        raise RuntimeError("No checkpoint weights found")
    record["status"] = "verified-download"
    args.output.write_text(json.dumps(record, indent=2) + "\n")


if __name__ == "__main__":
    main()
