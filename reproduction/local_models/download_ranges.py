"""Download pinned public safetensors with checked HTTPS ranges and bounded storage.

Two processes may use the same plan in opposite order; advisory locks avoid
duplicate transfers. Checkpoint.py independently checks every final weight and
support file before any serving launcher accepts the snapshot.
"""

import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import fcntl
import hashlib
import json
import os
from pathlib import Path
import shutil
import time
import urllib.request

from checkpoint import MODELS

CHUNK = 64 * 1024**2


def sha(path):
    h = hashlib.sha256()
    with path.open("rb") as f:
        for b in iter(lambda: f.read(16 * 1024**2), b""):
            h.update(b)
    return h.hexdigest()


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--model", choices=sorted(MODELS), required=True)
    p.add_argument("--cache", type=Path, required=True)
    p.add_argument("--spillover", type=Path, required=True)
    p.add_argument("--spillover-gib", type=int, default=240)
    p.add_argument("--output", type=Path, required=True)
    p.add_argument("--reverse", action="store_true")
    p.add_argument("--workers", type=int, default=16)
    args = p.parse_args()
    if args.output.exists() or args.spillover_gib < 0 or not 1 <= args.workers <= 16:
        p.error("fresh output, nonnegative spillover and 1..16 workers required")
    from huggingface_hub import HfApi

    rev = MODELS[args.model]
    info = HfApi().model_info(args.model, revision=rev, files_metadata=True)
    if info.sha != rev or info.gated:
        raise RuntimeError("Expected the pinned ungated public revision")
    model_dir = "models--" + args.model.replace("/", "--")
    base = args.cache / model_dir
    for root in (
        base / "blobs",
        base / "snapshots" / rev,
        args.spillover,
        args.cache / ".locks" / model_dir,
    ):
        root.mkdir(parents=True, exist_ok=True)
    files = sorted(
        (f for f in info.siblings if f.rfilename.endswith(".safetensors")),
        key=lambda f: f.rfilename,
    )
    plan, spilled = [], 0
    for f in files:
        if (
            Path(f.rfilename).is_absolute()
            or ".." in Path(f.rfilename).parts
            or not f.lfs
            or not f.lfs.sha256
        ):
            raise RuntimeError("Unsafe path or missing official weight digest")
        use_spill = spilled + f.size <= args.spillover_gib * 1024**3
        if use_spill:
            spilled += f.size
        dest = (args.spillover if use_spill else base / "blobs") / f.lfs.sha256
        plan.append(
            {
                "file": f.rfilename,
                "bytes": f.size,
                "sha256": f.lfs.sha256,
                "destination": str(dest.resolve()),
                "spilled": use_spill,
            }
        )
    for use_spill, root in ((True, args.spillover), (False, base / "blobs")):
        required = sum(
            r["bytes"]
            for r in plan
            if r["spilled"] == use_spill and not Path(r["destination"]).exists()
        )
        if shutil.disk_usage(root).free < required + 32 * 1024**3:
            raise RuntimeError("Insufficient storage with 32 GiB reserve: " + str(root))
    record = {
        "model": args.model,
        "revision": rev,
        "model_calls": 0,
        "transport": "HTTPS checked 64 MiB ranges",
        "runner_sha256": sha(Path(__file__)),
        "plan": plan,
        "files": [],
        "status": "downloading",
    }

    def save():
        args.output.write_text(json.dumps(record, indent=2) + "\n")

    args.output.parent.mkdir(parents=True, exist_ok=True)
    save()
    for row in reversed(plan) if args.reverse else plan:
        dest = Path(row["destination"])
        digest, size = row["sha256"], row["bytes"]
        with (args.cache / ".locks" / model_dir / (digest + ".lock")).open("a") as lock:
            try:
                fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
            except BlockingIOError:
                continue
            if dest.exists():
                continue
            temp = dest.with_name(digest + ".ranges.incomplete")
            fd = os.open(temp, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
            started = time.monotonic()
            try:
                os.ftruncate(fd, size)
                url = "https://huggingface.co/" + args.model + "/resolve/" + rev + "/" + row["file"]

                def chunk(start):
                    end = min(start + CHUNK, size) - 1
                    for attempt in range(6):
                        try:
                            req = urllib.request.Request(
                                url, headers={"Range": f"bytes={start}-{end}"}
                            )
                            with urllib.request.urlopen(req, timeout=45) as response:
                                if (
                                    response.status != 206
                                    or response.headers.get("Content-Range")
                                    != f"bytes {start}-{end}/{size}"
                                ):
                                    raise RuntimeError("Unexpected range response")
                                data = response.read(end - start + 2)
                            if len(data) != end - start + 1 or os.pwrite(fd, data, start) != len(
                                data
                            ):
                                raise RuntimeError("Incomplete range or local write")
                            return len(data)
                        except Exception as error:
                            if attempt == 5:
                                raise RuntimeError(
                                    "Range failed after retries: " + type(error).__name__
                                ) from None
                            time.sleep(min(2**attempt, 8))

                print(
                    json.dumps({"file": row["file"], "stage": "start", "bytes": size}), flush=True
                )
                with ThreadPoolExecutor(max_workers=args.workers) as pool:
                    jobs = [pool.submit(chunk, start) for start in range(0, size, CHUNK)]
                    completed = sum(job.result() for job in as_completed(jobs))
                os.close(fd)
                fd = None
                if completed != size or temp.stat().st_size != size or sha(temp) != digest:
                    raise RuntimeError("Full weight size/SHA-256 mismatch")
                os.replace(temp, dest)
                blob = base / "blobs" / digest
                if row["spilled"]:
                    blob.symlink_to(dest)
                target = base / "snapshots" / rev / row["file"]
                target.parent.mkdir(parents=True, exist_ok=True)
                target.symlink_to(os.path.relpath(blob, target.parent))
                record["files"].append({**row, "seconds": time.monotonic() - started})
                save()
                print(json.dumps(record["files"][-1]), flush=True)
            finally:
                if fd is not None:
                    os.close(fd)
    record["status"] = "finished"
    save()


if __name__ == "__main__":
    main()
