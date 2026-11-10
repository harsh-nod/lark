"""Transport the frozen runner and packet to one explicitly selected idle GPU."""

import argparse
import hashlib
from pathlib import Path
import subprocess


REMOTE = r"""
import hashlib, json, os
from pathlib import Path, PurePosixPath
import subprocess, tarfile
config = CONFIG
root = Path(config["remote"])
packet = root / "packet.tar.gz"
assert hashlib.sha256(packet.read_bytes()).hexdigest() == config["transport_sha256"]
with tarfile.open(packet) as tar:
    seen = set()
    for member in tar:
        path = PurePosixPath(member.name)
        assert member.isfile() and not path.is_absolute() and ".." not in path.parts
        assert str(path) == member.name and member.name not in seen
        seen.add(member.name)
        target = root / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(tar.extractfile(member).read())
out = root / "artifacts"
out.mkdir()
metric = subprocess.run(["amd-smi", "metric", "--json"], text=True, capture_output=True, check=True)
(out / "preexecution-metric.json").write_text(metric.stdout)
(out / "preexecution-metric.stderr").write_text(metric.stderr)
gpu = next(g for g in json.loads(metric.stdout)["gpu_data"] if g["gpu"] == config["physical_gpu"])
assert gpu["usage"]["gfx_activity"]["value"] == 0, "Selected GPU is active"
env = dict(os.environ)
env.pop("HIP_VISIBLE_DEVICES", None)
env.pop("CUDA_VISIBLE_DEVICES", None)
env["ROCR_VISIBLE_DEVICES"] = str(config["physical_gpu"])
with (out / "run.log").open("w") as log:
    run = subprocess.run(["python3", str(root / "runner.py"), "--input", str(root / "input"),
                          "--output", str(out / "gpu")], env=env, stdout=log, stderr=subprocess.STDOUT)
(out / "controller.json").write_text(json.dumps({**config, "returncode": run.returncode}, indent=2) + "\n")
with tarfile.open(root / "artifacts.tar.gz", "w:gz") as tar:
    for p in sorted(out.rglob("*")):
        if p.is_file():
            tar.add(p, arcname=p.relative_to(out), recursive=False)
print(json.dumps({"host": config["host"], "physical_gpu": config["physical_gpu"], "returncode": run.returncode}))
raise SystemExit(run.returncode)
"""


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--host", choices=("mi350", "mi350-2"), required=True)
    p.add_argument("--gpu", type=int, required=True)
    p.add_argument("--packet", type=Path, required=True)
    p.add_argument("--output", type=Path, required=True)
    p.add_argument("--remote", default="/tmp/lark-wave-reduction-run-20261110")
    args = p.parse_args()
    if args.gpu < 0 or not args.remote.startswith("/tmp/lark-wave-"):
        raise ValueError("Explicit GPU and owned temporary root required")
    if args.output.exists():
        raise ValueError("Fresh local output required")
    config = {
        "host": args.host,
        "physical_gpu": args.gpu,
        "remote": args.remote,
        "transport_sha256": hashlib.sha256(args.packet.read_bytes()).hexdigest(),
        "controller_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    }
    # mkdir refuses to replace any earlier run. JSON/Python literals never enter a shell command.
    create = "from pathlib import Path\nPath(" + repr(args.remote) + ").mkdir()\n"
    subprocess.run(["ssh", args.host, "python3 -"], input=create, text=True, check=True)
    subprocess.run(
        ["scp", str(args.packet), args.host + ":" + args.remote + "/packet.tar.gz"], check=True
    )
    result = subprocess.run(
        ["ssh", args.host, "python3 -"],
        input=REMOTE.replace("CONFIG", repr(config)),
        text=True,
    )
    # Recover evidence even when the runner fails; never relaunch a timed-out observation.
    subprocess.run(
        ["scp", args.host + ":" + args.remote + "/artifacts.tar.gz", str(args.output)], check=True
    )
    raise SystemExit(result.returncode)


if __name__ == "__main__":
    main()
