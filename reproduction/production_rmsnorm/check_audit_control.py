"""Require rejection of a changed raw stream even after its hashes are refreshed."""

import argparse
import hashlib
import json
from pathlib import Path
import shutil
import tempfile

from audit_gpu import audit


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--input", required=True, type=Path)
    p.add_argument("--results", required=True, type=Path)
    p.add_argument("--output", required=True, type=Path)
    args = p.parse_args()
    source = args.results.resolve()
    with tempfile.TemporaryDirectory(prefix="lark-rms-raw-control-") as temporary:
        dest = Path(temporary)
        for path in source.iterdir():
            if path.is_file() and path.name not in ("adapted.bin", "results.json", "manifest.json"):
                (dest / path.name).symlink_to(path)
        shutil.copyfile(source / "adapted.bin", dest / "adapted.bin")
        with (dest / "adapted.bin").open("r+b") as stream:
            stream.write(b"\xff\x7b")  # Finite half 65504: far beyond the unchanged reference.
        report = json.loads((source / "results.json").read_text())
        report["adapted_sha256"] = sha(dest / "adapted.bin")
        (dest / "results.json").write_text(json.dumps(report, indent=2) + "\n")
        manifest = json.loads((source / "manifest.json").read_text())
        for name in ("adapted.bin", "results.json"):
            manifest[name] = sha(dest / name)
        (dest / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
        try:
            audit(args.input.resolve(), dest)
        except AssertionError as exc:
            if str(exc) != "Numerical tolerance violated in raw stream":
                raise
            result = {
                "status": "passed",
                "control": "fully rehashed changed adapted output",
                "rejected": True,
                "gate": str(exc),
                "certificates": 0,
            }
        else:
            raise RuntimeError("Changed raw stream was accepted")
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result), flush=True)


if __name__ == "__main__":
    main()
