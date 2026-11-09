#!/usr/bin/env python3
"""Export all shipped example certificates to a new directory."""

import argparse
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from lark_kernels.certificate import verify


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    parser.add_argument("--lean")
    args = parser.parse_args()
    if args.output.exists():
        parser.error("output directory must not already exist")
    root = Path(__file__).resolve().parent.parent
    args.output.mkdir(parents=True)
    failed = False
    for p in sorted((root / "examples").iterdir()):
        report = verify(
            next(p.glob("kernel.*")),
            p / "reference.py",
            p / "task.json",
            args.output / p.name,
            lean=args.lean,
        )
        print(f"{p.name}: {report['status']}", flush=True)
        failed |= report["status"] != "verified"
    return int(failed)


if __name__ == "__main__":
    raise SystemExit(main())
