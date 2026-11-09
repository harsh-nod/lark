"""Command line entry point; failed proofs and unsupported inputs fail closed."""

import argparse
import json
from pathlib import Path
import shlex
import sys

from .certificate import check, verify
from .frontend import translate
from .ir import Refusal, Task
from .machine import preflight
from .spec import read_spec


def main(argv=None):
    parser = argparse.ArgumentParser(prog="lark", description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    for command in (
        "verify",
        "inspect",
        "verify-pointwise",
        "verify-gemv",
        "verify-matrix",
        "verify-linear",
        "verify-rotary",
        "verify-convolution",
    ):
        p = sub.add_parser(command)
        p.add_argument("kernel", type=Path)
        p.add_argument("--reference", required=True, type=Path)
        p.add_argument("--task", required=True, type=Path)
        if command in {
            "verify",
            "verify-pointwise",
            "verify-gemv",
            "verify-matrix",
            "verify-linear",
            "verify-rotary",
            "verify-convolution",
        }:
            p.add_argument("--output", required=True, type=Path)
            p.add_argument("--lean")
            p.add_argument("--timeout", type=float, default=120)
            p.add_argument("--proposal", type=Path)
            p.add_argument(
                "--provider", help="explicit local proof-provider command; JSON stdin/stdout"
            )
            p.add_argument("--attempts", type=int, default=1)
    p = sub.add_parser("check")
    p.add_argument("directory", type=Path)
    p.add_argument("--lean")
    p.add_argument("--timeout", type=float, default=120)
    args = parser.parse_args(argv)
    try:
        if args.command == "check":
            print(check(args.directory, lean=args.lean, timeout=args.timeout).strip())
            print("VERIFIED: source binding, model, proofs, and axiom audit rechecked")
        elif args.command == "inspect":
            task = Task.read(args.task)
            tr = translate(args.kernel.read_bytes().decode("utf-8"), task)
            spec = read_spec(args.reference.read_text(), task)
            m = preflight(task, tr, spec)
            print(
                json.dumps(
                    {
                        "status": "preflight-only",
                        "certificate": False,
                        "instructions": len(tr.program),
                        "accesses": len(m.trace),
                        "source_readback": True,
                    },
                    indent=2,
                )
            )
        elif args.command in {
            "verify-pointwise",
            "verify-gemv",
            "verify-matrix",
            "verify-linear",
            "verify-rotary",
            "verify-convolution",
        }:
            if args.command == "verify-pointwise":
                from .pointwise import verify as verify_inductive
            elif args.command == "verify-gemv":
                from .gemv import verify as verify_inductive
            elif args.command == "verify-matrix":
                from .matrix import verify as verify_inductive
            elif args.command == "verify-linear":
                from .linear import verify as verify_inductive
            elif args.command == "verify-rotary":
                from .rotary import verify as verify_inductive
            else:
                from .convolution import verify as verify_inductive

            if args.provider or args.proposal or args.attempts != 1:
                raise Refusal("configuration", "inductive profiles use their pinned proofs")
            report = verify_inductive(
                args.kernel,
                args.reference,
                args.task,
                args.output,
                lean=args.lean,
                timeout=args.timeout,
            )
            print(f"{report['status'].upper()}: {args.output / 'report.json'}")
            return 0 if report["status"] == "verified" else 1
        else:
            if not 1 <= args.attempts <= 20 or args.timeout <= 0:
                raise Refusal(
                    "configuration", "attempts must be 1..20 and timeout must be positive"
                )
            report = verify(
                args.kernel,
                args.reference,
                args.task,
                args.output,
                lean=args.lean,
                timeout=args.timeout,
                proposal_path=args.proposal,
                provider=shlex.split(args.provider) if args.provider else None,
                attempts=args.attempts,
            )
            print(f"{report['status'].upper()}: {args.output / 'report.json'}")
            return 0 if report["status"] == "verified" else 1
    except (Refusal, OSError, ValueError, KeyError, TypeError, RecursionError) as e:
        print(f"REFUSED: {e}", file=sys.stderr)
        return 2
    return 0
