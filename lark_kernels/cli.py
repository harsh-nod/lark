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
        "verify-shuffle",
        "verify-mfma",
        "inspect",
        "verify-pointwise",
        "verify-gemv",
        "verify-matrix",
        "verify-linear",
        "verify-rotary",
        "verify-convolution",
        "verify-normalization",
        "verify-silu",
        "verify-wave-sum",
        "verify-native-rmsnorm",
        "verify-native-fused-rmsnorm",
        "verify-native-rope",
        "verify-native-qknorm-rope",
    ):
        p = sub.add_parser(command)
        p.add_argument("kernel", type=Path)
        p.add_argument("--reference", required=True, type=Path)
        p.add_argument("--task", required=True, type=Path)
        if command in {
            "verify",
            "verify-shuffle",
            "verify-mfma",
            "verify-pointwise",
            "verify-gemv",
            "verify-matrix",
            "verify-linear",
            "verify-rotary",
            "verify-convolution",
            "verify-normalization",
            "verify-silu",
            "verify-wave-sum",
            "verify-native-rmsnorm",
            "verify-native-fused-rmsnorm",
            "verify-native-rope",
            "verify-native-qknorm-rope",
        }:
            p.add_argument("--output", required=True, type=Path)
            p.add_argument("--lean")
            p.add_argument(
                "--timeout",
                type=float,
                default=600 if command in {"verify-native-rmsnorm", "verify-native-fused-rmsnorm", "verify-native-rope", "verify-native-qknorm-rope"} else (
                    300 if command in {"verify-shuffle", "verify-mfma", "verify-wave-sum"} else 120
                ),
            )
            p.add_argument("--proposal", type=Path)
            p.add_argument(
                "--provider", help="explicit local proof-provider command; JSON stdin/stdout"
            )
            p.add_argument("--attempts", type=int, default=1)
    p = sub.add_parser("verify-ffn")
    p.add_argument("directory", type=Path)
    p.add_argument("--output", required=True, type=Path)
    p.add_argument("--lean")
    p.add_argument("--timeout", type=float, default=120)
    p = sub.add_parser("verify-attention")
    p.add_argument("directory", type=Path)
    p.add_argument("--output", required=True, type=Path)
    p.add_argument("--lean")
    p.add_argument("--timeout", type=float, default=120)
    p = sub.add_parser("verify-swiglu")
    p.add_argument("directory", type=Path)
    p.add_argument("--output", required=True, type=Path)
    p.add_argument("--lean")
    p.add_argument("--timeout", type=float, default=120)
    p = sub.add_parser("check")
    p.add_argument("directory", type=Path)
    p.add_argument("--lean")
    p.add_argument("--timeout", type=float, default=120)
    args = parser.parse_args(argv)
    try:
        if args.command == "check":
            print(check(args.directory, lean=args.lean, timeout=args.timeout).strip())
            print("VERIFIED: source binding, model, proofs, and axiom audit rechecked")
        elif args.command == "verify-mfma":
            from .mfma import verify as verify_mfma

            if args.provider or args.attempts != 1:
                raise Refusal(
                    "configuration", "MFMA verification checks one explicit proof proposal"
                )
            report = verify_mfma(
                args.kernel,
                args.reference,
                args.task,
                args.output,
                lean=args.lean,
                timeout=args.timeout,
                proposal_path=args.proposal,
            )
            print(f"{report['status'].upper()}: {args.output / 'report.json'}")
            return 0 if report["status"] == "verified" else 1
        elif args.command == "verify-shuffle":
            from .collective import verify as verify_shuffle

            if args.provider or args.attempts != 1:
                raise Refusal(
                    "configuration", "shuffle verification checks one explicit proof proposal"
                )
            report = verify_shuffle(
                args.kernel,
                args.reference,
                args.task,
                args.output,
                lean=args.lean,
                timeout=args.timeout,
                proposal_path=args.proposal,
            )
            print(f"{report['status'].upper()}: {args.output / 'report.json'}")
            return 0 if report["status"] == "verified" else 1
        elif args.command == "verify-attention":
            from .attention import verify as verify_attention

            report = verify_attention(
                args.directory, args.output, lean=args.lean, timeout=args.timeout
            )
            print(f"{report['status'].upper()}: {args.output / 'report.json'}")
            return 0 if report["status"] == "verified" else 1
        elif args.command == "verify-swiglu":
            from .swiglu import verify as verify_swiglu

            report = verify_swiglu(
                args.directory, args.output, lean=args.lean, timeout=args.timeout
            )
            print(f"{report['status'].upper()}: {args.output / 'report.json'}")
            return 0 if report["status"] == "verified" else 1
        elif args.command == "verify-ffn":
            from .feedforward import verify as verify_ffn

            report = verify_ffn(args.directory, args.output, lean=args.lean, timeout=args.timeout)
            print(f"{report['status'].upper()}: {args.output / 'report.json'}")
            return 0 if report["status"] == "verified" else 1
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
            "verify-normalization",
            "verify-silu",
            "verify-wave-sum",
            "verify-native-rmsnorm",
            "verify-native-fused-rmsnorm",
            "verify-native-rope",
            "verify-native-qknorm-rope",
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
            elif args.command == "verify-convolution":
                from .convolution import verify as verify_inductive
            elif args.command == "verify-wave-sum":
                from .wave_sum import verify as verify_inductive
            elif args.command == "verify-native-rope":
                from .native_rope_certificate import verify as verify_inductive
            elif args.command == "verify-native-qknorm-rope":
                from .native_qknorm_rope_certificate import verify as verify_inductive
            elif args.command == "verify-native-fused-rmsnorm":
                from .native_fused_rmsnorm_certificate import verify as verify_inductive
            elif args.command == "verify-native-rmsnorm":
                from .native_rmsnorm_certificate import verify as verify_inductive
            elif args.command == "verify-silu":
                from .silu import verify as verify_inductive
            else:
                from .normalization import verify as verify_inductive

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
