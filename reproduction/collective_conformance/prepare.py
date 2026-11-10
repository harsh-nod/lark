"""Deterministic shuffle selectors and exhaustive MFMA FP16 basis-pair probes."""

import argparse
from contextlib import ExitStack
import hashlib
import json
from pathlib import Path
import random
import struct

ROOT = Path(__file__).resolve().parent


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--output", type=Path, required=True)
    args = p.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    gen = random.Random(261102028)
    configs, inputs, expected = [], [], []
    for dtype in range(2):
        for width in (1, 2, 4, 8, 16, 32, 64):
            for mode in range(4):
                for selector in range(width + (mode in (1, 2))):
                    configs.append((mode, width, selector, dtype))
                    values = [gen.getrandbits(32) for _ in range(128)]
                    inputs.extend(values)
                    for lane in range(128):
                        local = lane % width
                        source = (selector, local - selector, local + selector, local ^ selector)[
                            mode
                        ]
                        if source < 0 or source >= width:
                            source = local
                        expected.append(values[lane - local + source])
    (args.output / "shuffle-configs.bin").write_bytes(
        b"".join(struct.pack("<4i", *c) for c in configs)
    )
    for name, values in (("shuffle-input.bin", inputs), ("shuffle-expected.bin", expected)):
        (args.output / name).write_bytes(struct.pack("<" + "I" * len(values), *values))

    def input_at(non_k, k):
        return (non_k + 16 * (k // 4)) * 4 + k % 4

    def output_at(row, col):
        return (16 * (row // 4) + col) * 4 + row % 4

    with ExitStack() as stack:
        streams = [
            stack.enter_context((args.output / name).open("wb"))
            for name in ("mfma-a.bin", "mfma-b.bin", "mfma-c.bin", "mfma-expected.bin")
        ]

        def emit(a, b, c, d):
            for f, x, kind in zip(streams, (a, b, c, d), ("e", "e", "f", "f")):
                f.write(struct.pack("<" + kind * 256, *x))

        zero = [0.0] * 256
        for ai in range(256):
            i, ka = divmod(ai, 16)
            a = zero.copy()
            a[input_at(i, ka)] = 1.0
            for bi in range(256):
                kb, j = divmod(bi, 16)
                b, d = zero.copy(), zero.copy()
                b[input_at(j, kb)] = 1.0
                if ka == kb:
                    d[output_at(i, j)] = 1.0
                emit(a, b, zero, d)
        for ci in range(256):
            c = zero.copy()
            c[ci] = 1.0
            emit(zero, zero, c, c)
        for trial in range(32):
            divisor = 1 if trial < 16 else 16
            a = [[gen.randint(-3, 3) / divisor for _ in range(16)] for _ in range(16)]
            b = [[gen.randint(-3, 3) / divisor for _ in range(16)] for _ in range(16)]
            c = [[gen.randint(-4, 4) / divisor for _ in range(16)] for _ in range(16)]
            pa, pb, pc, pd = [zero.copy() for _ in range(4)]
            for i in range(16):
                for j in range(16):
                    pa[input_at(i, j)] = a[i][j]
                    pb[input_at(j, i)] = b[i][j]
                    pc[output_at(i, j)] = c[i][j]
                    pd[output_at(i, j)] = c[i][j] + sum(a[i][k] * b[k][j] for k in range(16))
            emit(pa, pb, pc, pd)
    report = {
        "schema": 1,
        "experiment": "gfx950-shuffle-and-mfma-layout-conformance",
        "seed": 261102028,
        "runner_sha256": sha(Path(__file__)),
        "source_sha256": sha(ROOT / "probes.hip"),
        "shuffle_configs": len(configs),
        "shuffle_comparisons": len(expected),
        "mfma_basis_pairs": 65536,
        "mfma_accumulator_basis": 256,
        "mfma_exact_random_tiles": 32,
        "mfma_output_comparisons": (65536 + 256 + 32) * 256,
        "model_calls": 0,
        "scope": "Finite hardware conformance only. Full-partition uint32/float32 bit-copy shuffles and one MFMA shape with default modifiers. Exhaustive FP16 input basis pairs/accumulator basis plus exactly representable random operands. Not complete IEEE semantics, formal collective integration, NVIDIA layouts, other MFMA shapes or the authors instruction table.",
        "files": {p.name: sha(p) for p in sorted(args.output.glob("*.bin"))},
    }
    (args.output / "dataset.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({k: v for k, v in report.items() if k != "files"}))


if __name__ == "__main__":
    main()
