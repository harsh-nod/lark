"""Audit archived probe bytes, native assembly and both MI350X output payloads."""

import hashlib
import json
from pathlib import Path
import tarfile

ROOT = Path(__file__).resolve().parent


def sha(data):
    return hashlib.sha256(data).hexdigest()


def main():
    results = ROOT / "results"
    rows = []
    with tarfile.open(results / "source-and-data.tar.gz") as source:
        data_raw = source.extractfile("dataset.json").read()
        data = json.loads(data_raw)
        assert data["shuffle_configs"] == 1044 and data["shuffle_comparisons"] == 133632
        assert (
            data["mfma_basis_pairs"] == 65536
            and data["mfma_accumulator_basis"] == 256
            and data["mfma_exact_random_tiles"] == 32
        )
        assert data["mfma_output_comparisons"] == 16850944
        for name, digest in data["files"].items():
            assert sha(source.extractfile(name).read()) == digest
        assert sha(source.extractfile("prepare.py").read()) == data["runner_sha256"]
        assert sha(source.extractfile("probes.hip").read()) == data["source_sha256"]
        assert (ROOT / "probes.hip").read_bytes() == source.extractfile("probes.hip").read()
        assert (ROOT / "prepare.py").read_bytes() == source.extractfile("prepare.py").read()
        assert (ROOT / "run_gpu.py").read_bytes() == source.extractfile("run_gpu.py").read()
        for host in ("mi350", "mi350-2"):
            with tarfile.open(results / (host + "-artifacts.tar.gz")) as t:
                raw = t.extractfile("output/results.json").read()
                gpu = json.loads(raw)
                assert raw == (results / (host + ".json")).read_bytes()
                assert (
                    gpu["status"] == "passed"
                    and gpu["architecture"] == "gfx950"
                    and gpu["warp"] == 64
                )
                assert (
                    gpu["model_calls"] == 0
                    and gpu["inputs_unchanged"]
                    and gpu["guard_zones_unchanged"]
                )
                assert (
                    gpu["dataset_sha256"] == sha(data_raw)
                    and gpu["source_sha256"] == data["source_sha256"]
                )
                assert gpu["runner_sha256"] == sha(source.extractfile("run_gpu.py").read())
                launch = json.load(t.extractfile("launch.json"))
                assert launch["source_bundle_sha256"] == sha(
                    (results / "source-and-data.tar.gz").read_bytes()
                )
                assert gpu["compiler_mfma_assembly_present"] and gpu["compiler_assembly_hashes"]
                for name, digest in gpu["compiler_assembly_hashes"].items():
                    asm = t.extractfile("output/" + name).read()
                    assert sha(asm) == digest and b"v_mfma_f32_16x16x16" in asm
                assert [r["probe"] for r in gpu["results"]] == ["shuffle", "mfma"]
                for row, count in zip(gpu["results"], (133632, 16850944)):
                    stem = row["probe"]
                    actual = t.extractfile("output/" + stem + "-actual.bin").read()
                    expected = source.extractfile(stem + "-expected.bin").read()
                    assert len(actual) == len(expected) == count * 4 and actual == expected
                    assert (
                        row["comparisons"] == count
                        and row["mismatches"] == 0
                        and row["bit_identical"]
                    )
                    assert sha(actual) == row["actual_sha256"] == row["expected_sha256"]
                rows.append(f"| {host} | {gpu['device']} | 133,632 | 16,850,944 | 0 | unchanged |")
    (ROOT / "RESULTS.md").write_text(
        """# MI350X collective-layout conformance

Run date: 2026-11-09. **Independent finite hardware experiment, zero model calls.**
[Method and boundaries](README.md), [archived evidence](results/).

| Host | Device | Shuffle bit-copy comparisons | MFMA output comparisons | Mismatches | Inputs / allocation guards |
| --- | --- | ---: | ---: | ---: | --- |
"""
        + "\n".join(rows)
        + """

Each host passed **16,984,576 bit-identical output comparisons**. Actual output
payloads, compiler assembly, compile/run logs and every input/reference byte are
archived and SHA-256-bound; `summarize.py` audits these bindings. Both native
compilers emitted `v_mfma_f32_16x16x16...` in the saved device assembly.

- **Shuffles:** 1,044 full-partition configurations, two complete wave64s per
  configuration. Index/up/down/xor, every supported power-of-two width 1..64,
  all in-partition source selectors/xor masks, and all up/down offsets through
  the width. uint32 and float32 bit-copy overloads use seeded 32-bit payloads.
  Out-of-partition up/down reads check the documented self-return behavior;
  undefined index selectors are not issued.
- **One native MFMA shape:** FP16-input, FP32-accumulator 16x16x16, one full
  wave64, default modifiers. All **65,536 input basis pairs** cover every pair
  of A/B element positions, including matching and nonmatching reduction
  coordinates. Another **256 accumulator basis** cases and **32 exact random
  tiles** check accumulator preservation and arithmetic. The random integers
  and binary fractions are exactly representable throughout these tiny products.
- All source/config/input bytes stayed unchanged, and all seven device
  allocations retained 128-byte prefix/suffix guards.

This records finite conformance and lane/fragment layouts for these AMD forms.
It is **not** a proof of all IEEE operands, all modifiers, other MFMA shapes,
divergent/partial masks, barriers, NVIDIA/PTX collectives or the paper's complete
per-language instruction table. The existing Lean source reader still refuses
these operations. No whole-kernel certificate or race-freedom proof is inferred
from these measurements. Hardware/compiler correspondence remains trusted.
"""
    )
    (results / "validation.json").write_text(
        json.dumps(
            {
                "status": "passed",
                "source_and_probe_hashes_match": True,
                "current_runners_match_executed": True,
                "both_actual_output_payloads_match_expected": True,
                "compiler_native_mfma_present": True,
                "comparisons_per_host": 16984576,
                "formal_model_extended": False,
            },
            indent=2,
        )
        + "\n"
    )
    (results / "manifest.json").write_text(
        json.dumps(
            {
                str(p.relative_to(results)): sha(p.read_bytes())
                for p in sorted(results.rglob("*"))
                if p.is_file() and p.name != "manifest.json"
            },
            indent=2,
        )
        + "\n"
    )
    print("Both collective probe payloads, datasets, sources and native MFMA assembly audited")


if __name__ == "__main__":
    main()
