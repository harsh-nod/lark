"""Check archived normalization statements, source bindings and device evidence."""

import hashlib
import json
from pathlib import Path
import sys
import tarfile

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from lark_kernels import normalization
from lark_kernels.frontend import translate

ROOT = Path(__file__).resolve().parent


def sha(payload):
    return hashlib.sha256(payload).hexdigest()


def read(archive, name):
    try:
        return archive.extractfile(name).read()
    except KeyError:
        return archive.extractfile("./" + name).read()


def main():
    results = ROOT / "results"
    cpu = json.loads((results / "cpu.json").read_text())
    assert cpu["status"] == "passed" and cpu["model_calls"] == 0
    assert cpu["models"] == normalization.model_hashes()
    assert len(cpu["baselines"]) == 6 and len(cpu["scaling"]) == 9
    assert len(cpu["mutants"]) == 3
    assert all(not r["accepted"] and not r["timed_out"] for r in cpu["mutants"])
    with tarfile.open(results / "cpu-artifacts.tar.gz") as archive:
        for row in cpu["baselines"] + cpu["scaling"]:
            prefix = row["key"] + "/"
            task, tr, kind = normalization.prepare(
                *(
                    read(archive, prefix + f).decode()
                    for f in ("kernel.cu", "reference.py", "task.json")
                )
            )
            statement = normalization.render(task, tr, kind).encode()
            assert row["status"] == "verified" and row["rechecked"]
            assert statement == read(archive, prefix + "Main.lean")
            assert sha(statement) == row["theorem_sha256"]
            assert row["normalization_kind"] == kind and row["elements"] == task.grid
        kinds = {"square-arithmetic": "rms", "variance-centering": "layer", "max-start": "softmax"}
        for row in cpu["mutants"]:
            kind = kinds[row["name"]]
            case = ROOT / "cases" / kind / "hip"
            task, _, _ = normalization.prepare(
                *((case / f).read_text() for f in ("kernel.hip", "reference.py", "task.json"))
            )
            prefix = "mutants/" + row["name"] + "/"
            source = read(archive, prefix + "kernel.hip")
            statement = read(archive, prefix + "Main.lean")
            assert sha(source) == row["source_sha256"] and sha(statement) == row["theorem_sha256"]
            assert (
                normalization.render(task, translate(source.decode(), task), kind).encode()
                == statement
            )
            assert "tactic 'rfl' failed" in read(archive, prefix + "lean.log").decode()
    with tarfile.open(results / "cpu-source-snapshot.tar.gz") as archive:
        assert sha(read(archive, "reproduction/normalization/run_cpu.py")) == cpu["runner_sha256"]
    hosts = []
    with tarfile.open(results / "device-source-bundle.tar.gz") as archive:
        for host in ("mi350", "mi350-2"):
            gpu = json.loads((results / (host + ".json")).read_text())
            assert gpu["status"] == "passed" and gpu["model_calls"] == 0
            for key, name in [
                ("runner_sha256", "reproduction/normalization/run_gpu.py"),
                ("dataset_sha256", "cases.json"),
                ("tensor_data_sha256", "tensors.f16"),
                ("wrapper_sha256", "certified.hip"),
                ("certificate_index_sha256", "certificate-index.json"),
            ]:
                assert sha(read(archive, name)) == gpu[key]
            assert {c["key"] for c in gpu["cases"]} == set(normalization.KINDS)
            trials = [t for c in gpu["cases"] for t in c["trials"]]
            assert len(trials) == 30
            assert all(t["inputs_unchanged"] and t["guard_zones_unchanged"] for t in trials)
            assert sum(t["output_comparisons"] for t in trials) == 491520
            for case in gpu["cases"]:
                cert = case["certificate"]
                assert cert["model_hashes"] == cpu["models"]
                baseline = next(
                    r for r in cpu["baselines"] if r["key"] == f"baselines/{case['key']}/hip"
                )
                assert cert["theorem_sha256"] == baseline["theorem_sha256"]
            hosts.append(f"| {host} | {gpu['device']} | 30 | 491,520 | passed |")
    scaling = [
        f"| {r['normalization_kind']} | {r['elements']:,} | {r['status']} | {r['verify_seconds']:.3f} | {r['main_bytes']:,} |"
        for r in cpu["scaling"]
    ]
    (ROOT / "RESULTS.md").write_text(
        """# Full-length normalization results

Run date: 2026-11-09. **Independent partial reproduction; zero model calls in this study.**
[Method and commands](README.md), [raw evidence](results/), [paper coverage](../COVERAGE.md).

- **6/6 full-length certificates verified and independently rechecked**: HIP and
  CUDA FP16 RMSNorm, LayerNorm and stable Softmax, each at length 16,384.
- **9/9 scaling certificates verified and independently rechecked**, through
  N=2^31-1 for every family. Larger cases are symbolic proofs; no arrays allocated.
- **3/3 changed programs unproved by Lean**, with zero accepted mutants/timeouts.
  Square arithmetic, variance centering and maximum initialization changes bypass
  the structural screen and fail fixed-program equality (`segmentation_data`).
  These are source-binding checks, not original mutants or semantic diagnosis.
- The reduction-loop and grid proofs conclude the unchanged machine's `Correct`:
  completion, race freedom and every output, for all inputs and outside memory.

## Exact-source MI350X checks

| Host | Device | Trials passed | Output comparisons | Input bytes / guards |
| --- | --- | ---: | ---: | --- |
"""
        + "\n".join(hosts)
        + """

Each host compiled the same certificate-bound HIP bytes. Six normal-random trials
and zero, constant, alternating-sign and uniform probes compare every output with
CPU PyTorch, rtol=atol=0.01. Input bytes and 128-byte guards around both allocations
were unchanged. Full binary probes and individual extents are SHA-256-bound.
CUDA profiles were checked by CPU Lean without NVIDIA execution.

## Reduction/grid scaling

One fresh verification plus independent recheck per row. Verify timings include
fresh Python/Lean elaboration while other CPU checks ran concurrently.

| Kind | Vector length | Outcome | Verify seconds | Standalone Lean bytes |
| --- | ---: | --- | ---: | ---: |
"""
        + "\n".join(scaling)
        + """

One scalar thread/block recomputes reductions for each output, an O(N²) adaptation
with FP32 arithmetic and FP16 storage. RMSNorm/LayerNorm use eps=1e-5, no affine
parameters and population variance. Softmax subtracts the maximum before exp/sum.
The source, launch and harness differ from the authors' optimized implementations;
this study makes no optimized speedup or original model pass-rate/cost claim.

Arithmetic and half conversions are abstract in the theorem. Numerical checks
are separate. Source lowering, closed reference formalization, host contracts,
hardware correspondence and race-free-phase/GPU-interleaving correspondence
remain trusted. The coverage ledger records remaining paper results.
"""
    )
    (results / "validation.json").write_text(
        json.dumps(
            {
                "status": "passed",
                "current_statements_match_archived": True,
                "cpu_runner_matches_snapshot": True,
                "device_source_hashes_match": True,
                "models": normalization.model_hashes(),
            },
            indent=2,
        )
        + "\n"
    )
    manifest = {
        str(p.relative_to(results)): sha(p.read_bytes())
        for p in sorted(results.rglob("*"))
        if p.is_file() and p.name != "manifest.json"
    }
    (results / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print("Archived normalization statements, CPU runner and both devices agree")


if __name__ == "__main__":
    main()
