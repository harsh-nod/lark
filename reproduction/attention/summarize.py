"""Bind archived attention statements, exact GPU sources and both device records."""

import hashlib
import json
from pathlib import Path
import sys
import tarfile

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from lark_kernels import attention
from lark_kernels.frontend import translate

ROOT = Path(__file__).resolve().parent


def sha(x):
    return hashlib.sha256(x).hexdigest()


def read(t, name):
    try:
        return t.extractfile(name).read()
    except KeyError:
        return t.extractfile("./" + name).read()


def main():
    results = ROOT / "results"
    cpu = json.loads((results / "cpu.json").read_text())
    assert (
        cpu["status"] == "passed"
        and cpu["model_calls"] == 0
        and cpu["models"] == attention.model_hashes()
    )
    assert len(cpu["baselines"]) == 4 and len(cpu["scaling"]) == 4 and len(cpu["mutants"]) == 4
    with tarfile.open(results / "cpu-artifacts.tar.gz") as t:
        for row in cpu["baselines"] + cpu["scaling"]:
            prefix = row["key"] + "/"
            values = {n: read(t, prefix + n).decode() for n in attention.SOURCE_FILES}
            tasks, trs = attention.prepare(values)
            theorem = attention.render(tasks, trs).encode()
            assert (
                theorem == read(t, prefix + "Main.lean") and sha(theorem) == row["theorem_sha256"]
            )
            assert row["status"] == "verified" and row["rechecked"]
            assert row["attention_dimensions"] == list(attention.dimensions(tasks))
            assert row["source_hashes"] == {n: sha(v.encode()) for n, v in values.items()}
        tasks, trs = attention.prepare(
            {n: read(t, "baselines/gqa/hip/" + n).decode() for n in attention.SOURCE_FILES}
        )
        for row in cpu["mutants"]:
            prefix = "mutants/" + row["name"] + "/"
            source, theorem = read(t, prefix + "kernel.hip"), read(t, prefix + "Main.lean")
            changed = trs.copy()
            changed[row["stage"]] = translate(source.decode(), tasks[row["stage"]])
            assert not row["accepted"] and not row["timed_out"]
            assert sha(source) == row["source_sha256"] and sha(theorem) == row["theorem_sha256"]
            assert attention.render(tasks, changed).encode() == theorem
            assert "tactic 'rfl' failed" in read(t, prefix + "lean.log").decode()
    with tarfile.open(results / "cpu-source-snapshot.tar.gz") as t:
        assert sha(read(t, "reproduction/attention/run_cpu.py")) == cpu["runner_sha256"]
    hosts = []
    with tarfile.open(results / "device-source-bundle.tar.gz") as t:
        for host in ("mi350", "mi350-2"):
            gpu = json.loads((results / (host + ".json")).read_text())
            assert gpu["status"] == "passed" and gpu["model_calls"] == 0
            for key, name in (
                ("runner_sha256", "reproduction/attention/run_gpu.py"),
                ("dataset_sha256", "cases.json"),
                ("tensor_data_sha256", "tensors.bin"),
                ("wrapper_sha256", "certified.hip"),
                ("certificate_index_sha256", "certificate-index.json"),
            ):
                assert sha(read(t, name)) == gpu[key]
            assert [c["key"] for c in gpu["cases"]] == ["dense", "gqa"]
            for case in gpu["cases"]:
                baseline = next(
                    r for r in cpu["baselines"] if r["key"] == "baselines/" + case["key"] + "/hip"
                )
                cert = case["certificate"]
                assert (
                    cert["model_hashes"] == cpu["models"]
                    and cert["theorem_sha256"] == baseline["theorem_sha256"]
                    and cert["source_hashes"] == baseline["source_hashes"]
                )
                trials = case["trials"]
                assert len(trials) == 10 and all(
                    r["inputs_unchanged"] and r["guard_zones_unchanged"] for r in trials
                )
                expected = {"dense": (327680, 327680, 655360), "gqa": (2621440, 655360, 3276800)}[
                    case["key"]
                ]
                counts = tuple(
                    sum(r[k] for r in trials)
                    for k in ("intermediate_comparisons", "final_comparisons", "scalar_comparisons")
                )
                assert counts == expected
                hosts.append(
                    f"| {host} | {case['key']} | 10 | {counts[0]:,} | {counts[1]:,} | passed |"
                )
    scaling = [
        "| "
        + " | ".join(map(str, r["attention_dimensions"]))
        + f" | {r['status']} | {r['verify_seconds']:.3f} | {r['main_bytes']:,} |"
        for r in cpu["scaling"]
    ]
    (ROOT / "RESULTS.md").write_text(
        """# Full-size dense SDPA and GQA results

Run date: 2026-11-09. **Independent partial reproduction; zero model calls in this study.**
[Method](README.md), [evidence](results/), [paper coverage](../COVERAGE.md).

- **4/4 full-size certificates verified and independently rechecked**: HIP/CUDA
  dense attention Q/K/V `[1,128,256]`, and GQA Q `[8,128,64]`, K/V `[2,128,64]`.
- **4/4 scaling certificates verified and independently rechecked**, including
  4,096-token rows and 1,048,576-wide projections. Scaling arrays were not allocated.
- **4/4 changed programs unproved by Lean**, zero accepted/timeouts. Changed KV
  groups, score scale, softmax seed loop and value heads fail fixed-program equality
  after bypassing the structural screen. This checks source binding, not semantic
  diagnosis or the original mutation set.
- The theorem proves completion and race freedom of all three actual launches,
  grouped KV addressing, both FP32 intermediate buffers, every valid intermediate
  read from earlier final memories and every output, for all inputs/outside memories.

## Exact-source MI350X checks

| Host | Family | Trials passed | FP32 intermediate comparisons | FP16 final comparisons | Inputs / guards |
| --- | --- | ---: | ---: | ---: | --- |
"""
        + "\n".join(hosts)
        + """

Each host passed 20 trials and 3,932,160 scalar comparisons. The three exact
certificate-bound HIP stages use FP16 Q/K/V, FP32 scaled scores and row softmax,
then FP16 output. Every intermediate is checked against CPU PyTorch at rtol=2e-5,
atol=2e-6; final outputs use rtol=atol=0.01. Three inputs stayed byte-identical;
all six allocations retained 128-byte prefix/suffix guards. Probe files/extents
and actual compiled wrappers are SHA-256-bound. CUDA certificates were checked
by CPU Lean without NVIDIA execution.

## Symbolic scaling

Fresh verification plus independent recheck per row. Timings include elaboration
while other checks ran concurrently.

| Query heads | KV heads | Sequence | Dimension | Outcome | Verify seconds | Standalone Lean bytes |
| ---: | ---: | ---: | ---: | --- | ---: | ---: |
"""
        + "\n".join(scaling)
        + """

These are three-launch scalar, noncausal dense SDPA/GQA adaptations. The dense
case covers the paper's attention workload shape, not the FlashAttention online
softmax algorithm, optimized original kernel or PTX proof. No optimized-speedup,
H100 timing, original model pass-rate or original token-cost claim is made.
Small tests compare the entire connected IR with the independent tensor reader,
including scale, max initialization, grouping and precision boundaries.

Arithmetic and half conversions are abstract; finite numerical checks are separate.
Source/reference formalization, host layouts, ordered launches/pointer wiring,
hardware correspondence and the external race-free-phase/GPU-interleaving link
remain trusted. The host HIP runtime is outside the theorem.
"""
    )
    (results / "validation.json").write_text(
        json.dumps(
            {
                "status": "passed",
                "current_statements_match_archived": True,
                "cpu_runner_matches_snapshot": True,
                "device_source_hashes_match": True,
                "models": attention.model_hashes(),
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
    print("Archived attention statements, intermediate wiring and both devices agree")


if __name__ == "__main__":
    main()
