"""Validate the archived FFN source/pipeline statements and both device records."""

import hashlib
import json
from pathlib import Path
import sys
import tarfile

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from lark_kernels import feedforward
from lark_kernels.frontend import translate

ROOT = Path(__file__).resolve().parent
NAMES = ("up.cu", "down.cu", "reference.py", "up-task.json", "down-task.json")


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
        and cpu["models"] == feedforward.model_hashes()
    )
    assert len(cpu["baselines"]) == 2 and len(cpu["scaling"]) == 3 and len(cpu["mutants"]) == 3
    with tarfile.open(results / "cpu-artifacts.tar.gz") as t:
        for row in cpu["baselines"] + cpu["scaling"]:
            prefix = row["key"] + "/"
            values = [read(t, prefix + n) for n in NAMES]
            tasks, trs = feedforward.prepare(*(x.decode() for x in values))
            theorem = feedforward.render(tasks, trs).encode()
            assert (
                theorem == read(t, prefix + "Main.lean") and sha(theorem) == row["theorem_sha256"]
            )
            assert row["status"] == "verified" and row["rechecked"]
            assert row["ffn_dimensions"] == list(feedforward.dimensions(tasks))
            assert row["source_hashes"] == dict(zip(NAMES, map(sha, values)))
        baseline = next(r for r in cpu["baselines"] if r["key"] == "baselines/hip")
        tasks, trs = feedforward.prepare(*(read(t, "baselines/hip/" + n).decode() for n in NAMES))
        for row in cpu["mutants"]:
            prefix = "mutants/" + row["name"] + "/"
            source = read(t, prefix + "kernel.hip")
            theorem = read(t, prefix + "Main.lean")
            changed = trs.copy()
            changed[row["stage"]] = translate(source.decode(), tasks[row["stage"]])
            assert not row["accepted"] and not row["timed_out"]
            assert sha(source) == row["source_sha256"] and sha(theorem) == row["theorem_sha256"]
            assert feedforward.render(tasks, changed).encode() == theorem
            log = read(t, prefix + "lean.log").decode()
            assert "error: application type mismatch" in log
            assert (
                "upProgram = LarkDotMap.program chain.first"
                if row["stage"] == 0
                else "downProgram = LarkDotMap.program chain.second"
            ) in log
    with tarfile.open(results / "cpu-source-snapshot.tar.gz") as t:
        assert sha(read(t, "reproduction/feedforward/run_cpu.py")) == cpu["runner_sha256"]
    hosts = []
    with tarfile.open(results / "device-source-bundle.tar.gz") as t:
        for host in ("mi350", "mi350-2"):
            gpu = json.loads((results / (host + ".json")).read_text())
            assert gpu["status"] == "passed" and gpu["model_calls"] == 0
            for key, name in (
                ("runner_sha256", "reproduction/feedforward/run_gpu.py"),
                ("dataset_sha256", "cases.json"),
                ("tensor_data_sha256", "tensors.f16"),
                ("wrapper_sha256", "certified.hip"),
                ("certificate_index_sha256", "certificate-index.json"),
            ):
                assert sha(read(t, name)) == gpu[key]
            assert len(gpu["cases"]) == 1
            case = gpu["cases"][0]
            trials = case["trials"]
            assert case["key"] == "ffn" and len(trials) == 10
            assert case["certificate"]["model_hashes"] == cpu["models"]
            assert case["certificate"]["theorem_sha256"] == baseline["theorem_sha256"]
            assert case["certificate"]["source_hashes"] == baseline["source_hashes"]
            assert all(r["inputs_unchanged"] and r["guard_zones_unchanged"] for r in trials)
            assert sum(r["intermediate_comparisons"] for r in trials) == 655360
            assert sum(r["final_comparisons"] for r in trials) == 163840
            assert sum(r["scalar_comparisons"] for r in trials) == 819200
            hosts.append(f"| {host} | {gpu['device']} | 10 | 655,360 | 163,840 | passed |")
    scaling = [
        "| "
        + " | ".join(map(str, r["ffn_dimensions"]))
        + f" | {r['status']} | {r['verify_seconds']:.3f} | {r['main_bytes']:,} |"
        for r in cpu["scaling"]
    ]
    (ROOT / "RESULTS.md").write_text(
        """# Full-size two-launch FFN results

Run date: 2026-11-09. **Independent partial reproduction; zero model calls in this study.**
[Method and commands](README.md), [evidence](results/), [paper coverage](../COVERAGE.md).

- **2/2 full-size certificates verified and independently rechecked**: HIP/CUDA
  `[64,256] @ [256,1024]`, ReLU, FP16 intermediate, then `@ [1024,256]` and FP16 output.
- **3/3 scaling certificates verified and independently rechecked**, including
  a million-term first product and a million-cell intermediate/final footprint.
  Larger cases are symbolic proofs without allocating or executing those arrays.
- **3/3 changed programs unproved by Lean**, zero accepted mutants/timeouts.
  Missing ReLU, changed accumulation and changed second-stage addressing fail
  fixed-program equality after bypassing the structural screen. These check
  source binding, not the original mutation set or semantic diagnosis.
- The final theorem proves completion and race freedom of both actual-machine
  launches, every valid intermediate read from the first final memory, and every
  final output, for all inputs and arbitrary outside memory.

## Exact-source MI350X checks

| Host | Device | Trials passed | Intermediate comparisons | Final comparisons | Inputs / guards |
| --- | --- | ---: | ---: | ---: | --- |
"""
        + "\n".join(hosts)
        + """

Both hosts compiled the same two certificate-bound HIP sources. Ten trials check
all intermediate and final outputs against CPU PyTorch, rtol=atol=0.01. Three
input allocations were unchanged and all five allocations retained their
128-byte prefix/suffix guards. Binary probe extents and full files are SHA-256-bound.
CUDA profiles were checked by CPU Lean without NVIDIA execution.

## Pipeline scaling

One fresh verification plus independent recheck per row. Verify timings include
fresh Python/Lean elaboration while other CPU checks ran concurrently.

| Rows M | Input K | Hidden H | Output N | Outcome | Verify seconds | Standalone Lean bytes |
| ---: | ---: | ---: | ---: | --- | ---: | ---: |
"""
        + "\n".join(scaling)
        + """

Each kernel uses one scalar thread/block per output, serial FP32 accumulation and
FP16 storage. The programs/launches differ from the authors' optimized kernels.
This is a full-size independent FFN adaptation, without an original PTX/H100,
model pass-rate, token-cost or performance reproduction claim.

Arithmetic and half conversions are abstract; numerical checks remain separate.
Source/reference formalization, host layouts, ordered launches and pointer
wiring, hardware correspondence and the external race-free-phase/GPU-interleaving
connection remain trusted. The host HIP runtime is outside the formal theorem.
"""
    )
    (results / "validation.json").write_text(
        json.dumps(
            {
                "status": "passed",
                "current_statements_match_archived": True,
                "cpu_runner_matches_snapshot": True,
                "device_source_hashes_match": True,
                "models": feedforward.model_hashes(),
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
    print("Archived FFN statements, intermediate wiring, CPU runner and both devices agree")


if __name__ == "__main__":
    main()
