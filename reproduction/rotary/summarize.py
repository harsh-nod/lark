"""Check archived source/proof bindings and regenerate the RoPE result report."""

import hashlib
import json
from pathlib import Path
import sys
import tarfile

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from lark_kernels import rotary
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
    assert cpu["models"] == rotary.model_hashes()
    assert len(cpu["baselines"]) == 2 and len(cpu["scaling"]) == 4
    assert len(cpu["mutants"]) == 3
    assert all(not r["accepted"] and not r["timed_out"] for r in cpu["mutants"])
    with tarfile.open(results / "cpu-artifacts.tar.gz") as archive:
        for row in cpu["baselines"] + cpu["scaling"]:
            prefix = row["key"] + "/"
            task, tr = rotary.prepare(
                *(
                    read(archive, prefix + name).decode()
                    for name in ("kernel.cu", "reference.py", "task.json")
                )
            )
            statement = rotary.render(task, tr).encode()
            assert row["status"] == "verified" and row["rechecked"]
            assert statement == read(archive, prefix + "Main.lean")
            assert sha(statement) == row["theorem_sha256"]
        task = rotary.parse_task((ROOT / "cases/hip/task.json").read_text())
        for row in cpu["mutants"]:
            prefix = "mutants/" + row["name"] + "/"
            source = read(archive, prefix + "kernel.hip")
            statement = read(archive, prefix + "Main.lean")
            assert sha(source) == row["source_sha256"]
            assert sha(statement) == row["theorem_sha256"]
            assert rotary.render(task, translate(source.decode(), task)).encode() == statement
            assert "tactic 'rfl' failed" in read(archive, prefix + "lean.log").decode()
    with tarfile.open(results / "cpu-source-snapshot.tar.gz") as archive:
        assert sha(read(archive, "reproduction/rotary/run_cpu.py")) == cpu["runner_sha256"]
    hosts = []
    with tarfile.open(results / "device-source-bundle.tar.gz") as archive:
        for host in ("mi350", "mi350-2"):
            gpu = json.loads((results / (host + ".json")).read_text())
            assert gpu["status"] == "passed" and gpu["model_calls"] == 0
            for key, name in [
                ("runner_sha256", "reproduction/rotary/run_gpu.py"),
                ("dataset_sha256", "cases.json"),
                ("tensor_data_sha256", "tensors.f16"),
                ("wrapper_sha256", "certified.hip"),
                ("certificate_index_sha256", "certificate-index.json"),
            ]:
                assert sha(read(archive, name)) == gpu[key]
            trials = [t for c in gpu["cases"] for t in c["trials"]]
            assert len(trials) == 10
            assert all(t["inputs_unchanged"] and t["guard_zones_unchanged"] for t in trials)
            assert sum(t["output_comparisons"] for t in trials) == 327680
            for case in gpu["cases"]:
                cert = case["certificate"]
                assert cert["model_hashes"] == cpu["models"]
                baseline = next(r for r in cpu["baselines"] if r["key"] == "baselines/hip")
                assert cert["theorem_sha256"] == baseline["theorem_sha256"]
            hosts.append(f"| {host} | {gpu['device']} | 10 | 327,680 | passed |")
    scaling = [
        "| "
        + " | ".join(map(str, r["rotary_shape"]))
        + f" | {r['status']} | {r['verify_seconds']:.3f} | {r['main_bytes']} |"
        for r in cpu["scaling"]
    ]
    text = (
        """# Full-size RoPE results

Run date: 2026-11-09. **Independent partial reproduction; zero model calls.**
[Method and commands](README.md), [raw evidence](results/),
[full paper coverage](../COVERAGE.md).

- **2/2 full-size certificates verified and independently rechecked**: HIP and
  CUDA FP16 interleaved RoPE at `[256,128]`, with `[256,64]` cosine/sine inputs.
- **4/4 scaling certificates verified and independently rechecked**, including
  a 2,147,483,646-cell output footprint. Larger cases are symbolic proofs; no
  arrays were allocated or executed.
- **3/3 changed programs unproved by Lean**, zero accepted mutants/timeouts.
  Arithmetic, parity and pair-index changes bypass the structural frontend
  guard and fail fixed-program equality (`segmentation_data`). This checks source
  binding; it is not the original mutant set or semantic diagnosis/channel census.
- The branch/grid induction proof concludes the existing machine's `Correct`,
  including completion, race freedom, every output, all inputs and outside memory.

## Exact-source MI350X checks

| Host | Device | Trials passed | Output comparisons | Input bytes / guards |
| --- | --- | ---: | ---: | --- |
"""
        + "\n".join(hosts)
        + """

Each host compiled the same certificate-bound HIP bytes. Six normal-random
trials and zero, constant, alternating-sign and uniform probes check all outputs
against CPU PyTorch with rtol=atol=0.01. Inputs and 128-byte guards before/after
all three allocations were unchanged. Binary probe bytes and extents are bound
by SHA-256. These are finite numerical checks, with no performance claim. CUDA
profiles were checked by Lean on the CPU, without NVIDIA execution.

## Branch/grid scaling

One fresh verification and independent recheck per row. Verification times include
Python/fresh Lean elaboration while other CPU validation ran concurrently.

| Rows M | Width D | Outcome | Verify seconds | Standalone Lean bytes |
| ---: | ---: | --- | ---: | ---: |
"""
        + "\n".join(scaling)
        + """

The scalar launch uses one thread/block per output and branches on output parity,
with FP16 inputs/output and FP32 multiplication/addition/subtraction. It differs from the authors' optimized kernel, launch
and harness. This study does not reproduce original model pass rates/token
costs, optimized speedups or H100 measurements.

The formal theorem uses abstract arithmetic and half conversions; numerical
checks remain separate. Source lowering, closed reference formalization, host
contracts and the external correspondence between race-free phases and GPU
interleavings remain trusted. The coverage ledger records the remaining results.
"""
    )
    (ROOT / "RESULTS.md").write_text(text)
    (results / "validation.json").write_text(
        json.dumps(
            {
                "status": "passed",
                "current_statements_match_archived": True,
                "cpu_runner_matches_snapshot": True,
                "device_source_hashes_match": True,
                "models": rotary.model_hashes(),
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
    print("Archived statements, CPU runner, both devices and binary probes agree")


if __name__ == "__main__":
    main()
