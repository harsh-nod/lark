"""Derive the human-readable result table and verify archived source bindings."""

import hashlib
import json
from pathlib import Path
import sys
import tarfile

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from lark_kernels import pointwise

ROOT = Path(__file__).resolve().parent


def sha(payload):
    return hashlib.sha256(payload).hexdigest()


def main():
    results = ROOT / "results"
    cpu = json.loads((results / "cpu.json").read_text())
    assert cpu["status"] == "passed" and cpu["model_calls"] == 0
    assert len(cpu["baselines"]) == len(cpu["mutants"]) == 6
    assert cpu["models"] == pointwise.model_hashes()
    with tarfile.open(results / "cpu-artifacts.tar.gz") as archive:
        for row in cpu["baselines"] + cpu["mutants"] + cpu["scaling"]:
            if row["key"].startswith("scaling/flat"):
                continue
            prefix = "./" + row["key"] + "/"

            def get(name):
                return archive.extractfile(prefix + name).read().decode()

            args = pointwise.prepare(*(get(x) for x in ("kernel.cu", "reference.py", "task.json")))
            statement = pointwise.render(*args)
            assert statement == get("Main.lean")
            assert sha(statement.encode()) == row["theorem_sha256"]
    with tarfile.open(results / "cpu-source-snapshot.tar.gz") as archive:
        runner = archive.extractfile("reproduction/pointwise/run_cpu.py").read()
        assert sha(runner) == cpu["runner_sha256"]
    host_rows = []
    with tarfile.open(results / "device-source-bundle.tar.gz") as archive:
        for host in ("mi350", "mi350-2"):
            gpu = json.loads((results / (host + ".json")).read_text())
            assert gpu["status"] == "passed" and gpu["model_calls"] == 0
            for key, filename in [
                ("runner_sha256", "reproduction/pointwise/run_gpu.py"),
                ("dataset_sha256", "cases.json"),
                ("wrapper_sha256", "certified.hip"),
                ("certificate_index_sha256", "certificate-index.json"),
            ]:
                assert sha(archive.extractfile(filename).read()) == gpu[key]
            trials = [trial for case in gpu["cases"] for trial in case["trials"]]
            assert len(trials) == 30
            assert all(t["inputs_unchanged"] and t["guard_zones_unchanged"] for t in trials)
            comparisons = sum(t["output_comparisons"] for t in trials)
            assert comparisons == 491520
            host_rows.append(
                f"| {host} | {gpu['device']} | {len(trials)} | {comparisons} | passed |"
            )
    scaling = []
    for row in cpu["scaling"]:
        status = "timeout (30 s)" if row["timed_out"] else row["status"]
        scaling.append(
            f"| {row['method']} | {row['elements']} | {status} | "
            f"{row['verify_seconds']:.3f} | {row['main_bytes']} |"
        )
    text = (
        """# Full-length pointwise results

Run date: 2026-11-09. **Independent partial reproduction; zero model calls.**
[Method and commands](README.md), [raw evidence](results/),
[full paper coverage](../COVERAGE.md).

- **6/6 full-length certificates verified and independently rechecked**:
  ReLU/SiLU/tanh-GELU, HIP and CUDA, FP16 buffers of length 16,384.
- **6/6 arithmetic mutants unproved directly by Lean**, zero timeouts or accepted
  mutants. Python expression-equality and numerical screens were bypassed.
- **8/8 inductive scaling certificates verified**, including lengths 1,048,576
  and 2,147,483,647. Large arrays were not allocated or executed.
- Existing machine definitions are unchanged. The generic induction theorem
  concludes the actual `LarkNonlinear.Correct`, including completion, race
  freedom, every output, all inputs and arbitrary outside memory.

## Exact-source MI350X validation

| Host | Device | Trials passed | Output comparisons | Input bytes / guards |
| --- | --- | ---: | ---: | --- |
"""
        + "\n".join(host_rows)
        + """

Each host used the same certificate-bound source bytes, CPU PyTorch expected
values and wrapper. Six random trials and four probes per family check every
output with rtol=atol=0.01. All 128-byte guards before and after both allocations
were unchanged. CUDA source profiles were not executed on NVIDIA hardware.

## Flat evaluator versus induction

Same source, signature, reference and machine; one independent attempt per row.
Times include fresh Lean elaboration and Python overhead, with concurrent
validation on the CPU. Flat checks have a 30-second cap. A timeout means no
certificate within that cap, not that the kernel is incorrect.

| Method | Elements | Outcome | Verify seconds | Standalone Lean bytes |
| --- | ---: | --- | ---: | ---: |
"""
        + "\n".join(scaling)
        + """

The one-thread-per-block launch is intentionally simple and differs from the
paper's optimized launch. This is a new proof-scaling experiment, not the
original LLM ablation or a speedup reproduction. Arithmetic and half conversions
are abstract operations, not IEEE proofs or numerical-error bounds. The other
14 full-size families, original PTX/production certificates, original model
outcomes/token costs, and H100 timings remain unreproduced.
"""
    )
    (ROOT / "RESULTS.md").write_text(text)
    validation = {
        "status": "passed",
        "current_statements_match_archived": True,
        "cpu_runner_matches_snapshot": True,
        "device_source_hashes_match": True,
        "models": pointwise.model_hashes(),
    }
    (results / "validation.json").write_text(json.dumps(validation, indent=2) + "\n")
    manifest = {
        str(p.relative_to(results)): sha(p.read_bytes())
        for p in sorted(results.rglob("*"))
        if p.is_file() and p.name != "manifest.json"
    }
    (results / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print("Archived statements, CPU runner, both device bindings and counts agree")


if __name__ == "__main__":
    main()
