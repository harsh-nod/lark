"""Regenerate the result table after checking archived proof and device bindings."""

import hashlib
import json
from pathlib import Path
import sys
import tarfile

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from lark_kernels import gemv
from lark_kernels.frontend import translate

ROOT = Path(__file__).resolve().parent


def sha(payload):
    return hashlib.sha256(payload).hexdigest()


def main():
    results = ROOT / "results"
    cpu = json.loads((results / "cpu.json").read_text())
    assert cpu["status"] == "passed" and cpu["model_calls"] == 0
    assert cpu["models"] == gemv.model_hashes()
    assert len(cpu["baselines"]) == 2 and len(cpu["scaling"]) == 4
    assert len(cpu["mutants"]) == 3
    assert all(not r["accepted"] and not r["timed_out"] for r in cpu["mutants"])
    with tarfile.open(results / "cpu-artifacts.tar.gz") as archive:
        for row in cpu["baselines"] + cpu["scaling"]:
            prefix = "./" + row["key"] + "/"

            def get(name):
                return archive.extractfile(prefix + name).read().decode()

            task, tr = gemv.prepare(*(get(x) for x in ("kernel.cu", "reference.py", "task.json")))
            statement = gemv.render(task, tr)
            assert row["status"] == "verified" and row["rechecked"]
            assert statement == get("Main.lean")
            assert sha(statement.encode()) == row["theorem_sha256"]
        task = gemv.parse_task((ROOT / "cases/hip/task.json").read_text())
        for row in cpu["mutants"]:
            prefix = "./mutants/" + row["name"] + "/"
            source = archive.extractfile(prefix + "kernel.hip").read()
            statement = archive.extractfile(prefix + "Main.lean").read()
            assert sha(source) == row["source_sha256"]
            assert sha(statement) == row["theorem_sha256"]
            assert gemv.render(task, translate(source.decode(), task)).encode() == statement
            assert "segmentation_data" in archive.extractfile(prefix + "lean.log").read().decode()
    with tarfile.open(results / "cpu-source-snapshot.tar.gz") as archive:
        assert sha(archive.extractfile("reproduction/reduction/run_cpu.py").read()) == cpu["runner_sha256"]
    hosts = []
    with tarfile.open(results / "device-source-bundle.tar.gz") as archive:
        for host in ("mi350", "mi350-2"):
            gpu = json.loads((results / (host + ".json")).read_text())
            assert gpu["status"] == "passed" and gpu["model_calls"] == 0
            for key, filename in [
                ("runner_sha256", "reproduction/reduction/run_gpu.py"),
                ("dataset_sha256", "cases.json"),
                ("wrapper_sha256", "certified.hip"),
                ("certificate_index_sha256", "certificate-index.json"),
            ]:
                assert sha(archive.extractfile(filename).read()) == gpu[key]
            trials = [t for c in gpu["cases"] for t in c["trials"]]
            assert len(trials) == 10
            assert all(t["inputs_unchanged"] and t["guard_zones_unchanged"] for t in trials)
            assert sum(t["output_comparisons"] for t in trials) == 5120
            cert = gpu["cases"][0]["certificate"]
            assert cert["model_hashes"] == cpu["models"]
            assert cert["theorem_sha256"] == cpu["baselines"][0]["theorem_sha256"]
            hosts.append(f"| {host} | {gpu['device']} | 10 | 5,120 | passed |")
    scaling = [
        f"| {r['matrix_shape'][0]} | {r['matrix_shape'][1]} | {r['status']} | "
        f"{r['verify_seconds']:.3f} | {r['main_bytes']} |"
        for r in cpu["scaling"]
    ]
    text = """# Full-size GEMV results

Run date: 2026-11-09. **Independent partial reproduction; zero model calls.**
[Method and commands](README.md), [raw evidence](results/),
[full paper coverage](../COVERAGE.md).

- **2/2 full-size certificates verified and independently rechecked**: HIP and
  CUDA FP16 matrix-vector multiplication, `[512,1024] @ [1024,1] -> [512,1]`.
- **4/4 reduction-scaling certificates verified and independently rechecked**,
  including reduction length 1,048,576. Large proof-only arrays were not allocated.
- **3/3 changed programs unproved by Lean**, zero accepted mutants or timeouts.
  The structural frontend guard was bypassed: arithmetic, address and loop-bound
  changes fail equality with the fixed proved program (`segmentation_data`).
  This is a source-binding check, not the paper's semantic-falsity/diagnosis study.
- The generic counted-loop/grid proof concludes the existing machine's `Correct`:
  completion, race freedom, every output, all inputs and arbitrary outside memory.

## Exact-source MI350X checks

| Host | Device | Trials passed | Output comparisons | Input bytes / guards |
| --- | --- | ---: | ---: | --- |
""" + "\n".join(hosts) + """

Each host compiled the same certificate-bound HIP bytes. Six normal-random
trials and zero, constant, alternating-sign and uniform probes check every output
against CPU PyTorch with rtol=atol=0.01. Inputs and 128-byte guards before/after
all three allocations were unchanged. These probes are not exhaustive numerical
conformance or performance measurements. CUDA was checked by Lean on the CPU.

## Counted-loop scaling

One fresh proof and independent recheck per row; proof times include Python and
Lean elaboration while other CPU validation ran concurrently.

| Rows M | Reduction K | Outcome | Verify seconds | Standalone Lean bytes |
| ---: | ---: | --- | ---: | ---: |
""" + "\n".join(scaling) + """

The last row describes 536,870,912 matrix cells symbolically. Only the 512×1024
case ran on hardware. The program uses one scalar thread per row and a serial
FP32 accumulator, with FP16 inputs/output. It differs from the authors' optimized
kernel, launch and proof harness. No original model pass rate, token cost,
optimized speedup or H100 result is reproduced by this study.

Arithmetic is abstract in the formal theorem; floating-point calibration and
numerical comparisons remain separate. Source lowering, the closed Torch AST
formalizer, the host interface and race-free-phase hardware correspondence are
trusted. See the coverage ledger for all remaining paper results.
"""
    (ROOT / "RESULTS.md").write_text(text)
    (results / "validation.json").write_text(json.dumps({
        "status": "passed", "current_statements_match_archived": True,
        "cpu_runner_matches_snapshot": True, "device_source_hashes_match": True,
        "models": gemv.model_hashes(),
    }, indent=2) + "\n")
    manifest = {str(p.relative_to(results)): sha(p.read_bytes())
                for p in sorted(results.rglob("*"))
                if p.is_file() and p.name != "manifest.json"}
    (results / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print("Archived statements, CPU runner, device bindings and counts agree")


if __name__ == "__main__":
    main()
