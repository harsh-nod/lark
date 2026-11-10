"""Audit source-bound shuffle proofs and exact-source GPU evidence from frozen sources."""

import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tarfile
import tempfile

ROOT = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition, message):
    if not condition:
        raise ValueError(message)


def extract(bundle, dest):
    with tarfile.open(bundle) as archive:
        archive.extractall(dest, filter="data")


def audit(root, gpu_input, gpu_archives):
    # Executed only in the isolated frozen-source subprocess.
    sys.path.insert(0, str(ROOT.parents[1]))
    from lark_kernels import certificate, collective
    from lark_kernels.ir import Refusal, Task
    from lark_kernels.spec import read_spec
    from reproduction.shuffle.run import MUTANTS, source_files

    report = json.loads((root / "results.json").read_text())
    require(report["status"] == "finished", "CPU study unfinished")
    require(
        report["model_calls"] == 0 and not report["original_paper_fully_reproduced"],
        "Scope differs",
    )
    require(source_files() == report["source_files"], "Frozen run sources differ")
    actual = {
        str(f.relative_to(root)): sha(f)
        for f in root.rglob("*")
        if f.is_file() and f.name != "manifest.json" and ".lake" not in f.parts
    }
    require(actual == json.loads((root / "manifest.json").read_text()), "CPU manifest differs")
    names = [r["case"] for r in report["certificates"]]
    require(
        sorted(names) == ["broadcast8", "down8", "reverse", "up8", "xor8"], "Fixture set differs"
    )
    for name in names:
        dest, fixture = root / "certificates" / name, ROOT / "cases" / name
        for f in ("kernel.hip", "reference.py", "task.json"):
            require((dest / f).read_bytes() == (fixture / f).read_bytes(), "Fixture bytes differ")
        task = Task.read(dest / "task.json")
        tr = collective.translate((dest / "kernel.hip").read_bytes().decode(), task)
        spec = read_spec((dest / "reference.py").read_text(), task)
        proposal = json.loads((dest / "proposal.json").read_text())
        require(
            (dest / "Main.lean").read_text() == collective.render(task, tr, spec, proposal),
            "Theorem binding differs",
        )
        cert = json.loads((dest / "report.json").read_text())
        require(
            cert["status"] == "verified" and cert["model_profile"] == collective.PROFILE,
            "Certificate did not verify",
        )
        require(set(cert["files"]) == collective.FILES, "Certificate files differ")
        for f, expected in cert["files"].items():
            require(sha(dest / f) == expected, "Certificate manifest differs")
        require(
            cert["models"]
            == {
                "nonlinear": sha(certificate.model_path(True)),
                "collective": sha(collective.library()),
                "transfer": sha(collective.library("ShuffleTransfer.lean")),
            },
            "Embedded models differ",
        )
        for f in ("lean-1.log", "independent-recheck.log"):
            log = (dest / f).read_text()
            require(
                "LarkCertificate.kernel_eq_spec_pre" in log
                and "error:" not in log
                and "sorryAx" not in log,
                "Lean check failed",
            )
    require(sorted(r["name"] for r in report["mutants"]) == sorted(MUTANTS), "Mutant set differs")
    for row in report["mutants"]:
        case, before, after = MUTANTS[row["name"]]
        fixture, dest = ROOT / "cases" / case, root / "mutants" / row["name"]
        changed = (fixture / "kernel.hip").read_text().replace(before, after)
        require((dest / "kernel.hip").read_text() == changed, "Mutant source differs")
        task = Task.read(fixture / "task.json")
        tr = collective.translate(changed, task)
        spec = read_spec((fixture / "reference.py").read_text(), task)
        try:
            trace = collective.Machine(task, tr).run().trace
        except Refusal:
            trace = []
        expected = {
            "segments": certificate.default_segments(tr.program),
            "proofs": collective.default_proofs(task, tr, spec, trace),
        }
        require(
            json.loads((dest / "proposal.json").read_text()) == expected, "Mutant proposal differs"
        )
        require(
            (dest / "Main.lean").read_text() == collective.render(task, tr, spec, expected),
            "Mutant theorem differs",
        )
        log = (dest / "lean.log").read_text()
        require(
            "error:" in log and "Lean timed out" not in log and not row["python_preflight_used"],
            "Direct Lean rejection absent",
        )
    hardware = []
    with tempfile.TemporaryDirectory(prefix="lark-shuffle-data-") as tmp:
        data = Path(tmp) / "data"
        extract(gpu_input, data)
        manifest = json.loads((data / "manifest.json").read_text())
        require(
            manifest["input_generator_sha256"] == sha(ROOT / "prepare_gpu.py"),
            "Input generator differs",
        )
        for name in ("driver.hip", "run_gpu.py"):
            require(
                (data / name).read_bytes() == (ROOT / name).read_bytes(),
                "GPU harness differs from frozen source",
            )
        for f, expected in manifest["files"].items():
            require(sha(data / f) == expected, "GPU input changed")
        require([r["case"] for r in manifest["cases"]] == sorted(names), "GPU fixture set differs")
        require(len((data / "expected.bin").read_bytes()) == 3200 * 4, "GPU expected count differs")
        import struct

        inputs = struct.unpack("<640I", (data / "input.bin").read_bytes())
        expected_bits = []
        for name, row in zip(sorted(names), manifest["cases"]):
            fixture = ROOT / "cases" / name
            for f in ("kernel.hip", "reference.py", "task.json"):
                require(
                    (data / "cases" / name / f).read_bytes() == (fixture / f).read_bytes(),
                    "GPU source differs from certified source",
                )
            task = Task.read(fixture / "task.json")
            spec = read_spec((fixture / "reference.py").read_text(), task)
            require(
                row["input_indices"] == [n.args[1] for n in spec], "Reference permutation changed"
            )
            for trial in range(10):
                expected_bits.extend(inputs[trial * 64 + n.args[1]] for n in spec)
        require(
            struct.pack("<3200I", *expected_bits) == (data / "expected.bin").read_bytes(),
            "Independent expected bits differ",
        )
        for host, bundle in gpu_archives:
            target = Path(tmp) / host
            extract(bundle, target)
            run = target / "evidence/output"
            recorded_data = target / "evidence/input"
            require(
                sha(recorded_data / "manifest.json") == sha(data / "manifest.json"),
                "Remote GPU manifest differs",
            )
            for f, expected in manifest["files"].items():
                require(sha(recorded_data / f) == expected, "Remote GPU input changed")
            result = json.loads((run / "results.json").read_text())
            require(
                result["status"] == "passed"
                and result["comparisons"] == 3200
                and result["mismatches"] == 0,
                "GPU run failed",
            )
            require(
                result["input_manifest_sha256"] == sha(data / "manifest.json"),
                "GPU dataset binding differs",
            )
            require(result["runner_sha256"] == sha(data / "run_gpu.py"), "GPU runner differs")
            require(result["binary_sha256"] == sha(run / "driver"), "GPU binary differs")
            require(
                result["actual_sha256"]
                == sha(run / "actual.bin")
                == sha(data / "expected.bin")
                == result["expected_sha256"],
                "GPU output bits differ",
            )
            require(
                result["device"]["warp"] == 64
                and result["device"]["trials"] == 50
                and result["device"]["architecture"].startswith("gfx950"),
                "GPU geometry differs",
            )
            require(
                result["device"]["inputs_unchanged"] and result["device"]["guard_zones_unchanged"],
                "GPU guards changed",
            )
            for f, expected in result["assembly_sha256"].items():
                require(sha(run / f) == expected, "GPU assembly changed")
            hardware.append(
                {
                    "host": host,
                    "trials": 50,
                    "comparisons": 3200,
                    "mismatches": 0,
                    "source_files_identical_to_certificates": True,
                    "input_and_guard_bytes_unchanged": True,
                }
            )
    return {
        "status": "proof-statements-manifests-and-exact-source-gpu-evidence-audited",
        "original_paper_fully_reproduced": False,
        "certificates": 5,
        "independent_lean_rechecks_recorded": 5,
        "direct_lean_rejections": 4,
        "mutant_timeouts": 0,
        "hardware": hardware,
        "fresh_lean_rechecks_by_this_summary": 0,
        "scope": report["scope"],
    }


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--evidence", type=Path, default=ROOT / "results")
    p.add_argument("--output", type=Path, required=True)
    p.add_argument("--frozen-source-worker", action="store_true", help=argparse.SUPPRESS)
    args = p.parse_args()
    evidence = args.evidence.resolve()
    require(
        not args.output.exists() and not args.output.resolve().is_relative_to(evidence),
        "Fresh output outside evidence required",
    )
    if not args.frozen_source_worker:
        validation = json.loads((evidence / "validation.json").read_text())
        for f, expected in validation["archives"].items():
            require(sha(evidence / f) == expected, "Evidence archive changed: " + f)
        with tempfile.TemporaryDirectory(prefix="lark-shuffle-source-") as tmp:
            extract(evidence / "source.tar.gz", Path(tmp))
            script = Path(tmp) / "source/reproduction/shuffle/summarize.py"
            shutil.copyfile(Path(__file__), script)
            subprocess.run(
                [
                    sys.executable,
                    str(script),
                    "--evidence",
                    str(evidence),
                    "--output",
                    str(args.output.resolve()),
                    "--frozen-source-worker",
                ],
                cwd=Path(tmp) / "source",
                check=True,
            )
        return
    summary = audit(
        evidence / "cpu-20261110",
        evidence / "gpu-input.tar.gz",
        [(host, evidence / (host + "-artifacts.tar.gz")) for host in ("mi350", "mi350-2")],
    )
    args.output.write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary))


if __name__ == "__main__":
    main()
