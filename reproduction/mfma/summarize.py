"""Reconstruct MFMA proof statements and audit regenerated data plus both GPU archives."""

import argparse
import hashlib
import json
from pathlib import Path
import re
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


def audit(evidence):
    sys.path.insert(0, str(ROOT.parents[1]))
    from lark_kernels import certificate, mfma
    from lark_kernels.ir import Task
    from lark_kernels.spec import read_spec
    from reproduction.mfma.run import MUTANTS, source_files

    run = evidence / "cpu-20261110"
    report = json.loads((run / "results.json").read_text())
    require(report["status"] == "finished" and report["model_calls"] == 0, "CPU study unfinished")
    require(not report["original_paper_fully_reproduced"], "Scope differs")
    require(source_files() == report["source_files"], "Frozen study sources differ")
    manifest = {
        str(f.relative_to(run)): sha(f)
        for f in run.rglob("*")
        if f.is_file() and f.name != "manifest.json" and ".lake" not in f.parts
    }
    require(manifest == json.loads((run / "manifest.json").read_text()), "CPU manifest differs")
    require([r["case"] for r in report["certificates"]] == ["gemm16"], "Certificate set differs")
    fixture, dest = ROOT / "cases/gemm16", run / "certificates/gemm16"
    for f in ("kernel.hip", "reference.py", "task.json"):
        require(
            (fixture / f).read_bytes() == (dest / f).read_bytes(), "Certified fixture bytes differ"
        )
    task = Task.read(dest / "task.json")
    tr = mfma.translate((dest / "kernel.hip").read_bytes().decode(), task)
    spec = read_spec((dest / "reference.py").read_text(), task)
    proposal = json.loads((dest / "proposal.json").read_text())
    require(
        (dest / "Main.lean").read_text() == mfma.render(task, tr, spec, proposal),
        "Source-bound theorem differs",
    )
    cert = json.loads((dest / "report.json").read_text())
    require(
        cert["status"] == "verified" and cert["model_profile"] == mfma.PROFILE,
        "Certificate did not verify",
    )
    require(set(cert["files"]) == mfma.FILES, "Certificate file set differs")
    require(cert["accesses"] == 1024, "Access count differs")
    for f, expected in cert["files"].items():
        require(sha(dest / f) == expected, "Certificate manifest differs")
    require(
        cert["models"]
        == {
            "nonlinear": sha(certificate.model_path(True)),
            "mfma": sha(mfma.library()),
            "tile": sha(mfma.library("MFMATile.lean")),
        },
        "Embedded model hashes differ",
    )
    for name in ("lean-1.log", "independent-recheck.log"):
        log = (dest / name).read_text()
        require(
            "LarkCertificate.kernel_eq_spec_pre" in log
            and "error:" not in log
            and "sorryAx" not in log,
            "Lean verification failed",
        )
    require(sorted(r["name"] for r in report["mutants"]) == sorted(MUTANTS), "Mutant set differs")
    for row in report["mutants"]:
        dest = run / "mutants" / row["name"]
        filename, before, after = MUTANTS[row["name"]]
        for name in ("kernel.hip", "reference.py", "task.json"):
            expected = (fixture / name).read_text()
            if name == filename:
                expected = expected.replace(before, after)
            require((dest / name).read_text() == expected, "Mutation source/reference differs")
        tr = mfma.translate((dest / "kernel.hip").read_bytes().decode(), task)
        spec = read_spec((dest / "reference.py").read_text(), task)
        expected = {
            "segments": certificate.default_segments(tr.program),
            "proofs": dict(mfma.DEFAULT_PROOFS),
        }
        require(
            json.loads((dest / "proposal.json").read_text()) == expected,
            "Mutation proposal differs",
        )
        require(
            (dest / "Main.lean").read_text() == mfma.render(task, tr, spec, expected),
            "Mutation theorem differs",
        )
        log = (dest / "lean.log").read_text()
        require(
            "error:" in log and "Lean timed out" not in log and not row["python_preflight_used"],
            "Direct Lean rejection missing",
        )
    hardware = []
    with tempfile.TemporaryDirectory(prefix="lark-mfma-evidence-") as tmp:
        tmp = Path(tmp)
        data = tmp / "data"
        extract(evidence / "gpu-input.tar.gz", data)
        manifest = json.loads((data / "manifest.json").read_text())
        for name, expected in manifest["files"].items():
            require(sha(data / name) == expected, "GPU input differs")
        require(manifest["generator_sha256"] == sha(ROOT / "prepare_gpu.py"), "Generator differs")
        require(
            manifest["trials"] == 65824
            and manifest["comparisons"] == 16850944
            and manifest["independent_ast_reference_checks"] == 304,
            "Dataset coverage differs",
        )
        for name in ("kernel.hip", "reference.py", "task.json"):
            require(
                (data / "cases/gemm16" / name).read_bytes() == (fixture / name).read_bytes(),
                "GPU source differs from certified fixture",
            )
        for name in ("driver.hip", "run_gpu.py"):
            require(
                (data / name).read_bytes() == (ROOT / name).read_bytes(),
                "GPU harness differs from frozen source",
            )
        regenerated = tmp / "regenerated"
        generated = subprocess.run(
            [sys.executable, str(ROOT / "prepare_gpu.py"), "--output", str(regenerated)],
            capture_output=True,
            text=True,
            timeout=120,
        )
        require(
            generated.returncode == 0,
            "Independent dataset regeneration failed: " + generated.stderr,
        )
        require(
            (regenerated / "manifest.json").read_bytes() == (data / "manifest.json").read_bytes(),
            "Regenerated dataset manifest differs",
        )
        for name in manifest["files"]:
            require(sha(regenerated / name) == sha(data / name), "Regenerated dataset bytes differ")
        for host in ("mi350", "mi350-2"):
            target = tmp / host
            extract(evidence / (host + "-artifacts.tar.gz"), target)
            recorded_data, run = target / "evidence/input", target / "evidence/output"
            require(
                (recorded_data / "manifest.json").read_bytes()
                == (data / "manifest.json").read_bytes(),
                "Remote dataset manifest differs",
            )
            for name, expected in manifest["files"].items():
                require(sha(recorded_data / name) == expected, "Remote input differs")
            result = json.loads((run / "results.json").read_text())
            require(
                result["status"] == "passed"
                and result["comparisons"] == 16850944
                and result["mismatches"] == 0,
                "GPU result differs",
            )
            require(
                result["input_manifest_sha256"] == sha(data / "manifest.json"),
                "GPU dataset binding differs",
            )
            require(
                result["runner_sha256"] == sha(data / "run_gpu.py")
                and result["binary_sha256"] == sha(run / "driver"),
                "GPU executable binding differs",
            )
            require(
                result["actual_sha256"]
                == sha(run / "actual.bin")
                == sha(data / "expected.bin")
                == result["expected_sha256"],
                "GPU output bits differ",
            )
            device = result["device"]
            require(
                device["trials"] == 65824
                and device["warp"] == 64
                and device["architecture"].startswith("gfx950"),
                "GPU geometry differs",
            )
            require(
                device["inputs_unchanged"] and device["per_tile_guard_zones_unchanged"],
                "GPU input or guards changed",
            )
            for name, expected in result["assembly_sha256"].items():
                require(sha(run / name) == expected, "Assembly changed")
            require(
                result["native_mfma_assembly_present"]
                and any(
                    re.search(r"v_mfma_f32_16x16x16_?f16", (run / name).read_text())
                    for name in result["assembly_sha256"]
                ),
                "Native MFMA instruction missing",
            )
            hardware.append(
                {
                    "host": host,
                    "trials": 65824,
                    "comparisons": 16850944,
                    "mismatches": 0,
                    "same_source_as_certificate": True,
                    "per_tile_inputs_and_guards_unchanged": True,
                    "native_mfma_assembly_present": True,
                }
            )
    return {
        "status": "source-bound-proof-mutations-regenerated-dataset-and-gpu-evidence-audited",
        "original_paper_fully_reproduced": False,
        "certificates": 1,
        "independent_lean_rechecks_recorded": 1,
        "direct_lean_rejections": 4,
        "mutant_timeouts": 0,
        "independent_ast_reference_checks": 304,
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
        for name, expected in validation["archives"].items():
            require(sha(evidence / name) == expected, "Evidence archive changed: " + name)
        with tempfile.TemporaryDirectory(prefix="lark-mfma-source-") as tmp:
            extract(evidence / "source.tar.gz", Path(tmp))
            script = Path(tmp) / "source/reproduction/mfma/summarize.py"
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
    summary = audit(evidence)
    args.output.write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary))


if __name__ == "__main__":
    main()
