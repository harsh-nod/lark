"""Regenerate frozen statements/inputs and audit both raw GPU output streams.

This performs no new Lean, GPU or model calls. CPU regeneration requires the
recorded PyTorch/NumPy versions. The worker imports the archived implementation.
"""

import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import shutil
import subprocess
import sys
import tarfile
import tempfile


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def read(p):
    return json.loads(p.read_text())


def safe_path(name):
    p = PurePosixPath(name)
    require(not p.is_absolute() and ".." not in p.parts and str(p) == name, "Unsafe path")
    return p


def unpack(archive, dest):
    with tarfile.open(archive) as tar:
        seen = set()
        for member in tar:
            p = safe_path(member.name)
            require(member.isfile() and str(p) not in seen, "Unexpected archive member")
            seen.add(str(p))
            out = dest / p
            out.parent.mkdir(parents=True, exist_ok=True)
            out.write_bytes(tar.extractfile(member).read())


def files(root):
    return {p.relative_to(root).as_posix() for p in root.rglob("*") if p.is_file()}


def manifest(root, records, exact=False):
    for name, digest in records.items():
        require(sha(root / safe_path(name)) == digest, "Evidence hash differs: " + name)
    if exact:
        require(files(root) == set(records), "Unexpected evidence files")


def audit_axioms(log):
    require("error:" not in log and "sorryAx" not in log, "Positive Lean error/admission")
    for tag in (
        "segmentation_data",
        "segmentation",
        "race_free",
        "segment_equivalence",
        "kernel_eq_spec",
        "kernel_eq_spec_pre",
    ):
        lines = re.findall(r"^'LarkCertificate\." + tag + r"' (.+)$", log, re.M)
        require(len(lines) == 1, "Missing/ambiguous axiom audit: " + tag)
        line = lines[0]
        if line == "does not depend on any axioms":
            continue
        match = re.fullmatch(r"depends on axioms: \[([^]]*)\]", line)
        require(match is not None, "Invalid axiom audit")
        require(
            set(match[1].split(", ")) <= {"propext", "Classical.choice", "Quot.sound"},
            "Nonstandard axioms",
        )


def statement_worker(cpu):
    # This copy runs inside the extracted, hash-checked source archive.
    root = Path(__file__).resolve().parents[2]
    sys.path.insert(0, str(root))
    from lark_kernels import silu
    from lark_kernels.frontend import translate
    from lark_kernels.ir import Node

    record = read(cpu / "results.json")
    for entry in record["baselines"]:
        dest = cpu / (entry["key"] + "-" + entry["language"])
        cert = dest / "certificate"
        report = read(cert / "report.json")
        require(report["status"] == "verified" and report["source_readback"], "Bad certificate")
        require(report["model_profile"] == silu.PROFILE, "Wrong profile")
        require(report["model_hashes"] == silu.model_hashes(), "Wrong proof libraries")
        require(set(report["files"]) == silu.FILES, "Unexpected certificate files")
        manifest(cert, report["files"])
        task, tr, ref = silu.prepare(
            *((cert / n).read_bytes().decode() for n in ("kernel.cu", "reference.py", "task.json"))
        )
        require((cert / "Main.lean").read_text() == silu.render(task, tr, ref), "Statement differs")
        require(read(cert / "translation.json") == json.loads(json.dumps(tr.data())), "IR differs")
        rows, width = task.buffers[0].shape
        for key, value in {
            "rows": rows,
            "hidden": width,
            "output_elements": rows * width,
            "input_elements": rows * 2 * width,
            "block": task.block,
            "warp": task.warp,
        }.items():
            require(report[key] == entry[key] == value, "Shape/launch metadata differs")
        require(sha(cert / "Main.lean") == entry["theorem_sha256"], "Theorem digest differs")
        require(sha(cert / "report.json") == entry["report_sha256"], "Report digest differs")
        require((cert / "Main.lean").stat().st_size == entry["theorem_bytes"], "Size differs")
        require(report["axiom_audit"] == (cert / "lean-1.log").read_text(), "Audit log differs")
        audit_axioms(report["axiom_audit"])
        audit_axioms((dest / "fresh-check.log").read_text())

    def parse_node(data):
        return Node(data[0], tuple(parse_node(a) if isinstance(a, list) else a for a in data[1:]))

    for entry in record["mutants"]:
        dest = cpu / entry["name"]
        task = silu.parse_task((dest / "task.json").read_text())
        tr = translate((dest / "kernel.cu").read_text(), task)
        ref = parse_node(read(dest / "reference-node.json"))
        require((dest / "Main.lean").read_text() == silu.render(task, tr, ref), "Control differs")
        for file, key in (
            ("Main.lean", "theorem_sha256"),
            ("kernel.cu", "source_sha256"),
            ("lean.log", "log_sha256"),
        ):
            require(sha(dest / file) == entry[key], "Control digest differs")
    print(json.dumps({"regenerated_positive_statements": 8, "regenerated_negative_statements": 5}))


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--results", type=Path, default=Path(__file__).resolve().parent / "results")
    p.add_argument("--output", type=Path)
    p.add_argument("--frozen-statement-worker", action="store_true", help=argparse.SUPPRESS)
    args = p.parse_args()
    root = args.results.resolve()
    if args.frozen_statement_worker:
        statement_worker(root)
        return
    validation = read(root / "validation.json")
    manifest(root, validation["archives"])
    require(
        sha(root / "source-manifest.json") == validation["source_manifest_sha256"],
        "Source manifest differs",
    )
    cpu = root / "cpu-20261110"
    manifest(cpu, read(cpu / "manifest.json"))
    require(
        files(cpu) == set(read(cpu / "manifest.json")) | {"manifest.json"}, "Unexpected CPU files"
    )
    record = read(cpu / "results.json")
    wanted = {(k, lang) for k in ("full", "tail", "partial_wave") for lang in ("hip", "cuda")}
    wanted |= {("symbolic-grid", "hip"), ("symbolic-width", "hip")}
    require(record["status"] == "passed" and len(record["baselines"]) == 8, "CPU study incomplete")
    require({(x["key"], x["language"]) for x in record["baselines"]} == wanted, "Cases differ")
    require(
        all(x["status"] == "verified" and x["rechecked"] for x in record["baselines"]),
        "Rechecks missing",
    )
    require(sum(x["symbolic_only"] for x in record["baselines"]) == 2, "Symbolic scope differs")
    gates = {
        "wrong-input-half": "fixed-program equality",
        "overlapping-loop-step": "fixed-program equality",
        "omitted-last-column": "fixed-program equality",
        "removed-source-half-rounding": "fixed-program equality",
        "removed-reference-half-rounding": "reference-expression equality",
    }
    require(
        len(record["mutants"]) == 5 and {x["name"] for x in record["mutants"]} == set(gates),
        "Controls differ",
    )
    for control in record["mutants"]:
        require(
            not control["accepted"]
            and not control["timed_out"]
            and control["python_profile_preflight_bypassed"],
            "Control accepted/timed out",
        )
        require(control["failed_gate"] == gates[control["name"]], "Gate classification differs")
        log = (cpu / control["name"] / "lean.log").read_text()
        require(
            "error: tactic 'rfl' failed" in log, "Expected definitional-equality rejection missing"
        )
        require(
            not any(
                s in log
                for s in ("Lean timed out", "maximum recursion", "maximum number of heartbeats")
            ),
            "Control resource failure",
        )
        gate = (
            "program = LarkSilu.program shape"
            if control["failed_gate"] == "fixed-program equality"
            else "referenceResult ops input row col = LarkSilu.result shape ops input row col"
        )
        require(gate in log, "Wrong Lean rejection gate")
    hardware = []
    with tempfile.TemporaryDirectory(prefix="lark-silu-audit-") as directory:
        temp = Path(directory)
        source, packet, rebuilt = temp / "source", temp / "packet", temp / "rebuilt"
        unpack(root / "source.tar.gz", source)
        source_manifest = read(root / "source-manifest.json")
        manifest(source, source_manifest, exact=True)
        worker = source / "reproduction/production_silu/summarize.py"
        require(not worker.exists(), "Auditor must postdate the frozen experiment")
        shutil.copyfile(__file__, worker)
        result = subprocess.run(
            [sys.executable, str(worker), "--frozen-statement-worker", "--results", str(cpu)],
            cwd=source,
            capture_output=True,
            text=True,
            timeout=120,
        )
        require(
            result.returncode == 0,
            "Frozen statement replay failed: " + result.stdout + result.stderr,
        )
        unpack(root / "gpu-input.tar.gz", packet)
        inputs = packet / "input"
        stored = read(inputs / "manifest.json")
        manifest(inputs, stored["files"])
        require(files(inputs) == set(stored["files"]) | {"manifest.json"}, "Unexpected input files")
        runner = "reproduction/production_silu/run_gpu.py"
        require(
            sha(packet / "runner.py") == source_manifest[runner],
            "Runner differs from frozen source",
        )
        generator = source / "reproduction/production_silu/prepare_gpu.py"
        require(sha(generator) == stored["generator_sha256"], "Input generator differs")
        for key in ("full", "tail", "partial_wave"):
            for name in ("kernel.cu", "reference.py", "task.json", "Main.lean", "report.json"):
                require(
                    (inputs / (key + "-" + name)).read_bytes()
                    == (cpu / (key + "-hip/certificate") / name).read_bytes(),
                    "GPU certificate binding differs",
                )
        generated = subprocess.run(
            [sys.executable, str(generator), "--cpu", str(cpu), "--output", str(rebuilt)],
            cwd=source,
            capture_output=True,
            text=True,
            timeout=180,
        )
        require(
            generated.returncode == 0,
            "Frozen input regeneration failed: " + generated.stdout + generated.stderr,
        )
        require(files(rebuilt) == files(inputs), "Regenerated input file set differs")
        for name in files(inputs):
            require(
                (rebuilt / name).read_bytes() == (inputs / name).read_bytes(),
                "Regenerated input differs: " + name,
            )
        import numpy as np

        data = read(inputs / "dataset.json")
        require(
            data["ast_comparisons"] == 2966860 and data["ast_bit_differences"] == 0,
            "AST counts differ",
        )
        require(data["rounding_differences"] == 529104, "Rounding control differs")
        expected = np.frombuffer((inputs / "expected.bin").read_bytes(), dtype="<f2").astype(
            np.float64
        )
        require(
            len(expected) == 2966860 and np.isfinite(expected).all(), "Reference stream differs"
        )
        for host, gpu in (("mi350", 2), ("mi350-2", 0)):
            location = temp / host
            unpack(root / (host + "-artifacts.tar.gz"), location)
            controller = read(location / "controller.json")
            require(
                controller["host"] == host
                and controller["physical_gpu"] == gpu
                and controller["returncode"] == 0,
                "Controller failed/different GPU",
            )
            require(
                controller["transport_sha256"] == sha(root / "gpu-input.tar.gz"),
                "Transport differs",
            )
            run = location / "gpu"
            guard = read(run / "memory-guard.json")
            require(
                guard["minimum_free_fraction"] == 0.98
                and guard["free_bytes"] >= 0.98 * guard["total_bytes"],
                "Memory guard failed",
            )
            report = read(run / "results.json")
            require(
                report["status"] == "passed"
                and report["architecture"] == "gfx950"
                and report["warp"] == 64
                and report["max_threads_per_block"] == 1024,
                "Hardware contract differs",
            )
            require(
                report["input_manifest_sha256"] == sha(inputs / "manifest.json"),
                "Input manifest differs",
            )
            require(report["runner_sha256"] == source_manifest[runner], "Executed runner differs")
            for name, field in (
                ("driver.so", "binary_sha256"),
                ("adapted.bin", "adapted_sha256"),
                ("upstream.bin", "upstream_sha256"),
            ):
                require(sha(run / name) == report[field], "Raw GPU evidence digest differs")
            a, b = (run / "adapted.bin").read_bytes(), (run / "upstream.bin").read_bytes()
            require(a == b, "Raw adapted/upstream streams differ")
            require(len(a) == len(expected) * 2, "Raw output stream length differs")
            actual = np.frombuffer(a, dtype="<f2").astype(np.float64)
            errors = np.abs(actual - expected)
            require(np.isfinite(actual).all(), "Nonfinite device output")
            require(
                np.all(errors <= data["atol"] + data["rtol"] * np.abs(expected)),
                "CPU reference comparison failed",
            )
            require(
                float(errors.max()) == report["max_abs_error"] == 0.0,
                "Maximum observed error differs",
            )
            require(len(report["cases"]) == len(data["cases"]) == 3, "Device case count differs")
            for recorded, case in zip(report["cases"], data["cases"]):
                for field in ("key", "grid", "block", "warp"):
                    require(recorded[field] == case[field], "Device launch differs")
                require(len(recorded["trials"]) == case["trials"] == 10, "Trial count differs")
                require(
                    recorded["cpu_reference_comparisons"] == 20 * case["output_elements"],
                    "Case comparison count differs",
                )
                require(
                    recorded["bit_differences"]
                    == recorded["numerical_failures"]
                    == recorded["max_abs_error"]
                    == 0,
                    "Device case failed",
                )
                for index, trial in enumerate(recorded["trials"]):
                    require(
                        trial["trial"] == index
                        and trial["paired_output_values"] == case["output_elements"]
                        and trial["cpu_reference_comparisons"] == 2 * case["output_elements"],
                        "Trial metadata differs",
                    )
                    require(
                        trial["inputs_unchanged"] and trial["all_allocation_guards_unchanged"],
                        "Input/guard changed",
                    )
                    require(
                        trial["bit_differences"]
                        == trial["numerical_failures"]
                        == trial["max_abs_error"]
                        == 0,
                        "Trial failed",
                    )
            require(
                report["trials"] == 30 and report["launches_per_trial"] == 2, "Launch counts differ"
            )
            require(
                report["paired_output_values"] == 2966860
                and report["cpu_reference_comparisons"] == 5933720,
                "Comparison counts differ",
            )
            require(
                report["bit_differences"] == report["numerical_failures"] == 0,
                "Device summary failed",
            )
            hardware.append(
                {
                    "host": host,
                    "physical_gpu": gpu,
                    "trials": 30,
                    "kernel_launches": 60,
                    "adapted_outputs": 2966860,
                    "upstream_outputs": 2966860,
                    "bit_differences": 0,
                    "cpu_reference_comparisons": 5933720,
                    "numerical_failures": 0,
                    "max_abs_error": float(errors.max()),
                    "recorded_inputs_and_guards_unchanged": True,
                }
            )
    summary = {
        "status": "frozen-statements-inputs-and-raw-two-host-evidence-audited",
        "certificates": 8,
        "device_test_shape_certificates": 6,
        "symbolic_only_certificates": 2,
        "recorded_independent_lean_rechecks": 8,
        "regenerated_positive_statements": 8,
        "regenerated_negative_statements": 5,
        "direct_lean_rejections": 5,
        "mutant_timeouts": 0,
        "ast_reference_comparisons": data["ast_comparisons"],
        "outputs_changed_without_intermediate_rounding": data["rounding_differences"],
        "hardware": hardware,
        "fresh_lean_checks": 0,
        "fresh_gpu_trials": 0,
        "model_calls": 0,
        "original_paper_fully_reproduced": False,
        "scope": record["scope"],
    }
    if args.output:
        require(not args.output.exists(), "Refusing to overwrite an earlier summary")
        args.output.write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
