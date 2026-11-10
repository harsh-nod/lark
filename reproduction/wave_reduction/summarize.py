"""Regenerate frozen statements and CPU inputs, then audit both raw GPU streams.

No new Lean, GPU or model calls are made. Input regeneration uses the recorded
PyTorch/NumPy versions. Statement regeneration imports the archived frontend.
"""

import argparse
from dataclasses import replace
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


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path):
    return json.loads(path.read_text())


def safe_path(name):
    path = PurePosixPath(name)
    require(not path.is_absolute() and ".." not in path.parts and str(path) == name, "Unsafe path")
    return path


def files(root):
    return {p.relative_to(root).as_posix() for p in root.rglob("*") if p.is_file()}


def manifest(root, records, exact=False):
    for name, digest in records.items():
        path = root / safe_path(name)
        require(not path.is_symlink() and sha(path) == digest, "Evidence hash differs: " + name)
    if exact:
        require(files(root) == set(records), "Unexpected evidence files")


def unpack(archive, dest):
    with tarfile.open(archive) as tar:
        seen = set()
        for member in tar:
            path = safe_path(member.name)
            require(member.isfile() and member.name not in seen, "Unexpected archive member")
            seen.add(member.name)
            out = dest / path
            out.parent.mkdir(parents=True, exist_ok=True)
            out.write_bytes(tar.extractfile(member).read())


def audit_axioms(log):
    require("error:" not in log and "sorryAx" not in log, "Positive Lean error/admission")
    for name in (
        "segmentation_data",
        "segmentation",
        "race_free",
        "segment_equivalence",
        "kernel_eq_spec",
        "kernel_eq_spec_pre",
    ):
        lines = re.findall(r"^'LarkCertificate\." + name + r"' (.+)$", log, re.M)
        require(len(lines) == 1, "Missing/ambiguous axiom audit")
        if lines[0] == "does not depend on any axioms":
            continue
        match = re.fullmatch(r"depends on axioms: \[([^]]*)\]", lines[0])
        require(match is not None, "Invalid axiom audit")
        require(
            set(match[1].split(", ")) <= {"propext", "Classical.choice", "Quot.sound"},
            "Nonstandard axioms",
        )


GATES = {
    "wrong-last-shuffle": ("fixed-program equality", "program = LarkCollective.WaveSum.program"),
    "last-reference-cell": ("reference-cell equality", "reference_63 ops input = reference_0"),
    "all-reference-cells-plus-one": ("canonical-reference equality", "error: unsolved goals"),
    "wrong-launch": ("actual-launch interface", "geometry = LarkCollective.WaveSum.geometry"),
}


def statement_worker(cpu):
    # This worker runs inside the hash-checked archive with its original implementation.
    root = Path(__file__).resolve().parents[2]
    sys.path.insert(0, str(root))
    from lark_kernels import collective, real_backend, wave_sum
    from lark_kernels.ir import node

    record = read(cpu / "results.json")
    cert = cpu / "certificate"
    report = read(cert / "report.json")
    pinned = {**wave_sum.libraries(), **real_backend.configuration()}
    require(report["status"] == "verified" and report["source_readback"], "Bad certificate")
    require(report["model_profile"] == wave_sum.PROFILE, "Wrong profile")
    require(set(report["files"]) == wave_sum.BASE_FILES | set(pinned), "Certificate file set")
    manifest(cert, report["files"])
    for name, content in pinned.items():
        require((cert / name).read_bytes() == content, "Proof source/configuration differs")
    require(
        report["model_hashes"]
        == {n: hashlib.sha256(c).hexdigest() for n, c in wave_sum.libraries().items()},
        "Wrong proof libraries",
    )
    require(report["mathlib_commit"] == real_backend.MATHLIB, "Wrong Mathlib pin")
    source, reference, task_source = [
        (cert / n).read_bytes().decode() for n in ("kernel.hip", "reference.py", "task.json")
    ]
    task, tr, refs = wave_sum.prepare(source, reference, task_source)
    require(
        (cert / "Main.lean").read_text() == wave_sum.render(task, tr, refs), "Statement differs"
    )
    require(read(cert / "translation.json") == json.loads(json.dumps(tr.data())), "IR differs")
    for name, expected in {"input_elements": 64, "output_elements": 64, "instructions": 16}.items():
        require(report[name] == expected, "Certificate dimensions differ")
    require(sha(cert / "Main.lean") == record["baseline"]["theorem_sha256"], "Theorem digest")
    require(sha(cert / "report.json") == record["baseline"]["report_sha256"], "Report digest")
    require(report["axiom_audit"] == (cert / "lean-1.log").read_text(), "Audit log differs")
    audit_axioms(report["axiom_audit"])
    audit_axioms((cpu / "fresh-check.log").read_text())
    for entry in record["controls"]:
        name = entry["name"]
        dest = cpu / name
        cs, ct, ctr, cr = source, task, tr, list(refs)
        if name == "wrong-last-shuffle":
            cs = source.replace("__shfl_xor(x, 1, 64)", "__shfl_xor(x, 2, 64)")
            ctr = collective.translate(cs, task)
        elif name == "last-reference-cell":
            cr[63] = node("input", 0, 0)
        elif name == "all-reference-cells-plus-one":
            cr = [node("bin", "add", r, node("lit", 1, 1)) for r in cr]
        elif name == "wrong-launch":
            ct = replace(task, block=128)
        else:
            raise ValueError("Unknown control")
        raw = json.loads(task_source)
        raw["launch"]["block"] = ct.block
        require(read(dest / "task.json") == raw, "Control task differs")
        require((dest / "kernel.hip").read_text() == cs, "Control source differs")
        require(
            (dest / "reference.py").read_text() == reference, "Control reference source differs"
        )
        require(
            read(dest / "reference-nodes.json") == [n.data() for n in cr], "Control reference AST"
        )
        require(
            (dest / "Main.lean").read_text() == wave_sum.render(ct, ctr, cr), "Control statement"
        )
        for filename, field in (
            ("Main.lean", "theorem_sha256"),
            ("kernel.hip", "source_sha256"),
            ("lean.log", "log_sha256"),
        ):
            require(sha(dest / filename) == entry[field], "Control digest differs")
    print(json.dumps({"positive_statements": 1, "negative_statements": 4}))


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
        "Source manifest",
    )
    require(
        sha(root / "controller.py") == validation["controller_sha256"],
        "Controller source",
    )
    cpu = root / "cpu-20261110"
    stored_cpu = read(cpu / "manifest.json")
    manifest(cpu, stored_cpu)
    require(files(cpu) == set(stored_cpu) | {"manifest.json"}, "Unexpected CPU files")
    record = read(cpu / "results.json")
    require(
        record["status"] == "passed" and record["baseline"]["rechecked"], "CPU study incomplete"
    )
    for name, value in {
        "certificates": 1,
        "recorded_independent_rechecks": 1,
        "direct_lean_rejections": 4,
        "model_calls": 0,
    }.items():
        require(record[name] == value, "CPU counts differ")
    require(
        len(record["controls"]) == 4 and {c["name"] for c in record["controls"]} == set(GATES),
        "Controls differ",
    )
    for control in record["controls"]:
        require(
            not control["accepted"]
            and not control["timed_out"]
            and control["python_profile_preflight_bypassed"],
            "Control accepted/timed out",
        )
        gate, text = GATES[control["name"]]
        require(control["failed_gate"] == gate, "Gate classification")
        log = (cpu / control["name"] / "lean.log").read_text()
        require("error:" in log and text in log, "Wrong rejection gate")
        require(
            not any(
                s in log
                for s in ("Lean timed out", "maximum recursion", "maximum number of heartbeats")
            ),
            "Control resource failure",
        )
    hardware = []
    with tempfile.TemporaryDirectory(prefix="lark-wave-audit-") as temporary:
        temp = Path(temporary)
        source, packet, rebuilt = temp / "source", temp / "packet", temp / "rebuilt"
        unpack(root / "source.tar.gz", source)
        frozen_manifest = read(root / "source-manifest.json")
        manifest(source, frozen_manifest, exact=True)
        worker = source / "reproduction/wave_reduction/_statement_audit.py"
        require(not worker.exists(), "Reserved statement-worker path already exists")
        shutil.copyfile(__file__, worker)
        replay = subprocess.run(
            [sys.executable, str(worker), "--frozen-statement-worker", "--results", str(cpu)],
            cwd=source,
            capture_output=True,
            text=True,
            timeout=120,
        )
        require(
            replay.returncode == 0,
            "Frozen statement replay failed: " + replay.stdout + replay.stderr,
        )
        unpack(root / "gpu-input.tar.gz", packet)
        inputs = packet / "input"
        stored = read(inputs / "manifest.json")
        manifest(inputs, stored["files"])
        require(files(inputs) == set(stored["files"]) | {"manifest.json"}, "Unexpected input files")
        runner_name = "reproduction/wave_reduction/run_gpu.py"
        require(sha(packet / "runner.py") == frozen_manifest[runner_name], "Runner differs")
        generator = source / "reproduction/wave_reduction/prepare_gpu.py"
        require(sha(generator) == stored["generator_sha256"], "Generator differs")
        for name in ("kernel.hip", "reference.py", "task.json", "Main.lean", "report.json"):
            require(
                (inputs / name).read_bytes() == (cpu / "certificate" / name).read_bytes(),
                "GPU certificate binding",
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
            data["ordinary_trials"] == 264
            and data["stress_trials"] == 8
            and len(data["trials"]) == 272,
            "Dataset counts differ",
        )
        expected = (
            np.frombuffer((inputs / "reference.bin").read_bytes(), dtype="<f4")
            .astype(np.float64)
            .reshape(272, 64)
        )
        tree_bits = np.frombuffer((inputs / "source-tree.bin").read_bytes(), dtype="<u4").reshape(
            272, 64
        )
        tree = tree_bits.view("<f4").astype(np.float64)
        require(np.isfinite(expected).all() and np.isfinite(tree).all(), "Nonfinite reference")
        tree_failures = np.abs(tree - expected) > data["atol"] + data["rtol"] * np.abs(expected)
        require(
            int(tree_failures[:264].sum()) == data["ordinary_source_tree_reference_failures"] == 0,
            "CPU ordinary comparisons",
        )
        require(
            int(tree_failures[264:].sum())
            == data["stress_source_tree_reference_differences"]
            == 128,
            "CPU stress comparisons",
        )
        for host, physical in (("mi350", 2), ("mi350-2", 0)):
            location = temp / host
            unpack(root / (host + "-artifacts.tar.gz"), location)
            controller = read(location / "controller.json")
            require(
                controller["host"] == host
                and controller["physical_gpu"] == physical
                and controller["returncode"] == 0,
                "Controller failed/different GPU",
            )
            require(
                controller["transport_sha256"] == sha(root / "gpu-input.tar.gz"),
                "Transport differs",
            )
            require(
                controller["controller_sha256"] == validation["controller_sha256"],
                "Executed controller differs",
            )
            metrics = read(location / "preexecution-metric.json")["gpu_data"]
            metric = next(g for g in metrics if g["gpu"] == physical)
            require(metric["usage"]["gfx_activity"]["value"] == 0, "Preexecution GPU active")
            run = location / "gpu"
            guard = read(run / "memory-guard.json")
            require(
                guard["minimum_free_fraction"] == 0.98
                and guard["free_bytes"] >= 0.98 * guard["total_bytes"],
                "Memory guard",
            )
            report = read(run / "results.json")
            require(
                report["status"] == "passed"
                and report["architecture"] == "gfx950"
                and report["warp"] == 64
                and report["max_threads_per_block"] >= 64,
                "Hardware contract",
            )
            require(
                report["input_manifest_sha256"] == sha(inputs / "manifest.json"), "Input manifest"
            )
            require(report["runner_sha256"] == frozen_manifest[runner_name], "Executed runner")
            for name, field in (("driver.so", "binary_sha256"), ("output.bin", "output_sha256")):
                require(sha(run / name) == report[field], "Raw GPU evidence digest")
            flags = report["compile_command"]
            require(
                flags[:7]
                == [
                    "hipcc",
                    "-O3",
                    "-std=c++17",
                    "-shared",
                    "-fPIC",
                    "-ffp-contract=off",
                    "--offload-arch=gfx950",
                ],
                "Compiler flags differ",
            )
            raw = (run / "output.bin").read_bytes()
            require(len(raw) == 272 * 64 * 4, "Raw output length")
            bits = np.frombuffer(raw, dtype="<u4").reshape(272, 64)
            require(np.array_equal(bits, tree_bits), "Raw GPU/source-tree bits differ")
            actual = bits.view("<f4").astype(np.float64)
            require(np.isfinite(actual).all(), "Nonfinite GPU output")
            errors = np.abs(actual - expected)
            failures = errors > data["atol"] + data["rtol"] * np.abs(expected)
            require(len(report["trials"]) == 272, "Device trial count")
            for index, (recorded, trial) in enumerate(zip(report["trials"], data["trials"])):
                require(all(recorded[k] == v for k, v in trial.items()), "Trial metadata")
                require(
                    recorded["output_values"] == 64
                    and recorded["source_tree_bit_differences"] == 0,
                    "Trial bit comparison",
                )
                require(
                    recorded["inputs_unchanged"] and recorded["all_allocation_guards_unchanged"],
                    "Input/guard changed",
                )
                require(
                    recorded["reference_numerical_failures"] == int(failures[index].sum())
                    and recorded["max_abs_reference_error"] == float(errors[index].max()),
                    "Trial numerical metadata",
                )
            wanted = {
                "ordinary_trials": 264,
                "stress_trials": 8,
                "kernel_launches": 272,
                "output_values": 17408,
                "source_tree_bit_differences": 0,
                "ordinary_reference_comparisons": 16896,
                "ordinary_reference_numerical_failures": 0,
                "stress_reference_disagreements": 128,
                "model_calls": 0,
            }
            require(all(report[k] == v for k, v in wanted.items()), "Device summary counts")
            require(
                int(failures[:264].sum()) == 0 and int(failures[264:].sum()) == 128,
                "Independent raw numerical comparison",
            )
            require(
                report["ordinary_max_abs_reference_error"] == float(errors[:264].max())
                and report["stress_max_abs_reference_error"] == float(errors[264:].max()),
                "Maximum errors differ",
            )
            hardware.append(
                {
                    "host": host,
                    "physical_gpu": physical,
                    **wanted,
                    "ordinary_max_abs_reference_error": float(errors[:264].max()),
                    "stress_max_abs_reference_error": float(errors[264:].max()),
                    "recorded_inputs_and_guards_unchanged": True,
                }
            )
    summary = {
        "status": "frozen-statements-inputs-and-raw-two-host-evidence-audited",
        "certificates": 1,
        "recorded_independent_lean_rechecks": 1,
        "regenerated_positive_statements": 1,
        "regenerated_negative_statements": 4,
        "direct_lean_rejections": 4,
        "mutant_timeouts": 0,
        "hardware": hardware,
        "fresh_lean_checks": 0,
        "fresh_gpu_trials": 0,
        "model_calls": 0,
        "original_paper_fully_reproduced": False,
        "scope": record["scope"],
        "floating_point_scope": "Exact-real equality is proved. FP32 ordinary trials meet tolerance; fixed cancellation probes disagree with Torch in 128/512 outputs per host and remain separately reported. No IEEE equality/error theorem.",
    }
    if args.output:
        require(not args.output.exists(), "Refusing to overwrite an earlier summary")
        args.output.write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
