"""Export/recheck complete native RoPE certificates and scoped false claims."""

import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil
import sys
import tarfile
import time

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from lark_kernels import native_rope_certificate as native, native_rope_backend as backend
from lark_kernels.certificate import check, lean_binary
from lark_kernels.ir import Refusal

HERE = Path(__file__).resolve().parent
ROWS = (1, 3, 256, 65535)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n")


def audits(log):
    entries = re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", log)
    result = dict(entries)
    if len(entries) != len(result) or any(not {a.strip() for a in v.split(",") if a.strip()} <=
                                         {"propext", "Classical.choice", "Quot.sound"} for v in result.values()):
        raise ValueError("Axiom closure differs")
    return result


def logical_refusal(log):
    return "error:" in log and "is false" in log and not re.search(
        r"maximum recursion|heartbeats|stack overflow|timed out|out of memory", log, re.I)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--lean")
    parser.add_argument("--timeout", type=float, default=600)
    args = parser.parse_args()
    out = args.output.resolve()
    if out.is_relative_to(ROOT):
        raise ValueError("Fresh output outside repository required")
    out.mkdir(parents=True, exist_ok=False)
    if args.timeout <= 0:
        raise ValueError("Positive proof timeout required")
    lean, proofs = lean_binary(args.lean), native.libraries()
    provenance = json.loads((HERE / "provenance.json").read_text())
    checks = []

    def record(name, accepted, expected, before):
        if accepted is not expected:
            raise ValueError("Unexpected acceptance: " + name)
        checks.append({"name": name, "accepted": accepted, "expected_accepted": expected,
                       "seconds": time.monotonic() - before, "timed_out": False})

    baseline = None
    for layout in ("interleaved", "split-half"):
        case = HERE / "cases" / layout
        if sha(case / "kernel.hip") != provenance["files_sha256"]["cases/" + layout + "/kernel.hip"]:
            raise ValueError("GPU-tested source bytes changed")
        for rows in ROWS:
            raw = json.loads((case / "task.json").read_text())
            raw["launch"]["grid"] = rows
            for b in raw["buffers"]:
                b["shape"][0] = rows
            task = out / f"task-{layout}-{rows}.json"
            write(task, raw)
            name = f"{layout}-{rows}"
            dest = out / name
            before = time.monotonic()
            report = native.verify(case / "kernel.hip", case / "reference.py", task, dest, lean=lean, timeout=args.timeout)
            record(name, report["status"] == "verified", True, before)
            if len(audits(report["axiom_audit"])) != 10:
                raise ValueError("Principal source audits differ")
            before = time.monotonic()
            log = check(dest, lean=lean, timeout=args.timeout)
            (out / (name + "-recheck.log")).write_text(log)
            record("recheck-" + name, True, True, before)
            if layout == "interleaved" and rows == 1:
                baseline = dest

    controls = out / "controls"
    controls.mkdir()
    case = HERE / "cases/interleaved"
    source = (case / "kernel.hip").read_text()
    changed_sources = {
        "wrong-loop-stride": source.replace("qi = qi + 512;", "qi = qi + 511;"),
        "wrong-cache-half": source.replace("int qcb = qca + 64;", "int qcb = qca + 63;"),
        "missing-key-store": source.replace("    key[kb] = __float2half(koy);\n", ""),
        "wrong-pair-arithmetic": source.replace("float qox = qxc - qys;", "float qox = qys - qxc;"),
    }
    for name, changed in changed_sources.items():
        if changed == source:
            raise ValueError("Vacuous source control")
        path = controls / (name + ".hip")
        path.write_text(changed)
        before = time.monotonic()
        report = native.verify(path, case / "reference.py", case / "task.json", controls / name, lean=lean, timeout=args.timeout)
        if not logical_refusal(report["axiom_audit"]) or "program_data" not in report["axiom_audit"]:
            raise ValueError("Wrong source refusal gate: " + name)
        record(name, report["status"] == "verified", False, before)

    prefix = '''import Lark.NativeRopeCorrect
open LarkNonlinear LarkNativeRope
def p : Shape := ⟨1, by decide, by decide⟩
def testOps : Ops Nat := ⟨(fun _ _ => 0), Nat.add, Nat.sub, Nat.mul, Nat.max,
  Nat.div, id, id, id, id, id⟩
def values : Nat → Nat → Nat := fun _ _ => 0
def outside : Location → Option Nat := fun _ => none
'''
    false_claims = {
        "invented-none-launch": prefix + '''example : (runLaunch testOps (layout p) (geometry p) fuel (program false)
    (initial p values outside)).isNone = true := by
  rw [(final_launch p false testOps values outside).1]
  decide
''',
        "invented-final-race": prefix + '''example : raceFree (geometry p) (finalState p false testOps values outside).trace = false := by
  rw [final_race_free]
  decide
''',
        "missing-key-extraction": prefix + '''example : (extract (layout p) (finalState p false testOps values outside)).map List.length = some 4096 := by
  rw [final_extract]
  change some ((spec p false testOps values).length) = some 4096
  rw [spec_length]
  change some 5120 = some 4096
  decide
''',
        "wrong-first-query-value": prefix + '''example : (finalState p false testOps values outside).memory (globalCell 0 0) = some 1 := by
  rw [final_query_output p false testOps values outside 0 (by decide)]
  change some (0 : Nat) = some 1
  decide
''',
    }
    for name, text in false_claims.items():
        before = time.monotonic()
        accepted, log = native.validate_main(text.encode(), proofs, lean, args.timeout)
        (out / (name + ".log")).write_text(log)
        if not logical_refusal(log):
            raise ValueError("Wrong semantic refusal gate: " + name + ": " + log)
        record(name, accepted, False, before)

    for name, field, replacement in [
        ("rehashed-main", "Main.lean", lambda s: s.replace("def mutableBuffers : List Nat := [0, 1]", "def mutableBuffers : List Nat := [0]")),
        ("rehashed-model", "Lark/InOutScalar.lean", lambda s: s + "\n-- changed pinned model\n"),
        ("rehashed-reference", "reference.py", lambda s: s.replace("return rotate(query, cache), rotate(key, cache)", "return query, key")),
        ("invented-ieee-proof", None, None), ("invented-paper-completion", None, None),
        ("missing-inout-proof", None, None), ("boolean-row-count", None, None), ("unknown-proof-claim", None, None),
    ]:
        dest = controls / name
        shutil.copytree(baseline, dest)
        report = json.loads((dest / "report.json").read_text())
        if field:
            path = dest / field
            changed = replacement(path.read_text())
            if changed == path.read_text():
                raise ValueError("Vacuous integrity control")
            path.write_text(changed)
            report["files"][field] = sha(path)
            if field in report["model_hashes"]:
                report["model_hashes"][field] = sha(path)
        elif name == "invented-ieee-proof":
            report["ieee_equivalence_proved"] = True
        elif name == "invented-paper-completion":
            report["original_paper_fully_reproduced"] = True
        elif name == "missing-inout-proof":
            report["seeded_inout_proved"] = False
        elif name == "boolean-row-count":
            report["rows"] = True
        else:
            report["canonical_real_reference_proved"] = True
        write(dest / "report.json", report)
        before = time.monotonic()
        try:
            check(dest, lean=lean, timeout=args.timeout)
        except Refusal as error:
            (out / (name + ".log")).write_text(str(error) + "\n")
            record(name, False, False, before)
        else:
            raise ValueError("Rehashed claim accepted: " + name)

    cache, _ = backend.prepare(proofs, lean, args.timeout)
    shutil.copyfile(cache / "build.log", out / "fresh-library-build.log")
    library_audits = audits((out / "fresh-library-build.log").read_text())
    if "LarkNativeRope.correct" not in library_audits or "LarkNativeRope.final_race_free" not in library_audits:
        raise ValueError("Principal native source results absent")
    project = out / "source"
    filenames = ["lean/" + n for n in proofs] + ["lean/lean-toolchain", "lean/lakefile.toml", "LICENSE", "pyproject.toml"]
    filenames += [str(p.relative_to(ROOT)) for p in (ROOT / "lark_kernels").glob("*.py")]
    filenames += [str(p.relative_to(ROOT)) for p in HERE.glob("*.py")]
    for folder in ("cases", "upstream"):
        filenames += [str(p.relative_to(ROOT)) for p in (HERE / folder).rglob("*") if p.is_file()]
    filenames += [str((HERE / "provenance.json").relative_to(ROOT))]
    hashes = {}
    for name in sorted(set(filenames)):
        dest = project / name
        dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(ROOT / name, dest)
        hashes[name] = sha(dest)
    write(out / "source-manifest.json", hashes)
    with tarfile.open(out / "source.tar.gz", "w:gz") as archive:
        for name in hashes:
            archive.add(project / name, arcname=name, recursive=False)
    report = {"schema": 1, "status": "native-rope-source-bound-whole-launch-checked", "model_profile": native.PROFILE,
              "local_lean_modules": len(proofs), "library_axiom_audits": library_audits,
              "source_instances": 8, "source_certificates": 8, "main_axiom_audits_per_instance": 10,
              "false_lean_claims_rejected": 8, "rehashed_false_claims_rejected": 8, "checks": checks,
              "source_archive_sha256": sha(out / "source.tar.gz"), "source_manifest_sha256": sha(out / "source-manifest.json"),
              "both_layouts_proved": True, "whole_kernel_execution_proved": True, "actual_trace_race_freedom_proved": True,
              "seeded_inout_proved": True, "both_output_buffers_extracted": True, "source_reference_equality_proved": True,
              "scalar_interpretation": "arbitrary scalar operations and explicit half conversions",
              "ieee_equivalence_proved": False, "floating_point_error_bound_proved": False,
              "original_paper_fully_reproduced": False, "model_calls": 0, "gpu_trials": 0}
    write(out / "results.json", report)
    write(out / "manifest.json", {p.name: sha(p) for p in sorted(out.iterdir()) if p.is_file()})
    print(json.dumps({"status": report["status"], "modules": len(proofs), "library_audits": len(library_audits),
                      "certificates": 8, "rechecks": 8, "false_lean_claims": 8, "rehashed_controls": 8}))


if __name__ == "__main__":
    main()
