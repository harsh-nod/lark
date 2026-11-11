"""Freeze and check the full repaired softmax source against canonical reals.

Only clean, revision-locked external Mathlib packages may supply compiled
objects. All owned source, source binding, launch and reference proofs build
fresh. Half conversions are identities; the reserved seed is any finite real.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tarfile
import time

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from lark_kernels import real_backend
from reproduction.production_softmax import check_whole_grid as grid
from reproduction.production_softmax.canonical_statement import EXTRA

HERE = Path(__file__).resolve().parent
MATHLIB = real_backend.MATHLIB
TARGET = "LarkReal.NativeSoftmaxCanonical"
require, sha = grid.require, grid.sha


def modules(name, found):
    if name in found:
        return
    require(re.fullmatch(r"(?:Lark|LarkReal)\.[A-Za-z0-9_]+", name), "Unexpected owned module")
    found.add(name)
    root = ROOT / ("lean-real" if name.startswith("LarkReal.") else "lean")
    for line in (root / (name.replace(".", "/") + ".lean")).read_text().splitlines():
        if line.startswith("import "):
            for dependency in line.split()[1:]:
                if dependency.startswith(("Lark.", "LarkReal.")):
                    modules(dependency, found)
                else:
                    require(dependency == "Std" or dependency.startswith("Mathlib."), "Unexpected external module")


def controls(original, fixed, task):
    all_grid = grid.controls(original, fixed, task, grid.statement(original, fixed, task))
    result = {name: text for name, text in all_grid.items() if name.startswith("grid-fixed-")}
    common = "import RealMain\nopen LarkNonlinear LarkNativeSoftmax LarkReal.NativeSoftmax\n"
    binders = """(p : Shape) (seed : ℝ) (outside : Location → Option ℝ)
    (offset : Nat) (ho : offset<p.rows*50257)"""
    for name, wrong in (("uniform-dropped-column", "1/50256"), ("uniform-missing-division", "1")):
        result[name] = common + f"""example {binders} :
    (sourceFixedGrid p (softmaxOps seed) (fun _ _ => 0) outside).memory (globalCell 0 offset)=some ({wrong}) := by
  rewrite [source_uniform_output p seed outside offset ho]
  norm_num
"""
    result["nonpositive-source-denominator"] = common + """example (seed : ℝ) (input : Nat → Nat → ℝ) (row : Nat) :
    (0<rowExpSum (softmaxOps seed) input row)=False := by
  have hp := source_denominator_pos seed input row
  simp only [hp]
  decide
"""
    result["omitted-xor-tree-leaf"] = common + """example :
    (sumTree 5 0).leaves.Perm (List.range' 0 31) := by decide
"""
    result["zero-real-exponential"] = common + """example : (softmaxOps 0).exp 0=0 := by
  change Real.exp (0 : ℝ)=0
  norm_num
"""
    result["unscaled-exponential-shift"] = common + """example : Real.exp ((0 : ℝ)-1)=Real.exp 0 := by
  apply Real.exp_injective.eq_iff.mpr
  norm_num
"""
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    out = args.output.resolve()
    require(not any((p / ".git").exists() for p in (out, *out.parents)), "Choose output outside Git")
    out.mkdir(parents=True, exist_ok=False)
    project = out / "project"
    project.mkdir()
    original = (HERE / "cases/native_race/kernel.hip").read_text()
    fixed = (HERE / "cases/native_fixed/kernel.hip").read_text()
    require(original == grid.source(False) and fixed == grid.source(True), "Generated source differs")
    task = grid.native.parse_task((HERE / "cases/native_race/task.json").read_text())
    closure = set()
    for name in (TARGET, grid.base.TARGET, grid.prefix.TARGET):
        modules(name, closure)
    for name in sorted(closure):
        relative = name.replace(".", "/") + ".lean"
        source = ROOT / ("lean-real" if name.startswith("LarkReal.") else "lean") / relative
        destination = project / relative
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, destination)
    for name, blob in real_backend.configuration().items():
        (project / name).write_bytes(blob)
    lakefile = project / "lakefile.toml"
    lakefile.write_text(lakefile.read_text().replace('defaultTargets = ["Main"]', 'defaultTargets = ["Main", "RealMain"]')
                        + '\n[[lean_lib]]\nname = "RealMain"\n')
    (project / "Main.lean").write_text(grid.statement(original, fixed, task))
    (project / "RealMain.lean").write_text(EXTRA)
    frozen = project / "reproduction/production_softmax"
    frozen.mkdir(parents=True)
    for source in HERE.glob("*.py"):
        shutil.copyfile(source, frozen / source.name)
    for name in ("provenance.json", "rewrites.json"):
        shutil.copyfile(HERE / name, frozen / name)
    for name in ("cases", "upstream"):
        shutil.copytree(HERE / name, frozen / name)
    shutil.copyfile(ROOT / "reproduction/__init__.py", project / "reproduction/__init__.py")
    (project / "lark_kernels").mkdir()
    for source in (ROOT / "lark_kernels").glob("*.py"):
        shutil.copyfile(source, project / "lark_kernels" / source.name)
    shutil.copyfile(ROOT / "LICENSE", project / "LICENSE")
    (project / "validate_source.py").write_text('''from pathlib import Path
from reproduction.production_softmax import check_whole_grid as grid
from reproduction.production_softmax.canonical_statement import EXTRA
root=Path(__file__).resolve().parent
original=(grid.HERE/"cases/native_race/kernel.hip").read_text()
fixed=(grid.HERE/"cases/native_fixed/kernel.hip").read_text()
assert original==grid.source(False) and fixed==grid.source(True)
task=grid.native.parse_task((grid.HERE/"cases/native_race/task.json").read_text())
assert grid.statement(original,fixed,task)==(root/"Main.lean").read_text()
assert EXTRA==(root/"RealMain.lean").read_text()
print("Both full-source bindings, repaired complete grid and canonical-real reference bridge match.")
''')
    _, seeds = real_backend.dependencies()
    lock = json.loads((project / "lake-manifest.json").read_text())
    packages = lock["packages"]
    overrides = [dict(p, type="path", dir=str(seeds[p["name"]])) for p in packages]
    overrides_path = out / "dependency-path-overrides.json"
    overrides_path.write_text(json.dumps({"version": lock["version"], "packages": overrides}, indent=2) + "\n")
    lake = ["lake", "--packages=" + str(overrides_path)]
    env = dict(os.environ)
    env["PATH"] = str(Path(shutil.which("lean")).resolve().parent)
    env.pop("LEAN_PATH", None)
    env.pop("PYTHONPATH", None)
    env["PYTHONNOUSERSITE"] = "1"
    require(shutil.which("git", path=env["PATH"]) is None, "Git must be absent during proof checks")
    checks = []

    def run(name, command, expected, timeout=600):
        before = time.monotonic()
        result = subprocess.run(command, cwd=project, env=env, capture_output=True, text=True, timeout=timeout)
        log = result.stdout + result.stderr
        (out / (name + ".log")).write_text(log)
        accepted = result.returncode == 0 and "error:" not in log and "sorryAx" not in log
        require(accepted is expected, "Unexpected acceptance: " + name + "\n" + log)
        if not expected:
            require("error:" in log and ("is false" in log or "⊢ False" in log)
                    and not any(s in log for s in ("maximum recursion", "maximum heartbeats", "maximum number of heartbeats",
                                                   "deep recursion", "Stack overflow")), "Wrong rejection gate: " + name)
        checks.append({"name": name, "accepted": accepted, "expected_accepted": expected,
                       "exit_code": result.returncode, "seconds": time.monotonic() - before, "timed_out": False})
        return log

    run("frozen-reader", [sys.executable, "validate_source.py"], True)
    library_log = run("fresh-real-library-build", lake + ["build", TARGET], True)
    main_log = run("fresh-build", lake + ["build"], True)
    pattern = r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)"
    audits = dict(re.findall(pattern, library_log + "\n" + main_log))
    principal = grid.PRINCIPAL | {"LarkReal.NativeSoftmax.canonical_correct", "LarkReal.NativeSoftmax.row_sum_exponentials",
        "LarkReal.NativeSoftmax.source_denominator_pos", "LarkReal.NativeSoftmax.source_spec_canonical"}
    principal |= set(re.findall(r"^theorem (\w+)", EXTRA, re.M))
    require(principal <= audits.keys(), "Canonical-real principal audits absent")
    require(all(set(a.strip() for a in axioms.split(",") if a.strip()) <=
                {"propext", "Classical.choice", "Quot.sound"} for axioms in audits.values()), "Extra axiom")
    mutations = controls(original, fixed, task)
    for name, code in mutations.items():
        (project / (name + ".lean")).write_text(code)
        run(name, lake + ["env", "lean", name + ".lean"], False)
    (project / "README.md").write_text(
        "Fresh source check: python3 validate_source.py. Fresh owned proof build: lake build.\n"
        "Requires exactly the locked Mathlib dependencies; no owned compiled cache is archived.\n"
        "Main binds both full sources and the repaired complete grid under the original geometry/fuel.\n"
        "RealMain proves complete-launch Correct against the independent canonical dense softmax reference.\n"
        "Every supported shape, all real inputs and any finite seed. Half conversions are identities.\n"
        "The original source is proved through a complete block, without original race freedom.\n"
        "IEEE/error bounds and original-paper completion are not asserted. Other root Lean files intentionally fail.\n")
    files = sorted(p for p in project.rglob("*") if p.is_file()
                   and not {".lake", "__pycache__"}.intersection(p.relative_to(project).parts))
    (out / "source-manifest.json").write_text(json.dumps({str(p.relative_to(project)): sha(p) for p in files}, indent=2) + "\n")
    with tarfile.open(out / "source.tar.gz", "w:gz") as archive:
        for path in files:
            info = archive.gettarinfo(str(path), arcname=str(path.relative_to(project)))
            info.uid = info.gid = info.mtime = 0
            info.uname = info.gname = ""
            with path.open("rb") as stream:
                archive.addfile(info, stream)
    shutil.copyfile(Path(__file__), out / "checker.py")
    report = {
        "schema": 1, "status": "native-softmax-source-bound-canonical-real-whole-grid-checked", "stage": "canonical-real-whole-grid",
        "mathlib_revision": MATHLIB, "rows": {"min": 1, "max": 42730},
        "local_lean_modules": len(closure), "standard_lean_modules": sum(n.startswith("Lark.") for n in closure),
        "real_lean_modules": sum(n.startswith("LarkReal.") for n in closure),
        "axiom_audits": audits, "checks": checks, "false_lean_claims_rejected": len(mutations),
        "source_archive_sha256": sha(out / "source.tar.gz"),
        "source_sha256": {"original": hashlib.sha256(original.encode()).hexdigest(), "fixed": hashlib.sha256(fixed.encode()).hexdigest()},
        "dependency_sources_checked_before_path_restriction": [{"name": p["name"], "revision": p["rev"], "clean": True} for p in packages],
        "own_lean_compiled_cache_seeded": False, "external_pinned_mathlib_cache_seeded": True,
        "whole_kernel_execution_proved": True, "repaired_whole_grid_some_execution_proved": True,
        "repaired_whole_grid_race_freedom_proved": True, "repaired_whole_grid_all_outputs_proved": True,
        "canonical_source_equivalence_proved": True, "canonical_whole_grid_correct_proved": True,
        "positive_source_denominator_proved": True, "uniform_source_output_proved": True,
        "uniform_output": "1/50257", "whole_grid_variants": ["fixed"], "original_whole_grid_execution_proved": False,
        "half_conversions": "identity", "reserved_seed": "arbitrary finite real", "real_exponential": "Real.exp",
        "original_fuel": {"lane": 4096, "warp": 8, "block": 5, "grid": 1},
        "source_certificates": 0, "registered_source_profile": False, "race_freedom_assumed": False,
        "conflict_witness_state_reachability_proved": False, "original_whole_block_race_freedom_proved": False,
        "ieee_equivalence_proved": False, "floating_point_error_bound_proved": False,
        "original_paper_fully_reproduced": False, "model_calls": 0, "gpu_trials": 0,
    }
    (out / "results.json").write_text(json.dumps(report, indent=2) + "\n")
    (out / "manifest.json").write_text(json.dumps({p.name: sha(p) for p in sorted(out.iterdir()) if p.is_file()}, indent=2) + "\n")
    print(json.dumps({"status": report["status"], "modules": len(closure), "audits": len(audits), "rejections": len(mutations)}))


if __name__ == "__main__":
    main()
