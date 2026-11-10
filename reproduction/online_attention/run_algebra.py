"""Freshly check online-attention algebra and false-update controls, without model calls.

This proves a value recurrence. It produces no GPU-source certificate and makes
no claim about machine execution, source lowering, races or IEEE arithmetic.
"""

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from lark_kernels.certificate import lean_binary  # noqa: E402
from lark_kernels.real_backend import prepare  # noqa: E402

HERE = Path(__file__).resolve().parent
LIBRARY = "lean-real/LarkReal/OnlineSoftmax.lean"
NAMES = (
    "exp_rescale", "weight_shift", "numerator_shift", "weight_pos",
    "update_valid", "valid_reference", "process_valid", "process_reference", "run_reference",
)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n")


def require(ok, message):
    if not ok:
        raise ValueError(message)


HEADER = """import LarkReal.OnlineSoftmax
open LarkReal.OnlineSoftmax
noncomputable def entry (v : ℝ) : Entry := ⟨0, fun _ => v⟩
noncomputable def prior : Accumulator := start 0 [entry 2, entry 2]
"""

BAD_UPDATE = """
noncomputable def changed (a : Accumulator) (tileM : ℝ) (tile : List Entry) : Accumulator :=
  let m := max a.m tileM
  let l := Real.exp (a.m - m) * a.l + Real.exp (tileM - m) * weight tileM tile
  ⟨m, l, fun c => (1 / l) *
    ((a.l * Real.exp (a.m - m) * a.o c) +
      (Real.exp (tileM - m) * numerator tileM tile c))⟩
"""


def controls():
    simplify = "by norm_num [changed, prior, start, entry, weight, numerator]"
    call = "(changed prior 0 [entry 4]).o 0"
    cases = {
        "correct-update": (True, HEADER + """
example : (update prior 0 [entry 4]).o 0 = (8 / 3 : ℝ) := by
  norm_num [update, prior, start, entry, weight, numerator]
"""),
    }
    changes = {
        "omitted-old-mass": BAD_UPDATE.replace("a.l * Real.exp (a.m - m) * a.o c", "Real.exp (a.m - m) * a.o c"),
        "omitted-tile-mass": BAD_UPDATE.replace("+ Real.exp (tileM - m) * weight tileM tile", ""),
        "doubled-tile-value": BAD_UPDATE.replace("(Real.exp (tileM - m) * numerator tileM tile c)", "(2 * Real.exp (tileM - m) * numerator tileM tile c)"),
    }
    for name, source in changes.items():
        require(source != BAD_UPDATE, "Control did not change the recurrence")
        cases[name] = (False, HEADER + source + f"\nexample : {call} = (8 / 3 : ℝ) := {simplify}\n")
        cases[name + "-counterexample"] = (
            True, HEADER + source + f"\nexample : {call} ≠ (8 / 3 : ℝ) := {simplify}\n"
        )
    cases["reversed-rescale-sign"] = (False, HEADER + """
example : Real.exp (-1 : ℝ) * Real.exp (0 : ℝ) = Real.exp (1 : ℝ) := by
  simp only [Real.exp_zero, mul_one]
  apply congrArg Real.exp
  norm_num
""")
    cases["reversed-rescale-sign-counterexample"] = (True, HEADER + """
example : Real.exp (-1 : ℝ) * Real.exp (0 : ℝ) ≠ Real.exp (1 : ℝ) := by
  simp only [Real.exp_zero, mul_one]
  exact Real.exp_injective.ne (by norm_num)
""")
    return cases


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--timeout", type=int, default=600)
    args = parser.parse_args()
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    binary = lean_binary()
    source = (ROOT / LIBRARY).read_bytes()
    provenance = json.loads((HERE / "provenance.json").read_text())
    require(sha(HERE / "upstream/flash.cu") == provenance["source_sha256"], "Upstream source differs")
    require(sha(HERE / "upstream/LICENSE") == provenance["license_sha256"], "Upstream license differs")
    started = time.monotonic()
    cache, env = prepare(
        {"LarkReal/OnlineSoftmax.lean": source}, binary, args.timeout,
        target="LarkReal.OnlineSoftmax",
    )
    shutil.copyfile(cache / "build.log", out / "build.log")
    shutil.copyfile(cache / "checked-build.json", out / "checked-build.json")
    frozen = out / "OnlineSoftmax.lean"
    frozen.write_bytes(source)
    checks = [("fresh-check", True, frozen)]
    for name, (accepted, content) in controls().items():
        file = out / (name + ".lean")
        file.write_text(content)
        checks.append((name, accepted, file))
    records = []
    for name, expected, file in checks:
        before = time.monotonic()
        result = subprocess.run(
            [str(binary), str(file)], cwd=out, env=env,
            text=True, capture_output=True, timeout=args.timeout,
        )
        log = result.stdout + result.stderr
        (out / (name + ".log")).write_text(log)
        require((result.returncode == 0) == expected, "Unexpected Lean result: " + name)
        require("sorryAx" not in log, "Admission in a checked result: " + name)
        if not expected:
            require("error:" in log and "unsolved goals" in log and "⊢ False" in log,
                    "Not a completed false arithmetic assertion: " + name)
        records.append({"name": name, "expected_accepted": expected,
                        "accepted": result.returncode == 0, "exit_code": result.returncode,
                        "timed_out": False, "seconds": time.monotonic() - before})
    log = (out / "fresh-check.log").read_text()
    audits = {}
    for name in NAMES:
        entries = re.findall(
            r"^'LarkReal\.OnlineSoftmax\." + name + r"' depends on axioms: \[([^]]*)\]$", log, re.M
        )
        require(len(entries) == 1, "Missing or ambiguous audit: " + name)
        axioms = entries[0].split(", ")
        require(set(axioms) <= {"propext", "Classical.choice", "Quot.sound"}, "Extra axiom: " + name)
        audits[name] = axioms
    frozen_root = out / "source"
    paths = [LIBRARY, "lark_kernels/real_backend.py", "lark_kernels/certificate.py",
             "lean-real/lake-manifest.json", "lean-real/lakefile.toml", "lean-real/lean-toolchain",
             "reproduction/online_attention/run_algebra.py", "reproduction/online_attention/provenance.json",
             "reproduction/online_attention/upstream/flash.cu", "reproduction/online_attention/upstream/LICENSE"]
    for name in paths:
        target = frozen_root / name
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(ROOT / name, target)
    write(out / "source-manifest.json", {name: sha(frozen_root / name) for name in paths})
    write(out / "results.json", {
        "schema": 1, "status": "online-recurrence-algebra-checked",
        "checked_at_utc": datetime.now(timezone.utc).isoformat(),
        "seconds": time.monotonic() - started, "axioms": audits, "checks": records,
        "negative_algebra_controls": sum(not r["expected_accepted"] for r in records),
        "proved_counterexamples": sum(r["name"].endswith("-counterexample") for r in records),
        "source_sha256": hashlib.sha256(source).hexdigest(),
        "upstream": provenance,
        "source_certificates": 0, "gpu_trials": 0, "model_calls": 0,
        "whole_kernel_execution_proved": False, "race_freedom_proved": False,
        "ieee_equivalence_proved": False, "original_paper_fully_reproduced": False,
    })
    write(out / "manifest.json", {str(p.relative_to(out)): sha(p) for p in sorted(out.rglob("*")) if p.is_file()})
    print(json.dumps({"status": "passed", "axiom_audits": len(audits),
                      "negative_algebra_controls": 4, "proved_counterexamples": 4,
                      "source_certificates": 0, "gpu_trials": 0, "model_calls": 0}))


if __name__ == "__main__":
    main()
