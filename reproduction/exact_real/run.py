"""Check the optional exact-real bridge and reduction-algebra controls.

No new source certificate, hardware experiment or model outcome is claimed.
Run after installing the pinned optional package's Mathlib dependency/cache.
"""

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import shutil
import struct
import subprocess
import tarfile
import time

ROOT = Path(__file__).resolve().parents[2]
NAMES = (
    "silu_result",
    "silu_correct",
    "dot_correct",
    "tree_permutation",
    "chunk_sum",
    "universal_reassociation_impossible",
)
MATHLIB = "c44e0c8ee63ca166450922a373c7409c5d26b00b"


def require(ok, message):
    if not ok:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n")


def execute(command, cwd, log, timeout=300):
    start = time.monotonic()
    result = subprocess.run(command, cwd=cwd, capture_output=True, text=True, timeout=timeout)
    log.write_text(result.stdout + result.stderr)
    return result.returncode, time.monotonic() - start


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--lake", default="lake")
    args = parser.parse_args()
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    project = ROOT / "lean-real"
    lock = json.loads((project / "lake-manifest.json").read_text())
    dependencies = []
    for package in lock["packages"]:
        if package["type"] != "git":
            require(
                package["name"] == "lark" and package["dir"] == "./../lean",
                "Unexpected local dependency",
            )
            continue
        location = project / ".lake/packages" / package["name"]
        head = subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=location, text=True
        ).strip()
        require(head == package["rev"], "Dependency revision differs")
        subprocess.run(["git", "diff", "--quiet", "HEAD", "--"], cwd=location, check=True)
        dependencies.append({"name": package["name"], "url": package["url"], "commit": head})
    require(
        any(p["name"] == "mathlib" and p["commit"] == MATHLIB for p in dependencies),
        "Mathlib pin differs",
    )
    code, build_seconds = execute([args.lake, "build"], project, out / "build.log")
    require(code == 0, "Optional library build failed")
    code, check_seconds = execute(
        [args.lake, "env", "lean", "LarkReal/Ops.lean"], project, out / "fresh-check.log"
    )
    require(code == 0, "Fresh exact-real check failed")
    log = (out / "fresh-check.log").read_text()
    require("error:" not in log and "sorryAx" not in log, "Positive error/admission")
    audits = {}
    for name in NAMES:
        entries = re.findall(
            r"^'LarkReal\." + name + r"' depends on axioms: \[([^]]*)\]$", log, re.M
        )
        require(len(entries) == 1, "Missing/ambiguous audit: " + name)
        axioms = entries[0].split(", ")
        require(set(axioms) <= {"propext", "Classical.choice", "Quot.sound"}, "Forbidden axiom")
        audits[name] = axioms
    header = "import LarkReal.Ops\nopen LarkReal\n"
    positives = (
        header
        + """
example (v : Nat → ℝ) :
    (AddTree.join (.leaf 1) (.leaf 0)).eval v = ([0, 1].map v).sum := by
  exact tree_permutation _ _ v (by decide)
"""
    )
    controls = {
        "reversed-leaves-positive": (True, positives),
        "duplicated-leaf": (False, positives.replace("(.leaf 1) (.leaf 0)", "(.leaf 0) (.leaf 0)")),
        "omitted-leaf": (
            False,
            positives.replace("(AddTree.join (.leaf 1) (.leaf 0))", "(AddTree.leaf 0)"),
        ),
        "unrestricted-associativity": (
            False,
            header
            + """
example : nonassociativeOps.add (nonassociativeOps.add 1 2) 3 =
    nonassociativeOps.add 1 (nonassociativeOps.add 2 3) := by decide
""",
        ),
    }
    results = []
    for name, (expected, source) in controls.items():
        file = out / (name + ".lean")
        file.write_text(source)
        code, seconds = execute(
            [args.lake, "env", "lean", str(file)], project, out / (name + ".log")
        )
        require((code == 0) == expected, "Unexpected algebra-control outcome: " + name)
        if not expected:
            text = (out / (name + ".log")).read_text()
            require(
                "error: tactic 'decide' proved that the proposition" in text and "is false" in text,
                "Expected false-decision failure missing",
            )
        results.append(
            {"name": name, "accepted": code == 0, "timed_out": False, "seconds": seconds}
        )

    def f32(value):
        return struct.unpack("<f", struct.pack("<f", value))[0]

    a, b, c = f32(2**25), f32(-(2**25)), f32(1)
    left, right = f32(f32(a + b) + c), f32(a + f32(b + c))
    require(left == 1.0 and right == 0.0, "CPU binary32 scope witness differs")
    source = out / "source"
    names = [
        "lean-real/lakefile.toml",
        "lean-real/lean-toolchain",
        "lean-real/lake-manifest.json",
        "lean-real/LarkReal.lean",
        "lean-real/LarkReal/Ops.lean",
        "reproduction/exact_real/run.py",
    ]
    names += [
        "lean/Lark/" + n
        for n in (
            "Nonlinear.lean",
            "Pointwise.lean",
            "Reduction.lean",
            "DotLoop.lean",
            "Matrix.lean",
            "ScalarLaunch.lean",
            "Silu.lean",
        )
    ]
    names += ["lean/lean-toolchain", "lean/lakefile.toml", "LICENSE"]
    for name in names:
        dest = source / name
        dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(ROOT / name, dest)
    write(out / "source-manifest.json", {n: sha(source / n) for n in sorted(names)})
    with tarfile.open(out / "source.tar.gz", "w:gz") as archive:
        for name in sorted(names):
            archive.add(source / name, arcname=name, recursive=False)
    shutil.rmtree(source)
    write(
        out / "results.json",
        {
            "status": "passed",
            "recorded_utc": datetime.now(timezone.utc).isoformat(),
            "build_seconds": build_seconds,
            "fresh_check_seconds": check_seconds,
            "axiom_audits": audits,
            "algebra_controls": results,
            "dependencies": dependencies,
            "cpu_binary32_scope_witness": {
                "inputs": [a, b, c],
                "left_associated": left,
                "right_associated": right,
                "method": "explicit binary32 rounding with Python struct after each addition",
            },
            "new_source_certificates": 0,
            "new_gpu_trials": 0,
            "model_calls": 0,
            "original_paper_fully_reproduced": False,
            "scope": "Optional exact-real interpretation, canonical specifications for existing SiLU and dot-product machine proofs, and reduction-tree/chunk algebra. This adds no optimized GPU-program proof and does not reproduce original experiments. Half conversions are identities in this idealization; no IEEE or numerical-error theorem.",
        },
    )
    write(
        out / "manifest.json",
        {p.relative_to(out).as_posix(): sha(p) for p in sorted(out.rglob("*")) if p.is_file()},
    )
    print(
        json.dumps(
            {
                "status": "passed",
                "axiom_audits": 6,
                "positive_control": 1,
                "negative_controls": 3,
                "new_source_certificates": 0,
                "new_gpu_trials": 0,
                "model_calls": 0,
            }
        )
    )


if __name__ == "__main__":
    main()
