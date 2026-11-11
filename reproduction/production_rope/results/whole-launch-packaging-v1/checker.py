"""Bind wheel proof/reader bytes to a source revision and exercise installed CLI."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import venv
import zipfile

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from lark_kernels import native_rope_certificate as native
from reproduction.production_softmax import check_native_real as real, check_original_race as race


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--wheel", type=Path, required=True)
    parser.add_argument("--source-commit", required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--lean", required=True)
    args = parser.parse_args()
    out, wheel = args.output.resolve(), args.wheel.resolve()
    if out.is_relative_to(ROOT):
        raise ValueError("Fresh package audit outside repository required")
    out.mkdir(parents=True, exist_ok=False)

    def revision(path):
        return subprocess.check_output(["git", "-C", str(ROOT), "show", args.source_commit + ":" + path])

    closure = set()
    for target in (real.TARGET, race.TARGET, race.grid.TARGET, race.base.TARGET, race.prefix.TARGET):
        real.modules(target, closure)
    rope = native.libraries()
    closure.update(name[:-5].replace("/", ".") for name in rope)
    if len(closure) != 164 or len(rope) != 25:
        raise ValueError("Required proof closure changed")
    matched = {}
    with zipfile.ZipFile(wheel) as archive:
        for module in sorted(closure):
            path = ("lean-real/" if module.startswith("LarkReal.") else "lean/") + module.replace(".", "/") + ".lean"
            entries = [n for n in archive.namelist() if n.endswith("/share/lark/" + path)]
            if len(entries) != 1:
                raise ValueError("Missing or ambiguous proof resource: " + path)
            content = archive.read(entries[0])
            if content != (ROOT / path).read_bytes() or content != revision(path):
                raise ValueError("Wheel/source/revision proof bytes differ: " + path)
            matched[path] = hashlib.sha256(content).hexdigest()
        for source in sorted((ROOT / "lark_kernels").glob("*.py")):
            path = str(source.relative_to(ROOT))
            content = archive.read(path)
            if content != source.read_bytes() or content != revision(path):
                raise ValueError("Wheel/source/revision reader bytes differ: " + path)
            matched[path] = hashlib.sha256(content).hexdigest()
    if (ROOT / "pyproject.toml").read_bytes() != revision("pyproject.toml"):
        raise ValueError("Packaging configuration differs from source revision")
    env_dir = out / "venv"
    venv.EnvBuilder(with_pip=True).create(env_dir)
    env = dict(os.environ)
    env.pop("PYTHONPATH", None)
    env.pop("LEAN_PATH", None)
    env["PYTHONNOUSERSITE"] = "1"

    def run(name, command):
        result = subprocess.run(command, cwd=out, env=env, capture_output=True, text=True, timeout=900)
        log = result.stdout + result.stderr
        (out / name).write_text(log)
        if result.returncode:
            raise ValueError("Installed wheel command failed: " + name + ": " + log)
        return log

    run("install.log", [str(env_dir / "bin/python"), "-m", "pip", "install", "--no-deps", str(wheel)])
    case = ROOT / "reproduction/production_rope/cases/split-half"
    certificate = out / "installed-certificate"
    run("installed-export.log", [str(env_dir / "bin/lark"), "verify-native-rope", str(case / "kernel.hip"),
                                "--reference", str(case / "reference.py"), "--task", str(case / "task.json"),
                                "--output", str(certificate), "--lean", args.lean, "--timeout", "600"])
    run("installed-recheck.log", [str(env_dir / "bin/lark"), "check", str(certificate), "--lean", args.lean, "--timeout", "600"])
    report = json.loads((certificate / "report.json").read_text())
    if report["status"] != "verified" or set(report["model_hashes"]) != set(rope):
        raise ValueError("Installed proof resources differ")
    shutil.copyfile(wheel, out / wheel.name)
    shutil.copyfile(__file__, out / "checker.py")
    result = {"schema": 1, "status": "native-rope-whole-launch-wheel-and-installed-cli-checked",
              "source_commit": args.source_commit, "wheel_bytes": wheel.stat().st_size, "wheel_sha256": sha(wheel),
              "packaged_proof_modules": len(closure), "native_rope_required_modules": len(rope),
              "earlier_softmax_required_modules": 143, "matched_source_sha256": matched,
              "pyproject_sha256": sha(ROOT / "pyproject.toml"), "installed_source_certificates": 1,
              "installed_source_rechecks": 1, "model_calls": 0, "gpu_trials": 0,
              "original_paper_fully_reproduced": False}
    (out / "results.json").write_text(json.dumps(result, indent=2) + "\n")
    (out / "manifest.json").write_text(json.dumps({p.name: sha(p) for p in sorted(out.iterdir()) if p.is_file()}, indent=2) + "\n")
    print(json.dumps({"status": result["status"], "modules": len(closure), "installed_certificates": 1}))


if __name__ == "__main__":
    main()
