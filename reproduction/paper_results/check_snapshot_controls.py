"""Check standalone replay and fully rehashed false-completion controls."""

import argparse
import hashlib
import io
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tarfile
import tempfile
import uuid

from replay_snapshot import DEFAULT, file_set, read, write


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def rehash(snapshot, *, archive_changed=False):
    if archive_changed:
        provenance = read(snapshot / "provenance.json")
        provenance["evidence_archive_sha256"] = sha(snapshot / "evidence.tar.gz")
        provenance["evidence_manifest_sha256"] = sha(snapshot / "evidence-manifest.json")
        write(snapshot / "provenance.json", provenance)
    results = snapshot / "results"
    write(results / "manifest.json", {n: sha(results / n) for n in ("audit.json", "RESULTS.md")})
    write(
        snapshot / "manifest.json",
        {n: sha(snapshot / n) for n in sorted(file_set(snapshot)) if n != "manifest.json"},
    )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--snapshot", type=Path, default=DEFAULT)
    parser.add_argument("--source-archive", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    snapshot, manuscript, out = (
        args.snapshot.resolve(),
        args.source_archive.resolve(),
        args.output.resolve(),
    )
    out.mkdir(parents=True, exist_ok=False)
    results = []
    with tempfile.TemporaryDirectory(prefix="lark-snapshot-controls-") as temporary:
        root = Path(temporary)
        script = root / "isolated/bin/replay_snapshot.py"
        script.parent.mkdir(parents=True)
        shutil.copyfile(Path(__file__).with_name("replay_snapshot.py"), script)
        isolated = root / "isolated/snapshot"
        shutil.copytree(snapshot, isolated)
        env = dict(os.environ)
        env["PATH"] = "/nonexistent"
        env.pop("PYTHONPATH", None)
        env["PYTHONNOUSERSITE"] = "1"

        def execute(name, data, source=manuscript):
            run = subprocess.run(
                [
                    sys.executable,
                    str(script),
                    "--snapshot",
                    str(data),
                    "--source-archive",
                    str(source),
                ],
                cwd=root / "isolated",
                env=env,
                capture_output=True,
                text=True,
                timeout=120,
            )
            log = run.stdout + run.stderr
            (out / (name + ".log")).write_text(log)
            return run.returncode, log

        code, log = execute("outside-checkout-no-git", isolated)
        if code or "frozen-snapshot-replayed" not in log:
            raise RuntimeError("Standalone replay failed: " + log)
        results.append({"name": "outside-checkout-no-git", "accepted": True, "git_on_path": False})
        names = ["global-completion-claim", "original-production-claim"]
        has_production_cases = "production_cases" in read(snapshot / "targets.json")
        if has_production_cases:
            names.append("invented-native-awq-coverage")
        for name in names:
            altered = root / name
            shutil.copytree(snapshot, altered)
            report = read(altered / "results/audit.json")
            if name == "global-completion-claim":
                report["original_paper_fully_reproduced"] = True
                report["completion_percentage"] = 100
            elif name == "original-production-claim":
                row = next(r for r in report["floats"] if r["label"] == "tab:lib-kernels")
                row["original_result_reproduced"] = True
            else:
                row = next(r for r in report["production_cases"]
                           if r["paper_case"] == "vllm-awq-gemm")
                row["independent_status"] = "complete-scoped-proof"
                row["registered_source_certificates"] = 4
            write(altered / "results/audit.json", report)
            rehash(altered)
            code, log = execute(name, altered)
            if code == 0 or "Audit differs: audit.json" not in log:
                raise RuntimeError("False completion was not rejected at regeneration: " + log)
            results.append(
                {
                    "name": name,
                    "accepted": False,
                    "fully_rehashed": True,
                    "gate": "frozen report regeneration",
                }
            )
        if has_production_cases:
            altered = root / "missing-production-case"
            shutil.copytree(snapshot, altered)
            targets = read(altered / "targets.json")
            targets["production_cases"] = [
                row for row in targets["production_cases"]
                if row["paper_case"] != "vllm-awq-gemm"
            ]
            write(altered / "targets.json", targets)
            target_name = "reproduction/paper_results/targets.json"
            with tarfile.open(altered / "evidence.tar.gz") as archive:
                entries = [(m.name, archive.extractfile(m).read()) for m in archive]
            with tarfile.open(altered / "evidence.tar.gz", "w:gz") as archive:
                for name, data in entries:
                    if name == target_name:
                        data = (altered / "targets.json").read_bytes()
                    info = tarfile.TarInfo(name)
                    info.size = len(data)
                    archive.addfile(info, io.BytesIO(data))
            hashes = read(altered / "evidence-manifest.json")
            hashes[target_name] = sha(altered / "targets.json")
            write(altered / "evidence-manifest.json", hashes)
            rehash(altered, archive_changed=True)
            code, log = execute("missing-production-case", altered)
            if code == 0 or "Production case inventory differs from manuscript" not in log:
                raise RuntimeError("Production inventory control failed: " + log)
            results.append({
                "name": "missing-production-case", "accepted": False,
                "fully_rehashed": True, "gate": "actual manuscript production table",
            })
        altered = root / "traversal"
        shutil.copytree(snapshot, altered)
        with tarfile.open(altered / "evidence.tar.gz") as archive:
            entries = [(m.name, archive.extractfile(m).read()) for m in archive]
        unsafe = "../lark-paper-control-" + uuid.uuid4().hex
        entries.append((unsafe, b"must not be extracted"))
        with tarfile.open(altered / "evidence.tar.gz", "w:gz") as archive:
            for name, data in entries:
                info = tarfile.TarInfo(name)
                info.size = len(data)
                archive.addfile(info, io.BytesIO(data))
        hashes = read(altered / "evidence-manifest.json")
        hashes[unsafe] = hashlib.sha256(entries[-1][1]).hexdigest()
        write(altered / "evidence-manifest.json", hashes)
        rehash(altered, archive_changed=True)
        code, log = execute("fully-rehashed-traversal", altered)
        if code == 0 or "Unsafe path: " + unsafe not in log:
            raise RuntimeError("Wrong traversal-control outcome: " + log)
        results.append(
            {
                "name": "fully-rehashed-traversal",
                "accepted": False,
                "fully_rehashed": True,
                "gate": "safe archive path",
            }
        )
        wrong = root / "wrong-manuscript.tar"
        wrong.write_bytes(b"wrong manuscript bytes")
        code, log = execute("wrong-manuscript", isolated, wrong)
        if code == 0 or "Unexpected manuscript archive" not in log:
            raise RuntimeError("Wrong manuscript-control outcome: " + log)
        results.append(
            {"name": "wrong-manuscript", "accepted": False, "gate": "pinned manuscript digest"}
        )
    write(
        out / "results.json",
        {
            "status": "passed",
            "checks": results,
            "positive_replays": 1,
            "negative_controls": sum(not row["accepted"] for row in results),
            "source_snapshot_manifest_sha256": sha(snapshot / "manifest.json"),
            "replayer_sha256": sha(Path(__file__).with_name("replay_snapshot.py")),
            "control_runner_sha256": sha(Path(__file__)),
            "fresh_lean_checks": 0,
            "fresh_gpu_trials": 0,
            "model_calls": 0,
            "original_paper_fully_reproduced": False,
        },
    )
    write(out / "manifest.json", {n: sha(out / n) for n in sorted(file_set(out))})
    print(
        json.dumps(
            {
                "status": "passed",
                "outside_checkout_without_git": True,
                "positive_replays": 1,
                "negative_controls": sum(not row["accepted"] for row in results),
                "fresh_lean_checks": 0,
                "fresh_gpu_trials": 0,
                "model_calls": 0,
            }
        )
    )


if __name__ == "__main__":
    main()
