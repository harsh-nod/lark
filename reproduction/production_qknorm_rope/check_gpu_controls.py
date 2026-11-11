"""Reject fully rehashed numerical and proof-scope changes without GPU launches."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def replace(path, content):
    # Control trees share read-only files through hard links; replace modified
    # paths atomically so the authoritative input/runtime packet stays intact.
    temporary = path.with_name(path.name + ".changed")
    temporary.write_bytes(content)
    temporary.replace(path)


def write(path, value):
    replace(path, (json.dumps(value, indent=2) + "\n").encode())


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--host", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    inputs, host = args.input.resolve(), args.host.resolve()
    before = {str(p): sha(p) for folder in (inputs, host) for p in folder.rglob("*") if p.is_file()}
    checks = []
    with tempfile.TemporaryDirectory(prefix="lark-fused-qk-numerical-controls-") as temporary:
        base = Path(temporary)
        for name in ("wrong-output", "invented-whole-launch", "invented-ieee-proof",
                     "invented-certificate", "missing-trial", "widened-tolerance"):
            data, runtime, result = base / (name + "-input"), base / (name + "-host"), base / (name + "-audit")
            shutil.copytree(inputs, data, copy_function=os.link)
            shutil.copytree(host, runtime, copy_function=os.link)
            report = json.loads((runtime / "results.json").read_text())
            manifest = json.loads((runtime / "manifest.json").read_text())
            if name == "wrong-output":
                path = runtime / "interleaved-adapted.bin"
                replace(path, b"\x00\x7e" + path.read_bytes()[2:])
                report["output_sha256"][path.name[:-4]] = sha(path)
                manifest[path.name] = sha(path)
            elif name == "invented-whole-launch":
                report["whole_kernel_execution_proved"] = True
            elif name == "invented-ieee-proof":
                report["ieee_equivalence_proved"] = True
            elif name == "invented-certificate":
                report["source_certificates"] = 1
            elif name == "missing-trial":
                report["cases"].pop()
                report["trials"], report["launches"] = 47, 94
            else:
                metadata = json.loads((data / "dataset.json").read_text())
                metadata["atol"] = .02
                write(data / "dataset.json", metadata)
                binding = json.loads((data / "manifest.json").read_text())
                binding["files"]["dataset.json"] = sha(data / "dataset.json")
                write(data / "manifest.json", binding)
                report["input_manifest_sha256"] = sha(data / "manifest.json")
            write(runtime / "results.json", report)
            manifest["results.json"] = sha(runtime / "results.json")
            write(runtime / "manifest.json", manifest)
            run = subprocess.run([sys.executable, str(Path(__file__).with_name("audit_gpu.py")),
                                  "--input", str(data), "--host", str(runtime), "--output", str(result)],
                                 capture_output=True, text=True, timeout=90)
            log = run.stdout + run.stderr
            (out / (name + ".log")).write_text(log)
            wanted = ("Fresh CPU reference failed" if name == "wrong-output" else
                      "Pinned numerical scope differs" if name == "widened-tolerance" else "Host scope/trial/guard differs")
            if run.returncode == 0 or wanted not in log:
                raise ValueError("Wrong numerical-control outcome: " + name + ": " + log)
            checks.append({"name": name, "accepted": False, "fully_rehashed": True, "reason": wanted})
    if any(sha(Path(name)) != expected for name, expected in before.items()):
        raise ValueError("Authoritative packet changed during negative controls")
    report = {"schema": 1, "status": "fully-rehashed-native-fused-qknorm-rope-numerical-controls-rejected",
              "checks": checks, "negative_controls": len(checks), "authoritative_packets_unchanged": True,
              "input_manifest_sha256": sha(inputs / "manifest.json"), "runtime_manifest_sha256": sha(host / "manifest.json"),
              "auditor_sha256": sha(Path(__file__).with_name("audit_gpu.py")), "checker_sha256": sha(Path(__file__)),
              "model_calls": 0, "new_gpu_trials": 0, "original_paper_fully_reproduced": False}
    (out / "results.json").write_text(json.dumps(report, indent=2) + "\n")
    (out / "manifest.json").write_text(json.dumps({p.name: sha(p) for p in sorted(out.iterdir()) if p.is_file()}, indent=2) + "\n")
    print(json.dumps({"status": report["status"], "negative_controls": len(checks)}))


if __name__ == "__main__":
    main()
