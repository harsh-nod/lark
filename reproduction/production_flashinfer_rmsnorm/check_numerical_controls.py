"""Reject fully rehashed wrong outputs, missing trials and numerical overclaims."""

import argparse
import json
import os
from pathlib import Path
import shutil
import struct
import subprocess
import sys
import tempfile

from audit_gpu import sha, verify


def replace(path, content):
    # Copied packets use hard links for immutable large streams. Replacing the
    # inode, rather than writing through it, keeps the original evidence intact.
    temporary = path.with_name(path.name + ".replacement")
    temporary.write_bytes(content)
    temporary.replace(path)


def write(path, value):
    replace(path, (json.dumps(value, indent=2) + "\n").encode())


def rehash_host(host, data):
    report = json.loads((host / "results.json").read_text())
    report["input_manifest_sha256"] = sha(data / "manifest.json")
    report["output_sha256"] = {name: sha(host / (name + ".bin")) for name in ("adapted", "upstream")}
    write(host / "results.json", report)
    manifest = json.loads((host / "manifest.json").read_text())
    write(host / "manifest.json", {name: sha(host / name) for name in manifest})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--host", type=Path, action="append", required=True)
    parser.add_argument("--baseline", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    data, hosts = args.input.resolve(), [p.resolve() for p in args.host]
    if len(hosts) != 2 or len(set(hosts)) != 2:
        raise ValueError("Two distinct host packets required")
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    baseline = json.loads(args.baseline.read_text())
    auditor = Path(__file__).with_name("audit_gpu.py")
    if (baseline["status"] != "passed" or baseline["tolerance_failures"] != 0
            or baseline["input_manifest_sha256"] != sha(data / "manifest.json")
            or baseline["auditor_sha256"] != sha(auditor)
            or [h["report_sha256"] for h in baseline["hosts"]] != [sha(h / "results.json") for h in hosts]):
        raise ValueError("Checked positive baseline does not match the actual packets")
    mutations = [
        ("one-wrong-output", "Numerical tolerance failed"),
        ("missing-final-store", "Numerical tolerance failed"),
        ("widened-tolerance", "Fixed numerical tolerance differs"),
        ("invented-whole-launch", "Unsupported numerical-evidence proof/completion scope"),
        ("invented-paper-completion", "Unsupported numerical-evidence proof/completion scope"),
        ("boolean-certificate-count", "Unsupported numerical-evidence proof/completion scope"),
        ("invented-ieee-proof", "Unsupported numerical-evidence proof/completion scope"),
        ("missing-trial", "Runtime trial missing"),
        ("changed-readonly-input", "Runtime guard/trial record differs"),
    ]
    checks = []
    with tempfile.TemporaryDirectory(prefix="lark-flashinfer-numerical-controls-") as temporary:
        root = Path(temporary)
        for name, gate in mutations:
            work = root / name
            altered_data = work / "input"
            altered_hosts = [work / "host0", work / "host1"]
            shutil.copytree(data, altered_data, copy_function=os.link)
            for original, target in zip(hosts, altered_hosts):
                shutil.copytree(original, target, copy_function=os.link)
            metadata = json.loads((altered_data / "dataset.json").read_text())
            report = json.loads((altered_hosts[0] / "results.json").read_text())
            if name in ("one-wrong-output", "missing-final-store"):
                path = altered_hosts[0] / "adapted.bin"
                raw = bytearray(path.read_bytes())
                if name == "one-wrong-output":
                    raw[:2] = struct.pack("<e", 64.)
                else:
                    raw[-2:] = b"\x00\x7e"
                replace(path, raw)
            elif name == "widened-tolerance":
                metadata["atol"] = metadata["rtol"] = .02
            elif name == "invented-whole-launch":
                report["whole_kernel_execution_proved"] = True
            elif name == "invented-paper-completion":
                metadata["original_paper_fully_reproduced"] = True
            elif name == "boolean-certificate-count":
                metadata["source_certificates"] = False
            elif name == "invented-ieee-proof":
                metadata["ieee_equivalence_proved"] = True
            elif name == "missing-trial":
                report["cases"].pop()
            elif name == "changed-readonly-input":
                report["cases"][0]["input_unchanged"] = False
            write(altered_data / "dataset.json", metadata)
            write(altered_hosts[0] / "results.json", report)
            manifest = json.loads((altered_data / "manifest.json").read_text())
            manifest["files"]["dataset.json"] = sha(altered_data / "dataset.json")
            write(altered_data / "manifest.json", manifest)
            for target in altered_hosts:
                rehash_host(target, altered_data)
            output = work / "audit.json"
            command = [sys.executable, str(auditor), "--input", str(altered_data),
                       "--host", str(altered_hosts[0]), "--host", str(altered_hosts[1]),
                       "--output", str(output)]
            checked = subprocess.run(command, text=True, capture_output=True, timeout=180)
            log = checked.stdout + checked.stderr
            (out / (name + ".log")).write_text(log)
            if checked.returncode == 0 or gate not in log:
                raise ValueError("Unexpected numerical control outcome: " + name + "\n" + log)
            result = {"name": name, "accepted": False, "fully_rehashed": True, "gate": gate}
            if name in ("one-wrong-output", "missing-final-store"):
                failed = json.loads(output.read_text())
                if failed["status"] != "failed" or failed["tolerance_failures"] < 1:
                    raise ValueError("Wrong output was not rejected numerically")
                shutil.copyfile(output, out / (name + ".json"))
                result["tolerance_failures"] = failed["tolerance_failures"]
            checks.append(result)
            print(json.dumps(result), flush=True)
            shutil.rmtree(work)
    # Check the complete original streams, not just their unchanged manifests.
    verify(data, json.loads((data / "manifest.json").read_text())["files"])
    for host in hosts:
        verify(host, json.loads((host / "manifest.json").read_text()))
    result = {"schema": 1, "status": "fully-rehashed-numerical-controls-passed",
              "checks": checks, "negative_controls": len(checks),
              "actual_input_and_runtime_packets_unchanged": True,
              "input_manifest_sha256": sha(data / "manifest.json"),
              "runtime_manifests_sha256": [sha(h / "manifest.json") for h in hosts],
              "baseline_sha256": sha(args.baseline), "auditor_sha256": sha(auditor),
              "checker_sha256": sha(Path(__file__)), "model_calls": 0,
              "new_gpu_trials": 0, "original_paper_fully_reproduced": False}
    (out / "results.json").write_text(json.dumps(result, indent=2) + "\n")
    (out / "manifest.json").write_text(json.dumps({p.name: sha(p) for p in sorted(out.iterdir())
                                                  if p.is_file()}, indent=2) + "\n")
    print(json.dumps({"status": result["status"], "negative_controls": len(checks)}), flush=True)


if __name__ == "__main__":
    main()
