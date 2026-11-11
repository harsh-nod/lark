"""Reject rehashed real-softmax scope changes before archive extraction."""

import argparse
import copy
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--packet", type=Path, required=True)
    parser.add_argument("--earlier-packet", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--lean-bin", type=Path, required=True)
    args = parser.parse_args()
    out = args.output.resolve()
    if any((p / ".git").exists() for p in (out, *out.parents)):
        raise ValueError("Choose fresh output outside Git")
    out.mkdir(parents=True, exist_ok=False)
    current = json.loads((args.packet / "results.json").read_text())
    from reproduction.production_softmax.replay_native_real import TRUE_CLAIMS, FALSE_CLAIMS
    missing = "Missing canonical-real whole-grid claims"
    scope = "Wrong canonical-real interpretation/counts/fuel"
    invented = "Invented IEEE/original/certificate/cache claim"
    principal = "Canonical-real principal audits absent"
    scenarios = [
        ("invented-certificate", {"source_certificates": 1}, scope),
        ("boolean-certificate", {"source_certificates": False}, scope),
        ("ieee-half-conversions", {"half_conversions": "IEEE binary16"}, scope),
        ("infinite-real-seed", {"reserved_seed": "negative infinity"}, scope),
        ("approximate-exponential", {"real_exponential": "GPU approximate exp"}, scope),
        ("wrong-uniform-output", {"uniform_output": "1/50256"}, scope),
        ("changed-mathlib-revision", {"mathlib_revision": "0" * 40}, scope),
        ("both-source-grids", {"whole_grid_variants": ["original", "fixed"]}, scope),
        ("wrong-original-fuel", {"original_fuel": {"lane": 4096, "warp": 8, "block": 6, "grid": 1}}, scope),
        ("boolean-original-fuel", {"original_fuel": {"lane": 4096, "warp": 8, "block": 5, "grid": True}}, scope),
        ("omitted-real-refusal", {}, "Wrong canonical-real replay checks"),
        ("earlier-block-relabeled-real", {}, principal),
    ]
    scenarios += [("omitted-" + key, {key: False}, missing) for key in TRUE_CLAIMS]
    scenarios += [("invented-" + key, {key: True}, invented) for key in FALSE_CLAIMS]
    scenarios += [("integer-reference-claim", {"canonical_source_equivalence_proved": 1}, missing)]
    for key in ("local_lean_modules", "standard_lean_modules", "real_lean_modules", "false_lean_claims_rejected"):
        scenarios += [("wrong-" + key, {key: current[key] + 1}, scope),
                      ("boolean-" + key, {key: True}, scope)]
    audited = (
        "source_canonical_correct", "source_canonical_extract", "source_canonical_output", "source_uniform_output",
        "LarkReal.NativeSoftmax.canonical_correct", "LarkReal.NativeSoftmax.source_denominator_pos",
        "LarkReal.NativeSoftmax.row_sum_exponentials", "LarkNativeSoftmax.source_order_correct",
    )
    scenarios += [("omitted-audit-" + name.replace(".", "-"), {}, principal) for name in audited]
    records = []
    for name, changes, reason in scenarios:
        original = args.earlier_packet if name == "earlier-block-relabeled-real" else args.packet
        folder = out / name
        packet = folder / "packet"
        packet.mkdir(parents=True)
        manifest = json.loads((original / "manifest.json").read_text())
        for filename, digest in manifest.items():
            if Path(filename).name != filename or sha(original / filename) != digest:
                raise ValueError("Original packet hash/path differs")
            shutil.copyfile(original / filename, packet / filename)
        report = json.loads((packet / "results.json").read_text())
        if name == "earlier-block-relabeled-real":
            old_audits, old_archive = report["axiom_audits"], report["source_archive_sha256"]
            report = copy.deepcopy(current)
            report["axiom_audits"], report["source_archive_sha256"] = old_audits, old_archive
        report.update(changes)
        if name == "omitted-real-refusal":
            report["checks"] = [c for c in report["checks"] if c["name"] != "uniform-dropped-column"]
        if name.startswith("omitted-audit-"):
            key = next(k for k in audited if name == "omitted-audit-" + k.replace(".", "-"))
            del report["axiom_audits"][key]
        (packet / "results.json").write_text(json.dumps(report, indent=2) + "\n")
        (packet / "manifest.json").write_text(json.dumps({p.name: sha(p) for p in sorted(packet.iterdir())
                                                          if p.name != "manifest.json"}, indent=2) + "\n")
        target = folder / "attempted-replay"
        command = [sys.executable, str(HERE / "replay_native_real.py"), "--packet", str(packet),
                   "--output", str(target), "--lean-bin", str(args.lean_bin),
                   "--dependency-project", str(HERE.parents[1] / "lean-real")]
        run = subprocess.run(command, capture_output=True, text=True, timeout=30)
        log = run.stdout + run.stderr
        (out / (name + ".log")).write_text(log)
        if run.returncode == 0 or reason not in log or target.exists():
            raise ValueError("Wrong real stage rejection: " + name + "\n" + log)
        records.append({"name": name, "exit_code": run.returncode, "expected_reason": reason,
                        "packet_rehashed": True, "rejected_before_extraction": True})
    report = {
        "schema": 1, "status": "fully-rehashed-false-softmax-real-stage-claims-rejected-before-extraction",
        "checks": records, "real_packet_manifest_sha256": sha(args.packet / "manifest.json"),
        "earlier_packet_manifest_sha256": sha(args.earlier_packet / "manifest.json"),
        "replayer_sha256": sha(HERE / "replay_native_real.py"), "source_certificates": 0,
        "ieee_equivalence_proved": False, "original_paper_fully_reproduced": False,
    }
    (out / "results.json").write_text(json.dumps(report, indent=2) + "\n")
    shutil.copyfile(Path(__file__), out / "checker.py")
    (out / "manifest.json").write_text(json.dumps({p.name: sha(p) for p in sorted(out.iterdir()) if p.is_file()}, indent=2) + "\n")
    print(json.dumps({"status": report["status"], "checks": len(records)}))


if __name__ == "__main__":
    sys.path.insert(0, str(HERE.parents[1]))
    main()
