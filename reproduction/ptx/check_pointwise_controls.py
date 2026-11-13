"""Fresh replay and four direct Lean source-binding controls for the full-size PTX ReLU."""

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from lark_kernels import ptx_pointwise as reader  # noqa: E402
from lark_kernels import ptx_pointwise_certificate as checker  # noqa: E402

KERNEL_SHA256 = "7796e78074f76e2955dee35860c6ca3cb0dcc3263e9115480c9d57b66b676848"
MUTATIONS = {
    "wrong-arithmetic": (r"\bmax\.f32\b", "add.rn.f32"),
    "misaligned-byte-stride": (r"%rd5,\s*%r1,\s*2;", "%rd5, %r1, 1;"),
    "wrong-output-address": (r"\bst\.global\.u16\s+\[%rd7\],\s*%rs2;",
                             "st.global.u16 [%rd6], %rs2;"),
    "skipped-half-conversion": (r"\bcvt\.f32\.f16\s+%f1,\s*%rs1;", ""),
}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("recording", "output", "lean"):
        parser.add_argument("--" + name, required=True, type=Path)
    args = parser.parse_args()
    output = checker.fresh_output(args.output)
    recording = args.recording.resolve()
    checker.check_inventory(recording)
    source = (recording / "kernel.ptx").read_bytes()
    checker.require(hashlib.sha256(source).hexdigest() == KERNEL_SHA256,
                    "The exact recorded full-size compiler-study ReLU source is required")
    output.mkdir(parents=True)
    (output / "driver.py").write_bytes(Path(__file__).read_bytes())
    replay = output / "positive-source-only-replay"
    positive = checker.check_export(recording, replay, args.lean)
    lean, _ = checker.toolchain(args.lean)
    environment = os.environ.copy()
    environment["LEAN_PATH"] = str(replay / "modules")
    base = {name: (recording / name).read_bytes() for name in checker.INPUTS}
    report = {
        "schema": 1, "status": "direct-PTX-source-controls-in-progress",
        "checked_at_utc": datetime.now(timezone.utc).isoformat(),
        "recording_manifest_sha256": checker.sha((recording / "manifest.json").read_bytes()),
        "driver_sha256": checker.sha(Path(__file__).read_bytes()),
        "positive_controls": 1, "positive": positive, "negative_controls": [],
        "source_bound_proofs_added": 0, "new_registered_source_certificates": 0,
        "model_calls": 0, "gpu_trials": 0, "nvidia_execution": False,
        "original_paper_fully_reproduced": False,
        "scope": "A new source-only replay compiles all three trusted owned modules and checks "
                 "the positive Main. Four accepted-grammar PTX mutations then pass through "
                 "the actual reader and immutable renderer and are rejected directly by "
                 "Lean at the source-program equality proof, using those freshly compiled "
                 "imports. Shapes, dtypes, geometry and original CUDA contract fuel remain "
                 "unchanged. These are fixed-profile binding controls, not a general "
                 "kernel-falsity classifier or the paper's original42 mutants.",
    }
    checker.write(output / "results.json", report)
    for name, (pattern, replacement) in MUTATIONS.items():
        altered, replacements = re.subn(pattern, replacement, source.decode())
        checker.require(replacements == 1, "A control must change exactly one source fragment")
        data = {**base, "kernel.ptx": altered.encode()}
        prepared = reader.prepare(*(data[key].decode() for key in checker.INPUTS))
        task, translation, _ = prepared
        checker.require(task.grid == task.buffers[0].size == 16384
                        and task.block == 1 and task.warp == 32
                        and task.fuel == (4, 1, 1, 1)
                        and all(buffer.dtype == "float16" for buffer in task.buffers),
                        "A source control changed the reference contract")
        main = reader.render(*prepared)
        folder = output / name
        folder.mkdir()
        for key, value in data.items():
            (folder / key).write_bytes(value)
        (folder / "Main.lean").write_text(main)
        checker.write(folder / "translation.json", translation.data())
        check, log = checker.run_lean(lean, ["Main.lean"], folder, environment,
                                      folder / "Main.log")
        proof_line = next(i + 1 for i, line in enumerate(main.splitlines())
                          if line.startswith("theorem source_program "))
        errors = [int(value) for value in re.findall(r"Main\.lean:([0-9]+):[0-9]+: error:", log)]
        checker.require(check["exit_code"] != 0 and not check["timed_out"]
                        and proof_line in errors
                        and ("tactic 'rfl' failed" in log or "type mismatch" in log)
                        and not any(marker in log for marker in
                                    ("maximum recursion", "maximum number of heartbeats",
                                     "maximum heartbeats", "Stack overflow")),
                        "Control did not reach the expected bounded Lean source-binding refusal")
        row = {"control": name, "reader_accepted": True, "source_fragments_changed": 1,
               "source_sha256": checker.sha(data["kernel.ptx"]),
               "main_sha256": checker.sha(main.encode()),
               "PTX_instructions": len(translation.instructions),
               "Lean": check, "channel": "source-program-equality-proof-refused",
               "general_kernel_falsity_claim": False,
               "all_shapes_dtypes_geometry_and_CUDA_fuel_unchanged": True}
        checker.write(folder / "results.json", row)
        report["negative_controls"].append(row)
        checker.write(output / "results.json", report)
        print(json.dumps({"control": name, "reader_accepted": True,
                          "Lean_source_binding_refused": True}), flush=True)
    report.update(status="full-size-PTX-ReLU-source-controls-passed",
                  direct_Lean_negative_controls=4, timeouts=0,
                  owned_modules_freshly_compiled=3, old_owned_olean_cache_used=False,
                  negative_control_imports="source-checked imports from the fresh positive replay")
    checker.write(output / "results.json", report)
    checker.manifest(output)


if __name__ == "__main__":
    main()
