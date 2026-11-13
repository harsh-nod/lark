"""Fresh replay and four direct Lean source-binding controls for compiled Linear."""

import argparse
from datetime import datetime, timezone
import os
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from lark_kernels import ptx_linear as reader  # noqa: E402
from lark_kernels import ptx_linear_certificate as checker  # noqa: E402

KERNEL_SHA256 = "5ae52a2a03b700ffebe4de2d10c69e9fc3f34dea2d99e1bd3ad1c2472ef6e273"
MUTATIONS = {
    "wrong-product": (r"\bmul\.rn\.f32\s+%f36,\s*%f4,\s*%f5;", "add.rn.f32 %f36, %f4, %f5;"),
    "wrong-sign-extension-source": (r"\bcvt\.s64\.s32\s+%rd18,\s*%r11;", "cvt.s64.s32 %rd18, %r10;"),
    "wrong-bias-shift": (r"\bshl\.b64\s+%rd48,\s*%rd18,\s*1;", "shl.b64 %rd48, %rd18, 2;"),
    "wrong-bias-operation": (r"\badd\.rn\.f32\s+%f68,\s*%f69,\s*%f67;", "mul.rn.f32 %f68, %f69, %f67;"),
}



def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("recording", "output", "lean"):
        parser.add_argument("--" + name, required=True, type=Path)
    args = parser.parse_args()
    output, recording = checker.fresh_output(args.output), args.recording.resolve()
    checker.check_inventory(recording)
    source = (recording / "kernel.ptx").read_bytes()
    checker.require(checker.sha(source) == KERNEL_SHA256, "Exact original independent compiled Linear source required")
    output.mkdir(parents=True)
    (output / "driver.py").write_bytes(Path(__file__).read_bytes())
    replay = output / "positive-source-only-replay"
    positive = checker.check_export(recording, replay, args.lean)
    lean, _ = checker.toolchain(args.lean)
    environment = dict(os.environ, LEAN_PATH=str(replay / "modules"))
    base = {name: (recording / name).read_bytes() for name in checker.INPUTS}
    report = {
        "schema": 1, "status": "direct-PTX-LINEAR-source-controls-in-progress",
        "checked_at_utc": datetime.now(timezone.utc).isoformat(),
        "recording_manifest_sha256": checker.sha((recording / "manifest.json").read_bytes()),
        "driver_sha256": checker.sha(Path(__file__).read_bytes()),
        "positive_controls": 1, "positive": positive, "negative_controls": [],
        "source_bound_proofs_added": 0, "new_registered_source_certificates": 0,
        "model_calls": 0, "gpu_trials": 0, "nvidia_execution": False,
        "original_paper_fully_reproduced": False,
        "scope": "One new source-only replay compiles all ten trusted owned modules and checks the "
                 "positive full-size Main. Four accepted-grammar PTX mutations go through the actual "
                 "lossless reader and immutable renderer and fail directly in Lean at source_program. "
                 "Negative checks use the just-source-compiled positive imports. The [64,256] times [256,512] plus bias[512] FP16 "
                 "shapes, 32768/1/32 launch and original CUDA fuel [1030,1,1,1] remain unchanged. "
                 "These are fixed-profile source-binding controls, not a general kernel-falsity "
                 "classifier, NVIDIA experiment or the paper's original 42 mutants.",
    }
    checker.write(output / "results.json", report)
    for name, (pattern, replacement) in MUTATIONS.items():
        altered, replacements = re.subn(pattern, replacement, source.decode())
        checker.require(replacements == 1, "A control must change exactly one source fragment")
        data = {**base, "kernel.ptx": altered.encode()}
        prepared = reader.prepare_certificate(*(data[key].decode() for key in checker.INPUTS))
        task, translation, reference = prepared
        checker.require([b.shape for b in task.buffers] == [(64, 256), (256, 512), (512,), (64, 512)]
                        and all(b.dtype == "float16" for b in task.buffers)
                        and (task.grid, task.block, task.warp) == (32768, 1, 32)
                        and task.fuel == (1030, 1, 1, 1), "A control changed the unchanged reference contract")
        main = reader.render(*prepared)
        folder = output / name
        folder.mkdir()
        for key, content in data.items():
            (folder / key).write_bytes(content)
        (folder / "Main.lean").write_text(main)
        checker.write(folder / "translation.json", translation.data())
        checker.write(folder / "reference-ast.json", reference)
        check, log = checker.run_lean(lean, ["Main.lean"], folder, environment, folder / "Main.log")
        proof_line = next(i+1 for i, line in enumerate(main.splitlines()) if line.startswith("theorem source_program "))
        errors = [int(value) for value in re.findall(r"Main\.lean:([0-9]+):[0-9]+: error:", log)]
        checker.require(check["exit_code"] != 0 and not check["timed_out"] and proof_line in errors
                        and ("tactic 'decide' proved that" in log and "is false" in log)
                        and not any(marker in log for marker in ("maximum recursion", "maximum number of heartbeats",
                                                                "maximum heartbeats", "Stack overflow")),
                        "Control did not reach the expected bounded Lean source-program refusal")
        row = {"control": name, "reader_accepted": True, "source_fragments_changed": 1,
               "source_sha256": checker.sha(data["kernel.ptx"]), "main_sha256": checker.sha(main.encode()),
               "PTX_instructions": len(translation.instructions), "Lean": check,
               "channel": "source-program-equality-proof-refused", "general_kernel_falsity_claim": False,
               "all_shapes_dtypes_geometry_and_CUDA_fuel_unchanged": True}
        checker.write(folder / "results.json", row)
        report["negative_controls"].append(row)
        checker.write(output / "results.json", report)
        print({"control": name, "reader_accepted": True, "Lean_source_binding_refused": True}, flush=True)
    report.update(status="full-size-PTX-LINEAR-source-controls-passed", direct_Lean_negative_controls=4,
                  timeouts=0, owned_modules_freshly_compiled=10, old_owned_olean_cache_used=False,
                  negative_control_imports="source-checked imports from the fresh positive replay")
    checker.write(output / "results.json", report)
    checker.manifest(output)


if __name__ == "__main__":
    main()
