"""Fresh full FFN replay and four direct bounded Lean refusal controls."""

import argparse
import copy
from datetime import datetime, timezone
import os
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from lark_kernels import ptx_ffn as reader  # noqa: E402
from lark_kernels import ptx_ffn_certificate as checker  # noqa: E402

SOURCE_SHA256 = (
    "299d828a47a8387a62a3da1dc1de6fa2d053fd2dffefaf150cc40ffdfd6de0e0",
    "8a2098b08ca67dd40f62e5ddf5e83d445c6dcdbb9a68875e55051f761c6b5413",
)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("recording", "output", "lean"):
        parser.add_argument("--" + name, required=True, type=Path)
    args = parser.parse_args()
    output, recording = checker.fresh_output(args.output), args.recording.resolve()
    checker.check_inventory(recording)
    inputs = {name: (recording / name).read_bytes() for name in checker.INPUTS}
    checker.require(tuple(checker.sha(inputs[stage + "/kernel.ptx"]) for stage in ("up", "down"))
                    == SOURCE_SHA256, "The exact original independently compiled stages are required")
    output.mkdir(parents=True)
    (output / "driver.py").write_bytes(Path(__file__).read_bytes())
    replay = output / "positive-source-only-replay"
    positive = checker.check_export(recording, replay, args.lean)
    lean, _ = checker.toolchain(args.lean)
    environment = dict(os.environ, LEAN_PATH=str(replay / "modules"))
    main_source = (replay / "Main.lean").read_text()
    report = {
        "schema": 1, "status": "direct-PTX-FFN-source-controls-in-progress",
        "checked_at_utc": datetime.now(timezone.utc).isoformat(),
        "driver_sha256": checker.sha(Path(__file__).read_bytes()),
        "recording_manifest_sha256": checker.sha((recording / "manifest.json").read_bytes()),
        "positive_replay": positive, "positive_controls": 1, "negative_controls": [],
        "source_bound_proofs_added": 0, "new_registered_source_certificates": 0,
        "model_calls": 0, "gpu_trials": 0, "nvidia_execution": False,
        "original_paper_fully_reproduced": False,
        "scope": "Fresh source-only replay of the exact complete two-launch FFN proof. "
                 "Two accepted-grammar PTX mutations traverse the actual frontend/render path. "
                 "One direct reference-constructor mutation bypasses Python preflight. One direct "
                 "host-composition source mutation disconnects the actual intermediate. All four "
                 "must fail at the specified Lean proof, without resource failures or timeouts. "
                 "Negative controls use only the just-source-built positive imports. Original "
                 "shapes, launches, CUDA fuel and resource caps remain unchanged. These are "
                 "proof-binding/dependency controls, not a general falsity classifier or the "
                 "paper's original 42 mutants, and add no hardware/model/paper result.",
    }
    checker.write(output / "results.json", report)
    changes = (
        ("up-ReLU-replaced-by-addition", "up/kernel.ptx", "exact_up"),
        ("down-reduction-bound-shortened", "down/kernel.ptx", "exact_down"),
        ("intermediate-half-cast-removed", None, "original_reference"),
        ("down-launch-disconnected-from-up-memory", None, "actual_intermediate_shared"),
    )
    for label, input_name, gate in changes:
        case = output / label
        case.mkdir()
        data = dict(inputs)
        filename = "Main.lean"
        if input_name:
            pattern, replacement = (
                (r"\bmax\.f32\s+%f67,\s*%f69,\s*%f68;", "add.rn.f32 %f67, %f69, %f68;")
                if input_name.startswith("up/") else
                (r"\bsetp\.ne\.s32\s+%p1,\s*%r27,\s*1024;", "setp.ne.s32 %p1, %r27, 256;")
            )
            altered, count = re.subn(pattern, replacement, data[input_name].decode())
            checker.require(count == 1, "Each source control changes exactly one fragment")
            data[input_name] = altered.encode()
            prepared = reader.prepare(*(data[name].decode() for name in checker.INPUTS))
            generated = reader.render(*prepared)
            checker.write(case / "translation.json", [tr.data() for tr in prepared[1]])
            checker.write(case / "scope.json", checker.scope_fields(*prepared[:2]))
        elif gate == "original_reference":
            tree = copy.deepcopy(reader.REFERENCE)
            checker.require(tree[1][1][1][0] == "toHalf", "Expected original intermediate cast")
            before = "(.fromHalf (.toHalf (.relu"
            checker.require(main_source.count(before) == 1, "Expected unique intermediate cast")
            generated = main_source.replace(before, "(.fromHalf (.fromHalf (.relu")
            checker.write(case / "bypass.json", {
                "scope": "Direct closed Lean reference-constructor mutation bypasses strict Python AST preflight",
                "all_input_bytes_unchanged": True, "before": before,
                "after": "(.fromHalf (.fromHalf (.relu",
            })
        else:
            filename = "DisconnectedPipeline.lean"
            source = checker.own_sources()["lean/Lark/PtxFeedForwardPipeline.lean"].decode()
            before = "  view downRenaming (afterUp counts ops input outside)"
            after = "  view downRenaming (initial layout input outside)"
            checker.require(source.count(before) == 1, "Expected unique actual intermediate view")
            generated = source.replace(before, after)
            checker.write(case / "bypass.json", {
                "scope": "Direct trusted-library proof dependency control, bypassing source-binding inventory preflight",
                "all_input_bytes_unchanged": True, "before": before, "after": after,
            })
        for name, content in data.items():
            target = case / name
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(content)
        (case / filename).write_text(generated)
        lines = generated.splitlines()
        first = next(i + 1 for i, line in enumerate(lines) if line.startswith("theorem " + gate + " "))
        last = next((i + 1 for i, line in enumerate(lines) if i + 1 > first and line.startswith("theorem ")), len(lines))
        checker.write(output / "progress.json", {"pid": os.getpid(), "stage": label,
                      "expected_gate": gate, "expected_lines": [first, last - 1]})
        row, log = checker.run_lean(lean, [filename], case, environment, case / "Lean.log")
        errors = [int(n) for n in re.findall(re.escape(filename) + r":([0-9]+):[0-9]+: error:", log)]
        at_gate = any(first <= line < last for line in errors)
        resource_failure = any(marker in log.lower() for marker in (
            "stack overflow", "maximum number of heartbeats", "maximum heartbeats",
            "maximum recursion", "deep recursion",
        ))
        passed = row["exit_code"] != 0 and not row["timed_out"] and at_gate and not resource_failure
        result = {
            "control": label, "expected_gate": gate, "expected_lines": [first, last - 1],
            "reader_accepted": input_name is not None, "preflight_bypassed": input_name is None,
            "Lean": row, "expected_rejection_verified": passed,
            "rejected_at_expected_gate": at_gate, "resource_failure": resource_failure,
            "source_sha256": checker.sha(generated.encode()),
            "input_bindings": {name: checker.sha(content) for name, content in data.items()},
            "all_shapes_dtypes_geometry_and_CUDA_fuel_unchanged": True,
            "general_kernel_falsity_claim": False,
        }
        checker.write(case / "results.json", result)
        checker.manifest(case)
        report["negative_controls"].append(result)
        checker.write(output / "results.json", report)
        checker.require(passed, "Control did not reach the expected bounded Lean refusal: " + label)
        print({"control": label, "expected_rejection_verified": passed}, flush=True)
    report.update(status="all-four-direct-Lean-FFN-controls-rejected", direct_Lean_negative_controls=4,
                  timeouts=0, resource_limit_failures=0, owned_modules_freshly_compiled=14,
                  old_owned_olean_cache_used=False,
                  negative_control_imports="source-checked imports from the fresh positive replay")
    checker.write(output / "results.json", report)
    checker.manifest(output)


if __name__ == "__main__":
    main()
