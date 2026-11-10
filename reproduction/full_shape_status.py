"""Audit and summarize full-shape independent contracts without claiming paper completeness."""

import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
STUDIES = {
    "pointwise": {"relu": "ReLU", "silu": "SiLU", "gelu": "GELU (tanh)"},
    "reduction": {"gemv": "GEMV"},
    "matrix": {"gemm": "GEMM", "bmm": "Batched GEMM"},
    "linear": {"linear": "Linear with bias"},
    "rotary": {"rotary": "Interleaved RoPE"},
    "convolution": {"conv2d": "Valid Conv2D", "depthwise_conv": "Depthwise Conv2D"},
    "normalization": {"rms": "RMSNorm", "layer": "LayerNorm (no affine)", "softmax": "Softmax"},
    "feedforward": {"ffn": "Two-launch FFN"},
    "swiglu": {"swiglu": "Four-launch SwiGLU"},
    "attention": {"dense": "Dense SDPA (attention workload)", "gqa": "Three-launch GQA"},
}


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    report = {
        "schema": 1,
        "scope": "Independent scalar CUDA/HIP contracts at all 17 paper workload shapes. Algorithms, launch layouts, references and proof harness differ from the original registry. Dense SDPA is not the FlashAttention online algorithm. Abstract-operation proofs and finite numerical checks remain separate.",
        "original_paper_fully_reproduced": False,
        "kernel_study_model_calls": 0,
        "full_shape_certificates": 0,
        "families": [],
        "hosts": {},
        "evidence_sha256": {},
        "original_dependencies": [
            "Authors' pinned registry, adapted source revisions, reference contracts and proof/agent harness; bounded public artifact searches have not located them",
            "Original 42 mutants, failure channels, fallback/second-opinion and stage token traces",
            "Original nine accepted production kernels and full adapted llm.c kernel",
            "Original PTX/optimized tiled and online-attention kernels, NVIDIA operations and H100 timings",
            "Original closed-model endpoints/outcomes under the offline/free constraint; local open-model experiments are adaptations",
            "Authors' historical development/person-day records",
        ],
    }
    family_rows = {}
    for study, names in STUDIES.items():
        root = ROOT / study / "results"
        manifest = json.loads((root / "manifest.json").read_text())
        for name, digest in manifest.items():
            assert sha(root / name) == digest, study + "/" + name
        cpu = json.loads((root / "cpu.json").read_text())
        validation = json.loads((root / "validation.json").read_text())
        assert (
            cpu["status"] == "passed"
            and cpu["model_calls"] == 0
            and validation["status"] == "passed"
        )
        baselines = cpu["baselines"]
        assert len(baselines) == len(names) * 2
        assert all(b["status"] == "verified" and b["rechecked"] for b in baselines)
        report["full_shape_certificates"] += len(baselines)
        anchors = {b["theorem_sha256"] for b in baselines}
        for host in ("mi350", "mi350-2"):
            data = json.loads((root / (host + ".json")).read_text())
            assert data["status"] == "passed" and data["model_calls"] == 0
            assert {c["key"] for c in data["cases"]} == set(names)
            h = report["hosts"].setdefault(
                host,
                {
                    "device": data["device"],
                    "trials": 0,
                    "final_comparisons": 0,
                    "intermediate_comparisons": 0,
                    "scalar_comparisons": 0,
                },
            )
            for c in data["cases"]:
                assert c["certificate"]["theorem_sha256"] in anchors
                trials = c["trials"]
                assert len(trials) == 10 and all(
                    t["inputs_unchanged"] and t["guard_zones_unchanged"] for t in trials
                )
                scalar = sum(
                    t.get("scalar_comparisons", t.get("output_comparisons", 0)) for t in trials
                )
                final = sum(
                    t.get("final_comparisons", t.get("output_comparisons", 0)) for t in trials
                )
                assert scalar >= final > 0
                h["trials"] += len(trials)
                h["scalar_comparisons"] += scalar
                h["final_comparisons"] += final
                h["intermediate_comparisons"] += scalar - final
                key = study + "/" + c["key"]
                row = family_rows.setdefault(
                    key,
                    {
                        "family": names[c["key"]],
                        "study": study,
                        "evidence": study + "/RESULTS.md",
                        "cuda_and_hip_certificates": 2,
                        "hosts": {},
                    },
                )
                row["hosts"][host] = {
                    "trials": 10,
                    "final_comparisons": final,
                    "intermediate_comparisons": scalar - final,
                    "theorem_sha256": c["certificate"]["theorem_sha256"],
                }
            report["evidence_sha256"][str((root / (host + ".json")).relative_to(ROOT))] = sha(
                root / (host + ".json")
            )
        for name in ("cpu.json", "validation.json", "manifest.json"):
            report["evidence_sha256"][str((root / name).relative_to(ROOT))] = sha(root / name)
    report["families"] = list(family_rows.values())
    assert len(report["families"]) == 17 and report["full_shape_certificates"] == 34
    for h in report["hosts"].values():
        assert h["trials"] == 170
    report["status"] = "audited-independent-full-shape-coverage"
    (ROOT / "full-shape-status.json").write_text(json.dumps(report, indent=2) + "\n")
    rows = []
    for row in report["families"]:
        a, b = row["hosts"]["mi350"], row["hosts"]["mi350-2"]
        assert (a["final_comparisons"], a["intermediate_comparisons"]) == (
            b["final_comparisons"],
            b["intermediate_comparisons"],
        )
        rows.append(
            f"| [{row['family']}]({row['evidence']}) | 2 | 10 / 10 | {a['final_comparisons']:,} | {a['intermediate_comparisons']:,} |"
        )
    h = report["hosts"]["mi350"]
    (ROOT / "FULL_SHAPE.md").write_text(
        """# Full-shape independent coverage

**The original paper is not fully reproduced.** This table counts independent
scalar CUDA/HIP contracts at the paper's workload shapes. It does not count
the authors' original kernels, model pass rates or optimized timings.
[Complete paper ledger](COVERAGE.md), [audited machine-readable totals](full-shape-status.json).

All **34 full-shape certificates** (17 HIP + 17 CUDA) verified and independently
rechecked in Lean 4.19.0. Each family also passed ten exact-source HIP trials on
each MI350X host. Inputs and allocation guards stayed unchanged in every trial.
Theorems concern abstract scalar operations; numerical comparisons are separate.

| Independent family / method | HIP + CUDA certificates | Trials: mi350 / mi350-2 | Final comparisons per host | Intermediate comparisons per host |
| --- | ---: | ---: | ---: | ---: |
"""
        + "\n".join(rows)
        + f"""
| **Total** | **34** | **170 / 170** | **{h["final_comparisons"]:,}** | **{h["intermediate_comparisons"]:,}** |

Each host checked **{h["scalar_comparisons"]:,} scalar values** across these full-shape
sources. Counts include every FP32 projection/score/probability and FP16 hidden
buffer in the multi-launch adaptations. CUDA certificates have no NVIDIA
execution evidence. The largest symbolic scaling cases are separate from these
allocated/executed workloads.

Dense SDPA covers the attention workload shape; it does not implement the
FlashAttention online algorithm. GELU, normalization conventions, precision
boundaries, scalar kernels and launch layouts are explicit independent contracts,
rather than recovered original reference files. A same-source
[dot-product proof ablation](dot_ablation/RESULTS.md) and separate
[shuffle/MFMA hardware conformance](collective_conformance/RESULTS.md) add evidence
for other result categories without converting it into original-paper results.

`python3 reproduction/full_shape_status.py` validates each study's artifact
manifest, completed CPU/device records, certificate anchors and counts before
regenerating this table/JSON. Per-study summarizers additionally reconstruct the
archived source-bound theorem statements and device wrappers. No model calls
are needed. [Local model experiments](local_models/README.md) have separate,
recorded budgets and must not be pooled with these deterministic proof studies.
"""
    )
    print(
        json.dumps(
            {
                "families": 17,
                "full_shape_certificates": 34,
                "hosts": report["hosts"],
                "original_paper_fully_reproduced": False,
            }
        )
    )


if __name__ == "__main__":
    main()
