"""Render completed audited cohorts; never infer missing results or make model calls."""

import argparse
import hashlib
import json
from pathlib import Path
import platform
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from reproduction.local_models.compare_models import COHORTS, ROOT, audit_cohort

ORDER = ("glm", "glm_flash", "deepseek")
LABELS = {"glm": "GLM-5.3", "glm_flash": "GLM-5.3-Flash", "deepseek": "DeepSeek-V4.1-Flash-1017"}
LEVEL2 = {"ffn", "flash_attn", "gqa", "rope", "swiglu"}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_audit(path, *, lean):
    """Recompute the completed audit from raw evidence and fresh Lean rechecks."""
    data = json.loads((path / "comparison.json").read_text())
    manifest = json.loads((path / "manifest.json").read_text())
    actual = {
        str(p.relative_to(path)): sha(p)
        for p in path.rglob("*")
        if p.is_file() and p != path / "manifest.json"
    }
    require(manifest == actual, "Audit output manifest differs")
    require(data["three_model_comparison_complete"] is True, "Three-model comparison is incomplete")
    require(data["original_paper_fully_reproduced"] is False, "Unexpected original-paper claim")
    require(
        data["same_first_attempt_messages_across_selected_models"] is True,
        "Requests are not matched",
    )
    require(set(data["models"]) == set(ORDER), "Model set differs")
    require(data["external_api_spend_usd"] == 0, "Unexpected external API spending")
    require(data["auditor_sha256"] == sha(ROOT / "compare_models.py"), "Auditor source differs")
    messages, rechecks = {}, {}
    for name in ORDER:
        model = data["models"][name]
        runs = [ROOT / "results" / r for r in COHORTS[name]["runs"]]
        recomputed, logs = audit_cohort(name, runs, lean=lean)
        require(recomputed == model, "Audit summary differs from reconstructed raw evidence")
        rechecks[name] = logs
        for case in recomputed["cases"]:
            existing = messages.setdefault(case["case"], case["first_messages_sha256"])
            require(existing == case["first_messages_sha256"], "First requests differ")
            if case["verified_within_recorded_budget"]:
                require(
                    (path / "rechecks" / name / (Path(case["case"]).name + ".log")).is_file(),
                    "Independent recheck log is missing",
                )
    return data, rechecks


def tokens(usage):
    count = f"{usage['reported_usage']['total_tokens']:,}"
    return count + (" reported; incomplete" if usage["usage_incomplete"] else "")


def report(data):
    lines = [
        "# Independent local three-model comparison",
        "",
        "**The original paper is not fully reproduced.** These are the same 17 reduced HIP",
        "fixtures under a bounded immutable-proof-slot harness. Models received identical",
        "decoded first-request messages, seed 261102028, temperature zero, a 16,384-token",
        "output cap and a 4,096 reasoning-token limit. Every successful exported model",
        "proposal passed another source-bound Lean recheck.",
        "",
        "![Common first-attempt certificates and reported tokens](comparison.svg)",
        "",
        "| Local checkpoint | First-attempt certificates / fixtures | Responses / requests | Reported first-attempt tokens |",
        "| --- | ---: | ---: | ---: |",
    ]
    for name in ORDER:
        model = data["models"][name]
        lines.append(
            f"| {LABELS[name]} | {model['first_attempt_certificates']} / 17 | {model['first_attempt_responses']} / 17 | {tokens(model['first_attempt_usage'])} |"
        )
    lines += [
        "",
        "Only the first request per fixture is compared above. Later retries are",
        "separate: full GLM and DeepSeek allow up to three requests per fixture, while",
        "Flash allows one. These different budgets must not be pooled into a matched rate.",
        "",
        "| Local checkpoint | Maximum requests per fixture | Certificates within recorded budget | Actual requests | Actual Lean checks | All-attempt reported tokens |",
        "| --- | ---: | ---: | ---: | ---: | ---: |",
    ]
    for name in ORDER:
        model = data["models"][name]
        lines.append(
            f"| {LABELS[name]} | {model['attempts_per_case']} | {model['certificates_within_recorded_budget']} / 17 | {model['requests']} | {model['lean_checks']} | {tokens(model['all_attempt_usage'])} |"
        )
    lines += [
        "",
        "| Local checkpoint | First-attempt outcomes |",
        "| --- | --- |",
    ]
    for name in ORDER:
        values = data["models"][name]["first_attempt_outcomes"]
        outcomes = "; ".join(f"{key}: {value}" for key, value in sorted(values.items()))
        lines.append(f"| {LABELS[name]} | {outcomes} |")
    lines += [
        "",
        "| Local checkpoint | First certificates in 12 Level-1 families | First certificates in 5 Level-2 families | Certificates within budget (request count) |",
        "| --- | ---: | ---: | --- |",
    ]
    for name in ORDER:
        cases = data["models"][name]["cases"]
        level2 = sum(c["first_verified"] for c in cases if Path(c["case"]).name in LEVEL2)
        level1 = sum(c["first_verified"] for c in cases if Path(c["case"]).name not in LEVEL2)
        proven = (
            ", ".join(
                f"{Path(c['case']).name} ({c['requests']})"
                for c in cases
                if c["verified_within_recorded_budget"]
            )
            or "none"
        )
        lines.append(f"| {LABELS[name]} | {level1} / 12 | {level2} / 5 | {proven} |")
    lines += [
        "",
        "Family names match the paper's workload categories; their kernels, shapes",
        "and verification protocol remain independent reduced adaptations.",
        "",
        "| Reduced fixture | GLM-5.3 first outcome | Flash first outcome | DeepSeek first outcome |",
        "| --- | --- | --- | --- |",
    ]
    indexed = {n: {c["case"]: c for c in data["models"][n]["cases"]} for n in ORDER}
    for case in sorted(indexed[ORDER[0]]):
        outcomes = " | ".join(indexed[n][case]["first_outcome"] for n in ORDER)
        lines.append(f"| {Path(case).name} | {outcomes} |")
    lines += [
        "",
        "Transport failures, empty final responses and invalid proposals are distinct",
        "from unproved Lean checks. The recorded validator also forbids comments and",
        "`native_decide`; a proposal refusal is not proof of a kernel bug. No posthoc",
        "tactic repair is counted. Unknown usage remains incomplete rather than zero.",
        "",
        "Tokens are server-reported prompt/completion counts, not billed costs. Tokenizers,",
        "chat templates, native precision and tensor parallelism differ. GLM uses low",
        "reasoning effort; DeepSeek has no equivalent effort field. This is one seeded",
        "first request per fixture, with no repeated-run uncertainty estimate or isolated",
        "model-size conclusion. Hosted API spending is $0; GPU/electricity cost is not estimated.",
        "",
        "The original kernels, registry, prompts, agent tools, budgets and hosted-model",
        "outcomes remain unavailable. These results do not reproduce their pass rates,",
        "stage token costs or model-size conclusions. The input audit JSON binds every",
        "raw source file and independent Lean recheck; the render manifest binds this report.",
        "",
    ]
    return "\n".join(lines)


def figure(data, path):
    import matplotlib

    matplotlib.use("Agg")
    from matplotlib import pyplot as plt
    from matplotlib.patches import Patch
    from matplotlib.ticker import FuncFormatter

    labels = ["GLM-5.3", "GLM-5.3\nFlash", "DeepSeek-V4.1\nFlash-1017"]
    fig, axes = plt.subplots(1, 2, figsize=(10.8, 4.4), constrained_layout=True)
    x = list(range(3))
    counts = [data["models"][n]["first_attempt_certificates"] for n in ORDER]
    axes[0].bar(x, counts, color="#287d8e", width=0.6)
    for i, value in enumerate(counts):
        axes[0].text(i, value + 0.35, f"{value}/17", ha="center")
    axes[0].set_ylim(0, 18.5)
    axes[0].set_yticks([0, 4, 8, 12, 16])
    axes[0].set_ylabel("Verified certificates (17 first requests)")
    axes[0].set_title("Common first-attempt outcomes")
    for i, name in enumerate(ORDER):
        usage = data["models"][name]["first_attempt_usage"]
        if usage["usage_incomplete"]:
            axes[1].text(i, 0, "usage\nincomplete", ha="center", va="bottom")
            continue
        values = usage["reported_usage"]
        prompt, completion = values["prompt_tokens"], values["completion_tokens"]
        axes[1].bar(i, prompt, color="#426ca0", width=0.6, label="Prompt" if i == 0 else None)
        axes[1].bar(
            i,
            completion,
            bottom=prompt,
            color="#d59b3e",
            hatch="//",
            width=0.6,
            label="Completion" if i == 0 else None,
        )
    axes[1].yaxis.set_major_formatter(FuncFormatter(lambda n, _: f"{n / 1000:,.0f}k"))
    axes[1].set_ylabel("Reported tokens (17 first requests)")
    axes[1].set_title("Tokenizers and templates differ")
    axes[1].legend(
        handles=[
            Patch(facecolor="#426ca0", label="Prompt"),
            Patch(facecolor="#d59b3e", hatch="//", label="Completion"),
        ],
        frameon=False,
    )
    for axis in axes:
        axis.set_xticks(x, labels)
        axis.spines[["top", "right"]].set_visible(False)
        axis.grid(axis="y", alpha=0.18)
        axis.set_axisbelow(True)
    fig.suptitle(
        "Independent reduced HIP proof experiment; not original paper results", fontsize=11
    )
    fig.savefig(path, metadata={"Creator": "LARK independent reproduction", "Date": None})
    plt.close(fig)
    return matplotlib.__version__


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--audit", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--lean", required=True)
    args = parser.parse_args()
    require(not args.output.exists(), "Fresh output directory required")
    data, rechecks = read_audit(args.audit, lean=args.lean)
    # Import plotting only after all completeness and binding checks pass.
    args.output.mkdir(parents=True)
    version = figure(data, args.output / "comparison.svg")
    (args.output / "RESULTS.md").write_text(report(data))
    for model, logs in rechecks.items():
        for name, log in logs.items():
            target = args.output / "rechecks" / model / (name + ".log")
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text(log)
    manifest = {
        "schema": 1,
        "original_paper_fully_reproduced": False,
        "input_comparison_sha256": sha(args.audit / "comparison.json"),
        "input_manifest_sha256": sha(args.audit / "manifest.json"),
        "renderer_sha256": sha(Path(__file__)),
        "python": platform.python_version(),
        "matplotlib": version,
        "fresh_independent_certificate_rechecks": sum(len(logs) for logs in rechecks.values()),
        "files": {
            str(p.relative_to(args.output)): sha(p)
            for p in sorted(args.output.rglob("*"))
            if p.is_file()
        },
    }
    (args.output / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print("Rendered audited completed cohorts:", args.output)


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError, TypeError, AssertionError) as error:
        raise SystemExit("REPORT REFUSED: " + str(error))
