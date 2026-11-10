"""Source-bound two-launch FP16 ReLU feed-forward certificates."""

import ast
from dataclasses import replace
import json

from . import matrix
from .certificate import LAKEFILE, TOOLCHAIN, digest, lean_binary, model_path, run_lean, write_json
from .frontend import translate
from .ir import Refusal, Task, lean_list, lean_node, node
from .spec import read_spec

PROFILE = "feedforward-pipeline-v10"
FILES = {
    "Main.lean",
    "up.cu",
    "down.cu",
    "up-task.json",
    "down-task.json",
    "reference.py",
    "translation.json",
    "lean-toolchain",
    "lakefile.toml",
}


def reference_expression(x="x", w1="w1", down="down"):
    return f"(({x}.float() @ {w1}.float()).relu().half().float() @ {down}.float()).half()"


def expected_program(task, activation):
    result = matrix.expected_program(task)
    if activation:
        result[7] = node(
            "store",
            "global",
            2,
            node("ivar", 0),
            node("un", "toHalf", node("bin", "max", node("reg", 0), node("lit", 0, 1))),
        )
    return result


def prepare(up_source, down_source, reference, up_task, down_task):
    up, down = matrix.parse_task(up_task), matrix.parse_task(down_task)
    if (
        any(len(b.shape) != 2 for t in (up, down) for b in t.buffers)
        or up.language != down.language
        or up.warp != down.warp
        or up.entry == down.entry
        or up.buffers[2] != replace(down.buffers[0], role="output")
        or len({b.name for b in (*up.buffers, *down.buffers[1:])}) != 5
    ):
        raise Refusal(
            "ffn", "expected two distinct rank-two FP16 stages wired through one named intermediate"
        )
    trs = [translate(source, task) for source, task in ((up_source, up), (down_source, down))]
    for task, tr, activated in zip((up, down), trs, (True, False)):
        if tr.shared or tr.program != expected_program(task, activated):
            raise Refusal("ffn", "source differs from the proved ReLU/FP16/matmul stage")
    tree = ast.parse(reference)
    fn = next((s for s in tree.body if isinstance(s, ast.FunctionDef)), None)
    names = (up.buffers[0].name, up.buffers[1].name, down.buffers[1].name)
    if (
        fn is None
        or len(fn.body) != 1
        or not isinstance(fn.body[0], ast.Return)
        or ast.dump(fn.body[0].value)
        != ast.dump(ast.parse(reference_expression(*names), mode="eval").body)
    ):
        raise Refusal(
            "ffn-reference", "expected the closed two-matmul/ReLU/FP16-intermediate reference"
        )
    # The entire pipeline AST matched before this minimal module/binding check.
    small = Task.parse(
        json.dumps(
            {
                "name": "ffn_module_check",
                "entry": "ffn_module_check",
                "language": up.language,
                "launch": {"grid": 1, "block": 1, "warp": up.warp},
                "buffers": [
                    {"name": name, "role": role, "shape": [1, 1], "dtype": "float16"}
                    for name, role in [
                        *((n, "input") for n in names),
                        (down.buffers[2].name, "output"),
                    ]
                ],
            }
        )
    )
    read_spec(reference, small)
    return (up, down), trs


def dimensions(tasks):
    up, down = tasks
    m, k = up.buffers[0].shape
    h = up.buffers[1].shape[1]
    return m, k, h, down.buffers[1].shape[1]


def model_hashes():
    return {
        **matrix.model_hashes(),
        **{
            name.lower(): digest(matrix.library_path(name).read_bytes())
            for name in ("DotMap", "Pipeline", "FeedForward")
        },
    }


def render(tasks, trs):
    parts = [model_path(True).read_text()]
    for name, imported in [
        ("Pointwise", "Nonlinear"),
        ("Reduction", "Pointwise"),
        ("DotLoop", "Reduction"),
        ("Matrix", "DotLoop"),
        ("DotMap", "Matrix"),
        ("Pipeline", "DotMap"),
        ("FeedForward", "Pipeline"),
    ]:
        source = matrix.library_path(name).read_text()
        prefix = "import Lark." + imported + "\n"
        if not source.startswith(prefix):
            raise Refusal("installation", "unexpected " + name + " proof library import")
        parts.append(source.removeprefix(prefix))
    m, k, h, n = dimensions(tasks)
    warp = tasks[0].warp
    programs = [lean_list(lean_node(i) for i in tr.program) for tr in trs]
    return (
        "\n".join(parts)
        + f"""
namespace LarkCertificate
open LarkNonlinear
def shape : LarkFeedForward.Shape :=
  ⟨{m},{k},{h},{n},by decide,by decide,by decide,by decide,
    by decide,by decide,by decide,by decide,by decide⟩
def chain : LarkPipeline.Chain := LarkFeedForward.chain shape
def upProgram : List Instr := {programs[0]}
def downProgram : List Instr := {programs[1]}
def spec (ops : Ops α) (input : Nat → Nat → α) : List α := LarkPipeline.spec chain ops input
def firstFinal (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) : State α :=
  LarkPipeline.firstFinal chain ops input outside
def secondFinal (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) : State α :=
  LarkPipeline.secondFinal chain ops input outside
theorem segmentation_data : upProgram=LarkDotMap.program chain.first ∧ downProgram=LarkDotMap.program chain.second := by
  exact ⟨rfl,rfl⟩
theorem segmentation (ops : Ops α) : ∀ input outside1 outside2,∃ f1 f2,
    LarkPipeline.RunsWith chain ops {warp} upProgram downProgram input
      (initial (LarkDotMap.layout chain.first) input outside1) outside2 f1 f2 := by
  rw [segmentation_data.1,segmentation_data.2]
  exact LarkFeedForward.correct shape ops {warp} (by decide)
theorem race_free (ops : Ops α) (input : Nat → Nat → α) (outside1 outside2 : Location → Option α) :
    raceFree (LarkDotMap.geometry chain.first {warp}) (firstFinal ops input outside1).trace=true ∧
    raceFree (LarkDotMap.geometry chain.second {warp}) (secondFinal ops input outside2).trace=true := by
  exact ⟨LarkReduction.owned_raceFree _ _ (LarkDotMap.partialState_owned ops input outside1 chain.first chain.first.n),
    LarkReduction.owned_raceFree _ _ (LarkDotMap.partialState_owned ops (LarkPipeline.idealInput chain ops input) outside2 chain.second chain.second.n)⟩
theorem segment_equivalence (ops : Ops α) (input : Nat → Nat → α) (outside2 : Location → Option α) :
    extract (LarkDotMap.layout chain.second) (secondFinal ops input outside2)=some (spec ops input) := by
  have h:=LarkDotMap.extract_eq ops (LarkPipeline.idealInput chain ops input) outside2 chain.second
  rw [LarkDotMap.spec_eq_matrixSpec] at h
  exact h
theorem kernel_eq_spec (ops : Ops α) : ∀ input outside1 outside2,∃ f1 f2,
    LarkPipeline.RunsWith chain ops {warp} upProgram downProgram input
      (initial (LarkDotMap.layout chain.first) input outside1) outside2 f1 f2 := segmentation ops
theorem kernel_eq_spec_pre (ops : Ops α) (input : Nat → Nat → α) (start : State α)
    (outside2 : Location → Option α) (pre : StdPre (LarkDotMap.layout chain.first) input start) :
    ∃ f1 f2,LarkPipeline.RunsWith chain ops {warp} upProgram downProgram input start outside2 f1 f2 := by
  obtain ⟨outside1,rfl⟩:=pre
  exact kernel_eq_spec ops input outside1 outside2
#print axioms segmentation_data
#print axioms segmentation
#print axioms race_free
#print axioms segment_equivalence
#print axioms kernel_eq_spec
#print axioms kernel_eq_spec_pre
end LarkCertificate
"""
    )


def verify(case, output, *, lean=None, timeout=120):
    if output.exists() or timeout <= 0:
        raise Refusal("configuration", "fresh output directory and positive timeout required")
    sources = {}
    for stage in ("up", "down"):
        candidates = [case / (stage + ext) for ext in (".hip", ".cu")]
        found = [p for p in candidates if p.is_file()]
        if len(found) != 1:
            raise Refusal("ffn", "exactly one source file is required per stage")
        sources[stage + ".cu"] = found[0].read_bytes()
    for name in ("reference.py", "up-task.json", "down-task.json"):
        sources[name] = (case / name).read_bytes()
    tasks, trs = prepare(
        *(
            sources[f].decode()
            for f in ("up.cu", "down.cu", "reference.py", "up-task.json", "down-task.json")
        )
    )
    binary = lean_binary(lean)
    output.mkdir(parents=True)
    for name, data in sources.items():
        (output / name).write_bytes(data)
    (output / "Main.lean").write_text(render(tasks, trs))
    (output / "lean-toolchain").write_text(TOOLCHAIN)
    (output / "lakefile.toml").write_text(LAKEFILE)
    write_json(output / "translation.json", [tr.data() for tr in trs])
    ok, log = run_lean(output, binary, timeout)
    (output / "lean-1.log").write_text(log)
    report = {
        "schema": 1,
        "status": "verified" if ok else "unproved",
        "model_profile": PROFILE,
        "model_hashes": model_hashes(),
        "source_readback": True,
        "model_calls": 0,
        "files": {name: digest((output / name).read_bytes()) for name in sorted(FILES)},
        "axiom_audit": log,
        "ffn_dimensions": list(dimensions(tasks)),
        "kernel_launches": 2,
        "trusted_assumptions": [
            "Lean 4.19.0 kernel and printed standard axioms; pinned nonlinear machine",
            "Strict CUDA/HIP lowering and the closed two-matmul/ReLU/FP16-intermediate reference formalization",
            "Host layout/disjoint allocations and ordered launches connecting the same intermediate buffer",
            "Abstract scalar/half operations; hardware correspondence and numerical error outside theorem",
            "External race-free-phase/GPU-interleaving correspondence",
        ],
        "scope": "Both actual runLaunch programs: completion, race freedom and every final output for all inputs/outside memories; every valid second-stage intermediate read comes from first-stage final memory. Independent scalar two-launch FFN, not original optimized kernels.",
    }
    write_json(output / "report.json", report)
    return report


def check(directory, *, lean=None, timeout=120):
    report = json.loads((directory / "report.json").read_text())
    if report.get("model_profile") != PROFILE or set(report["files"]) != FILES:
        raise Refusal("integrity", "unexpected FFN profile or file set")
    for name, expected in report["files"].items():
        if digest((directory / name).read_bytes()) != expected:
            raise Refusal("integrity", "file changed: " + name)
    if report["model_hashes"] != model_hashes():
        raise Refusal("integrity", "different pinned machine or proof libraries")
    if (directory / "lean-toolchain").read_text() != TOOLCHAIN or (
        directory / "lakefile.toml"
    ).read_text() != LAKEFILE:
        raise Refusal("integrity", "unexpected standalone project configuration")
    tasks, trs = prepare(
        *(
            (directory / f).read_text()
            for f in ("up.cu", "down.cu", "reference.py", "up-task.json", "down-task.json")
        )
    )
    dims = report.get("ffn_dimensions")
    if (
        not isinstance(dims, list)
        or any(type(x) is not int for x in dims)
        or dims != list(dimensions(tasks))
        or type(report.get("kernel_launches")) is not int
        or report["kernel_launches"] != 2
    ):
        raise Refusal(
            "integrity", "reported FFN shape/launch count differs from the fixed pipeline"
        )
    if json.loads((directory / "translation.json").read_text()) != json.loads(
        json.dumps([tr.data() for tr in trs])
    ):
        raise Refusal("integrity", "translation differs from the two sources")
    if (directory / "Main.lean").read_text() != render(tasks, trs):
        raise Refusal("integrity", "theorem differs from the fixed source/reference/pipeline")
    ok, log = run_lean(directory, lean_binary(lean), timeout)
    if not ok:
        raise Refusal("proof", log)
    return log
