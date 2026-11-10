"""Four-launch SwiGLU with FP32 projections and one FP16 intermediate rounding."""

import ast
from dataclasses import replace
import json

from . import feedforward, matrix
from .certificate import LAKEFILE, TOOLCHAIN, digest, lean_binary, model_path, run_lean, write_json
from .frontend import translate
from .ir import Buffer, Refusal, Task, lean_list, lean_node, node
from .spec import read_spec

PROFILE = "swiglu-pipeline-v11"
STAGES = ("gate", "up", "combine", "down")
SOURCE_FILES = tuple(x for stage in STAGES for x in (stage + ".cu", stage + "-task.json")) + (
    "reference.py",
)
FILES = set(SOURCE_FILES) | {"Main.lean", "translation.json", "lean-toolchain", "lakefile.toml"}


def reference_expression(x="x", gate="wgate", up="wup", down="down"):
    return f"((torch.nn.functional.silu({x}.float() @ {gate}.float()) * ({x}.float() @ {up}.float())).half().float() @ {down}.float()).half()"


def projection_task(source):
    d = json.loads(source)
    if [b["dtype"] for b in d["buffers"]] != ["float16", "float16", "float32"]:
        raise Refusal("swiglu", "projections require FP16 inputs and FP32 outputs")
    original = json.loads(source)
    for b in d["buffers"]:
        b["dtype"] = "float16"
    task = matrix.parse_task(json.dumps(d))
    if any(len(b.shape) != 2 for b in task.buffers):
        raise Refusal("swiglu", "expected rank-two projections")
    return replace(
        task,
        buffers=tuple(
            Buffer(b["name"], b["role"], tuple(b["shape"]), b["dtype"]) for b in original["buffers"]
        ),
    )


def combine_task(source):
    d = json.loads(source)
    bufs = d["buffers"]
    if (
        len(bufs) != 3
        or [b["role"] for b in bufs] != ["input", "input", "output"]
        or [b["dtype"] for b in bufs] != ["float32", "float32", "float16"]
        or any(
            not isinstance(b["shape"], list)
            or len(b["shape"]) != 2
            or any(type(n) is not int or n <= 0 for n in b["shape"])
            for b in bufs
        )
        or any(b["shape"] != bufs[0]["shape"] for b in bufs)
    ):
        raise Refusal("swiglu", "combine requires two equal FP32 matrices and one FP16 output")
    m, h = bufs[0]["shape"]
    n = m * h
    warp = 32 if d.get("language", "cuda") == "cuda" else 64
    if (
        n >= 2147483648
        or d["launch"] != {"grid": n, "block": 1, "warp": warp}
        or any(type(x) is not int for x in d["launch"].values())
        or d.get("fuel") != [5, 1, 1, 1]
        or any(type(x) is not int for x in d["fuel"])
    ):
        raise Refusal(
            "swiglu", "combine requires grid=M*H, block=1, native warp, exact fuel and size<2^31"
        )
    small = json.loads(source)
    small["launch"]["grid"] = 1
    for b in small["buffers"]:
        b["shape"] = [1, 1]
    checked = Task.parse(json.dumps(small))
    return replace(
        checked,
        grid=n,
        buffers=tuple(Buffer(b["name"], b["role"], tuple(b["shape"]), b["dtype"]) for b in bufs),
    )


def combine_program():
    a, b = node("reg", 0), node("reg", 1)
    reciprocal = node(
        "bin",
        "div",
        node("lit", 1, 1),
        node(
            "bin",
            "add",
            node("lit", 1, 1),
            node("un", "exp", node("bin", "sub", node("lit", 0, 1), a)),
        ),
    )
    silu = node("bin", "mul", a, reciprocal)
    ix = node("ivar", 0)
    return [
        node("idx", 0, node("bid")),
        node("set", 0, node("load", "global", 0, ix)),
        node("set", 1, node("load", "global", 1, ix)),
        node("store", "global", 2, ix, node("un", "toHalf", node("bin", "mul", silu, b))),
        node("halt"),
    ]


def dimensions(tasks):
    m, k = tasks[0].buffers[0].shape
    h = tasks[0].buffers[1].shape[1]
    n = tasks[3].buffers[1].shape[1]
    return m, k, h, n


def prepare(sources):
    tasks = [projection_task(sources[s + "-task.json"]) for s in STAGES[:2]]
    tasks += [
        combine_task(sources["combine-task.json"]),
        matrix.parse_task(sources["down-task.json"]),
    ]
    g, u, c, d = tasks
    if (
        len({t.language for t in tasks}) != 1
        or len({t.warp for t in tasks}) != 1
        or len({t.entry for t in tasks}) != 4
        or any(len(b.shape) != 2 for t in tasks for b in t.buffers)
        or g.buffers[0] != u.buffers[0]
        or g.buffers[1].shape != u.buffers[1].shape
        or g.buffers[2] != replace(c.buffers[0], role="output")
        or u.buffers[2] != replace(c.buffers[1], role="output")
        or c.buffers[2] != replace(d.buffers[0], role="output")
    ):
        raise Refusal("swiglu", "stage signatures, types, entries or intermediate wiring differ")
    names = (g.buffers[0].name, g.buffers[1].name, u.buffers[1].name, d.buffers[1].name)
    allocations = (
        *names,
        g.buffers[2].name,
        u.buffers[2].name,
        c.buffers[2].name,
        d.buffers[2].name,
    )
    if len(set(allocations)) != 8:
        raise Refusal("swiglu", "eight distinct named allocations are required")
    trs = [translate(sources[s + ".cu"], t) for s, t in zip(STAGES, tasks)]
    for i, (t, tr) in enumerate(zip(tasks, trs)):
        expected = combine_program() if i == 2 else matrix.expected_program(t)
        if i < 2:
            expected[7] = node("store", "global", 2, node("ivar", 0), node("reg", 0))
        if tr.shared or tr.program != expected:
            raise Refusal(
                "swiglu", "source differs from the checked FP32-projection/SiLU/FP16/down pipeline"
            )
    reference = sources["reference.py"]
    tree = ast.parse(reference)
    fn = next((n for n in tree.body if isinstance(n, ast.FunctionDef)), None)
    if (
        fn is None
        or len(fn.body) != 1
        or not isinstance(fn.body[0], ast.Return)
        or ast.dump(fn.body[0].value)
        != ast.dump(ast.parse(reference_expression(*names), mode="eval").body)
    ):
        raise Refusal(
            "swiglu-reference", "expected the closed SiLU/gate/up/FP16-intermediate/down AST"
        )
    small = Task.parse(
        json.dumps(
            {
                "name": "swiglu_module_check",
                "entry": "swiglu_module_check",
                "language": g.language,
                "launch": {"grid": 1, "block": 1, "warp": g.warp},
                "buffers": [
                    {"name": n, "role": r, "shape": [1, 1], "dtype": "float16"}
                    for n, r in [*((n, "input") for n in names), (d.buffers[2].name, "output")]
                ],
            }
        )
    )
    read_spec(reference, small)
    return tasks, trs


def model_hashes():
    return {
        **feedforward.model_hashes(),
        **{
            n.lower(): digest(matrix.library_path(n).read_bytes())
            for n in ("PairMap", "SwiPointwise", "SwiGLU")
        },
    }


def render(tasks, trs):
    parts = [model_path(True).read_text()]
    for name, imports in [
        ("Pointwise", ["Nonlinear"]),
        ("Reduction", ["Pointwise"]),
        ("DotLoop", ["Reduction"]),
        ("Matrix", ["DotLoop"]),
        ("DotMap", ["Matrix"]),
        ("Pipeline", ["DotMap"]),
        ("FeedForward", ["Pipeline"]),
        ("PairMap", ["DotMap"]),
        ("SwiPointwise", ["PairMap"]),
        ("SwiGLU", ["SwiPointwise", "FeedForward"]),
    ]:
        text = matrix.library_path(name).read_text()
        prefix = "".join("import Lark." + i + "\n" for i in imports)
        if not text.startswith(prefix):
            raise Refusal("installation", "unexpected " + name + " library imports")
        parts.append(text.removeprefix(prefix))
    m, k, h, n = dimensions(tasks)
    warp = tasks[0].warp
    programs = [lean_list(lean_node(i) for i in tr.program) for tr in trs]
    return (
        "\n".join(parts)
        + f"""
namespace LarkCertificate
open LarkNonlinear
def shape : LarkFeedForward.Shape := ⟨{m},{k},{h},{n},by decide,by decide,by decide,by decide,
  by decide,by decide,by decide,by decide,by decide⟩
def programs : LarkSwiGLU.Programs := ⟨{programs[0]},{programs[1]},{programs[2]},{programs[3]}⟩
def spec (ops : Ops α) (input : Nat → Nat → α) : List α := LarkSwiGLU.spec shape ops input
theorem segmentation_data : programs=LarkSwiGLU.programs shape := by rfl
theorem segmentation (ops : Ops α) : LarkSwiGLU.Correct shape ops {warp} programs := by
  rw [segmentation_data]
  exact LarkSwiGLU.correct shape ops {warp} (by decide)
theorem race_free (ops : Ops α) (input : Nat → Nat → α) (og ou oh oo : Location → Option α) :
    raceFree (LarkDotMap.geometry (LarkSwiGLU.projection shape) {warp}) (LarkSwiGLU.gateFinal shape ops input og).trace=true ∧
    raceFree (LarkDotMap.geometry (LarkSwiGLU.projection shape) {warp}) (LarkSwiGLU.upFinal shape ops input ou).trace=true ∧
    raceFree (LarkPairMap.geometry {m * h} {warp}) (LarkSwiGLU.hiddenFinal shape ops input oh).trace=true ∧
    raceFree (LarkDotMap.geometry (LarkFeedForward.stage2 shape) {warp}) (LarkSwiGLU.finalState shape ops input oo).trace=true := by
  exact ⟨LarkReduction.owned_raceFree _ _ (LarkDotMap.partialState_owned ops input og (LarkSwiGLU.projection shape) {m * h}),
    LarkReduction.owned_raceFree _ _ (LarkDotMap.partialState_owned ops (LarkSwiGLU.upInput input) ou (LarkSwiGLU.projection shape) {m * h}),
    LarkReduction.owned_raceFree _ _ (LarkPairMap.partialState_owned (LarkSwiPointwise.profile {m * h}) ops (LarkSwiGLU.pairInput shape ops input) oh {m * h}),
    LarkReduction.owned_raceFree _ _ (LarkDotMap.partialState_owned ops (LarkSwiGLU.downInput shape ops input) oo (LarkFeedForward.stage2 shape) {m * n})⟩
theorem segment_equivalence (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) :
    extract (LarkDotMap.layout (LarkFeedForward.stage2 shape)) (LarkSwiGLU.finalState shape ops input outside)=some (spec ops input) := by
  have h:=LarkDotMap.extract_eq ops (LarkSwiGLU.downInput shape ops input) outside (LarkFeedForward.stage2 shape)
  rw [LarkDotMap.spec_eq_matrixSpec] at h
  exact h
theorem kernel_eq_spec (ops : Ops α) : LarkSwiGLU.Correct shape ops {warp} programs := segmentation ops
theorem kernel_eq_spec_pre (ops : Ops α) (input : Nat → Nat → α) (start : State α) (ou oh oo : Location → Option α)
    (pre : StdPre (LarkDotMap.layout (LarkSwiGLU.projection shape)) input start) :
    ∃ fg fu fh fo,LarkSwiGLU.RunsWith shape ops {warp} programs input start ou oh oo fg fu fh fo := by
  obtain ⟨og,rfl⟩:=pre
  exact kernel_eq_spec ops input og ou oh oo
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
        raise Refusal("configuration", "fresh output and positive timeout required")
    sources = {}
    for stage in STAGES:
        found = [p for p in (case / (stage + ".hip"), case / (stage + ".cu")) if p.is_file()]
        if len(found) != 1:
            raise Refusal("swiglu", "exactly one source per stage is required")
        sources[stage + ".cu"] = found[0].read_bytes()
        sources[stage + "-task.json"] = (case / (stage + "-task.json")).read_bytes()
    sources["reference.py"] = (case / "reference.py").read_bytes()
    tasks, trs = prepare({n: v.decode() for n, v in sources.items()})
    binary = lean_binary(lean)
    output.mkdir(parents=True)
    for n, v in sources.items():
        (output / n).write_bytes(v)
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
        "files": {n: digest((output / n).read_bytes()) for n in sorted(FILES)},
        "axiom_audit": log,
        "swiglu_dimensions": list(dimensions(tasks)),
        "kernel_launches": 4,
        "trusted_assumptions": [
            "Lean 4.19.0 kernel and printed standard axioms; pinned nonlinear machine",
            "Strict CUDA/HIP lowering and closed SwiGLU Torch AST formalization",
            "Host layouts/disjoint allocations and ordered launches wiring the same intermediate buffers",
            "Abstract scalar/half operations; hardware correspondence and numerical error outside theorem",
            "External race-free-phase/GPU-interleaving correspondence",
        ],
        "scope": "Four actual scalar launches: completion, race freedom, FP32 projections, FP16 intermediate rounding, every valid intermediate read from earlier final memory and every final output for all inputs/outside memories. Independent four-launch adaptation; not the original optimized two-launch kernel or PTX proof.",
    }
    write_json(output / "report.json", report)
    return report


def check(directory, *, lean=None, timeout=120):
    report = json.loads((directory / "report.json").read_text())
    if report.get("model_profile") != PROFILE or set(report["files"]) != FILES:
        raise Refusal("integrity", "unexpected SwiGLU profile/file set")
    for n, v in report["files"].items():
        if digest((directory / n).read_bytes()) != v:
            raise Refusal("integrity", "file changed: " + n)
    if report["model_hashes"] != model_hashes():
        raise Refusal("integrity", "different pinned machine/proof libraries")
    if (directory / "lean-toolchain").read_text() != TOOLCHAIN or (
        directory / "lakefile.toml"
    ).read_text() != LAKEFILE:
        raise Refusal("integrity", "unexpected standalone project configuration")
    tasks, trs = prepare({n: (directory / n).read_text() for n in SOURCE_FILES})
    dims = report.get("swiglu_dimensions")
    if (
        not isinstance(dims, list)
        or any(type(x) is not int for x in dims)
        or dims != list(dimensions(tasks))
        or type(report.get("kernel_launches")) is not int
        or report["kernel_launches"] != 4
    ):
        raise Refusal("integrity", "reported shape/launch count differs")
    if json.loads((directory / "translation.json").read_text()) != json.loads(
        json.dumps([tr.data() for tr in trs])
    ):
        raise Refusal("integrity", "translation differs from sources")
    if (directory / "Main.lean").read_text() != render(tasks, trs):
        raise Refusal("integrity", "theorem differs from source/reference/pipeline")
    ok, log = run_lean(directory, lean_binary(lean), timeout)
    if not ok:
        raise Refusal("proof", log)
    return log
