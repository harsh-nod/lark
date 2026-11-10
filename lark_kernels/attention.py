"""Three-launch dense SDPA/GQA with explicit FP32 scores and probabilities."""

import ast
from dataclasses import replace
import json
import math

from . import gemv, matrix
from .certificate import LAKEFILE, TOOLCHAIN, digest, lean_binary, model_path, run_lean, write_json
from .frontend import translate
from .ir import Buffer, Refusal, Task, lean_list, lean_node, node
from .spec import read_spec

PROFILE = "attention-pipeline-v12"
STAGES = ("score", "softmax", "value")
SOURCE_FILES = tuple(n for s in STAGES for n in (s + ".cu", s + "-task.json")) + ("reference.py",)
FILES = set(SOURCE_FILES) | {"Main.lean", "translation.json", "lean-toolchain", "lakefile.toml"}


def stage_task(source, stage):
    d = json.loads(source)
    bufs = d["buffers"]
    roles = ["input", "output"] if stage == "softmax" else ["input", "input", "output"]
    dtypes = {
        "score": ["float16", "float16", "float32"],
        "softmax": ["float32", "float32"],
        "value": ["float32", "float16", "float16"],
    }[stage]
    if (
        len(bufs) != len(roles)
        or [b["role"] for b in bufs] != roles
        or [b["dtype"] for b in bufs] != dtypes
        or any(
            not isinstance(b["shape"], list)
            or len(b["shape"]) != 3
            or any(type(x) is not int or x <= 0 for x in b["shape"])
            or math.prod(b["shape"]) >= 2147483648
            for b in bufs
        )
    ):
        raise Refusal("attention", "expected positive rank-three, typed, bounded stage allocations")
    count = math.prod(bufs[-1]["shape"])
    warp = 32 if d.get("language", "cuda") == "cuda" else 64
    reduction = bufs[0]["shape"][-1]
    fuel = [10 * reduction + 9 if stage == "softmax" else 4 * reduction + 6, 1, 1, 1]
    if (
        d["launch"] != {"grid": count, "block": 1, "warp": warp}
        or any(type(x) is not int for x in d["launch"].values())
        or d.get("fuel") != fuel
        or any(type(x) is not int for x in d["fuel"])
    ):
        raise Refusal(
            "attention",
            "expected one scalar thread/block per output, native warp and exact stage fuel",
        )
    small = json.loads(source)
    small["launch"]["grid"] = 1
    for b in small["buffers"]:
        b["shape"] = [1, 1, 1]
    checked = Task.parse(json.dumps(small))
    return replace(
        checked,
        grid=count,
        buffers=tuple(Buffer(b["name"], b["role"], tuple(b["shape"]), b["dtype"]) for b in bufs),
    )


def dimensions(tasks):
    hq, seq, dim = tasks[0].buffers[0].shape
    hkv = tasks[0].buffers[1].shape[0]
    return hq, hkv, seq, dim


def reference_expression(groups, scale, names=("q", "k", "v")):
    q, k, v = [n + ".float()" for n in names]
    if groups != 1:
        k += f".repeat_interleave({groups},dim=0)"
        v += f".repeat_interleave({groups},dim=0)"
    return f"((({q} @ {k}.transpose(-1,-2)) / {scale}.0).softmax(dim=-1) @ {v}).half()"


def expected_dot(task, groups, scale, score):
    _, seq, dim = task.buffers[-1].shape
    # Score output is [Hq,S,S]; its actual reduction is the query width D.
    if score:
        dim = task.buffers[0].shape[-1]
    ix, j = node("ivar", 0), node("ivar", 1)

    def c(n):
        return node("const", n)

    def binary(op, a, b):
        return node(op, a, b)

    def add(a, b):
        return binary("add", a, b)

    def mul(a, b):
        return binary("mul", a, b)

    def div(a, b):
        return binary("div", a, b)

    def mod(a, b):
        return binary("mod", a, b)

    block = seq * seq if score else seq * dim
    if score:
        ai = add(
            mul(div(ix, c(seq * seq)), c(seq * dim)),
            add(mul(mod(div(ix, c(seq)), c(seq)), c(dim)), j),
        )
        row, col = mod(ix, c(seq)), j
    else:
        ai = add(
            mul(div(ix, c(seq * dim)), c(seq * seq)),
            add(mul(mod(div(ix, c(dim)), c(seq)), c(seq)), j),
        )
        row, col = j, mod(ix, c(dim))
    head = div(div(ix, c(block)), c(groups))
    bi = add(mul(head, c(seq * dim)), add(mul(row, c(dim)), col))
    left = node("load", "global", 0, ai)
    right = node("un", "fromHalf", node("load", "global", 1, bi))
    if score:
        left = node("un", "fromHalf", left)
    p = gemv.expected_program(dim if score else seq)
    p[4] = node("set", 0, node("bin", "add", node("reg", 0), node("bin", "mul", left, right)))
    output = (
        node("bin", "div", node("reg", 0), node("lit", scale, 1))
        if score
        else node("un", "toHalf", node("reg", 0))
    )
    p[7] = node("store", "global", 2, ix, output)
    return p


def expected_softmax(n):
    ix, j = node("ivar", 0), node("ivar", 1)
    ri = node("add", node("mul", node("div", ix, node("const", n)), node("const", n)), j)
    acc, ctx, val = [node("reg", i) for i in range(3)]
    exp = node("un", "exp", node("bin", "sub", val, ctx))
    return [
        node("idx", 0, node("bid")),
        node("idx", 1, node("const", 0)),
        node("set", 0, node("load", "global", 0, ri)),
        node("set", 1, node("lit", 0, 1)),
        node("set", 2, node("lit", 0, 1)),
        node("idx", 1, node("const", 1)),
        node("branch", node("lt", j, node("const", n)), 11),
        node("set", 2, node("load", "global", 0, ri)),
        node("set", 0, node("bin", "max", acc, val)),
        node("idx", 1, node("add", j, node("const", 1))),
        node("jump", 6),
        node("set", 1, acc),
        node("set", 0, node("lit", 0, 1)),
        node("idx", 1, node("const", 0)),
        node("branch", node("lt", j, node("const", n)), 19),
        node("set", 2, node("load", "global", 0, ri)),
        node("set", 0, node("bin", "add", acc, exp)),
        node("idx", 1, node("add", j, node("const", 1))),
        node("jump", 14),
        node("set", 2, node("load", "global", 0, ix)),
        node("store", "global", 1, ix, node("bin", "div", exp, acc)),
        node("halt"),
    ]


def prepare(sources):
    tasks = [stage_task(sources[s + "-task.json"], s) for s in STAGES]
    a, b, c = tasks
    hq, hkv, seq, dim = dimensions(tasks)
    if hq % hkv or a.buffers[1].shape != (hkv, seq, dim):
        raise Refusal("attention", "KV heads must divide query heads with matching sequence/width")
    groups = hq // hkv
    scale = math.isqrt(dim)
    if scale * scale != dim:
        raise Refusal("attention", "this profile requires an integer square-root scale")
    if (
        a.buffers[2].shape != (hq, seq, seq)
        or a.buffers[2] != replace(b.buffers[0], role="output")
        or b.buffers[1].shape != a.buffers[2].shape
        or b.buffers[1] != replace(c.buffers[0], role="output")
        or c.buffers[1].shape != (hkv, seq, dim)
        or c.buffers[2].shape != a.buffers[0].shape
        or len({t.language for t in tasks}) != 1
        or len({t.warp for t in tasks}) != 1
        or len({t.entry for t in tasks}) != 3
    ):
        raise Refusal("attention", "stage signatures, heads, entries or intermediate wiring differ")
    names = (a.buffers[0].name, a.buffers[1].name, c.buffers[1].name)
    if len(set((*names, a.buffers[2].name, b.buffers[1].name, c.buffers[2].name))) != 6:
        raise Refusal("attention", "six distinct named allocations are required")
    trs = [translate(sources[s + ".cu"], t) for s, t in zip(STAGES, tasks)]
    expected = (
        expected_dot(a, groups, scale, True),
        expected_softmax(seq),
        expected_dot(c, groups, scale, False),
    )
    if any(tr.shared or tr.program != p for tr, p in zip(trs, expected)):
        raise Refusal(
            "attention",
            "source differs from checked grouped/scaled/FP32-softmax/FP16-output programs",
        )
    reference = sources["reference.py"]
    tree = ast.parse(reference)
    fn = next((x for x in tree.body if isinstance(x, ast.FunctionDef)), None)
    if (
        fn is None
        or len(fn.body) != 1
        or not isinstance(fn.body[0], ast.Return)
        or ast.dump(fn.body[0].value)
        != ast.dump(ast.parse(reference_expression(groups, scale, names), mode="eval").body)
    ):
        raise Refusal(
            "attention-reference",
            "expected the closed noncausal dense scaled-dot-product attention AST",
        )
    small = Task.parse(
        json.dumps(
            {
                "name": "attention_module_check",
                "entry": "attention_module_check",
                "language": a.language,
                "launch": {"grid": groups, "block": 1, "warp": a.warp},
                "buffers": [
                    {"name": name, "role": role, "shape": shape, "dtype": "float16"}
                    for name, role, shape in (
                        (names[0], "input", [groups, 1, 1]),
                        (names[1], "input", [1, 1, 1]),
                        (names[2], "input", [1, 1, 1]),
                        (c.buffers[2].name, "output", [groups, 1, 1]),
                    )
                ],
            }
        )
    )
    read_spec(reference, small)
    return tasks, trs


def model_hashes():
    return {
        **matrix.model_hashes(),
        **{
            n.lower(): digest(matrix.library_path(n).read_bytes())
            for n in (
                "DotMap",
                "UnaryMap",
                "FoldPhase",
                "RowPhase",
                "RowSoftmax",
                "AttentionAddress",
                "AttentionPipeline",
            )
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
        ("UnaryMap", ["Pointwise"]),
        ("FoldPhase", ["UnaryMap", "Reduction"]),
        ("RowPhase", ["FoldPhase"]),
        ("RowSoftmax", ["RowPhase", "Matrix"]),
        ("AttentionAddress", ["DotMap", "RowSoftmax"]),
        ("AttentionPipeline", ["AttentionAddress"]),
    ]:
        text = matrix.library_path(name).read_text()
        prefix = "".join("import Lark." + i + "\n" for i in imports)
        if not text.startswith(prefix):
            raise Refusal("installation", "unexpected " + name + " proof library imports")
        parts.append(text.removeprefix(prefix))
    hq, hkv, seq, dim = dimensions(tasks)
    groups = hq // hkv
    scale = math.isqrt(dim)
    warp = tasks[0].warp
    programs = [lean_list(lean_node(i) for i in tr.program) for tr in trs]
    return (
        "\n".join(parts)
        + f"""
namespace LarkCertificate
open LarkNonlinear
def shape : LarkAttention.Shape := ⟨{hkv},{groups},{seq},{dim},{scale},
  by decide,by decide,by decide,by decide,by decide,by decide,by decide,by decide,by decide⟩
def programs : LarkAttention.Programs := ⟨{programs[0]},{programs[1]},{programs[2]}⟩
def spec (ops : Ops α) (input : Nat → Nat → α) : List α := LarkAttention.spec shape ops input
theorem segmentation_data : programs=LarkAttention.programs shape := by rfl
theorem segmentation (ops : Ops α) : LarkAttention.Correct shape ops {warp} programs := by
  rw [segmentation_data]
  exact LarkAttention.correct shape ops {warp} (by decide)
theorem race_free (ops : Ops α) (input : Nat → Nat → α) (oq os ov : Location → Option α) :
    raceFree (LarkDotMap.geometry (LarkAttention.scoreProfile shape) {warp}) (LarkAttention.scoreFinal shape ops input oq).trace=true ∧
    raceFree (LarkUnaryMap.geometry (LarkRowSoftmax.total (LarkAttention.softmaxShape shape)) {warp}) (LarkAttention.softFinal shape ops input os).trace=true ∧
    raceFree (LarkDotMap.geometry (LarkAttention.valueProfile shape) {warp}) (LarkAttention.finalState shape ops input ov).trace=true := by
  exact ⟨LarkReduction.owned_raceFree _ _ (LarkDotMap.partialState_owned ops input oq (LarkAttention.scoreProfile shape) {hq * seq * seq}),
    LarkUnaryMap.owned_raceFree _ _ (LarkUnaryMap.partialState_owned (LarkRowSoftmax.profile (LarkAttention.softmaxShape shape)) ops (LarkAttention.softInput shape ops input) os {hq * seq * seq}),
    LarkReduction.owned_raceFree _ _ (LarkDotMap.partialState_owned ops (LarkAttention.valueInput shape ops input) ov (LarkAttention.valueProfile shape) {hq * seq * dim})⟩
theorem segment_equivalence (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) :
    extract (LarkDotMap.layout (LarkAttention.valueProfile shape)) (LarkAttention.finalState shape ops input outside)=some (spec ops input) := by
  have h:=LarkDotMap.extract_eq ops (LarkAttention.valueInput shape ops input) outside (LarkAttention.valueProfile shape)
  rw [LarkDotMap.spec_eq_matrixSpec] at h
  exact h
theorem kernel_eq_spec (ops : Ops α) : LarkAttention.Correct shape ops {warp} programs := segmentation ops
theorem kernel_eq_spec_pre (ops : Ops α) (input : Nat → Nat → α) (start : State α) (os ov : Location → Option α)
    (pre : StdPre (LarkDotMap.layout (LarkAttention.scoreProfile shape)) input start) :
    ∃ fs fp fo,LarkAttention.RunsWith shape ops {warp} programs input start os ov fs fp fo := by
  obtain ⟨oq,rfl⟩:=pre
  exact kernel_eq_spec ops input oq os ov
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
    for s in STAGES:
        found = [p for p in (case / (s + ".hip"), case / (s + ".cu")) if p.is_file()]
        if len(found) != 1:
            raise Refusal("attention", "exactly one source per stage required")
        sources[s + ".cu"] = found[0].read_bytes()
        sources[s + "-task.json"] = (case / (s + "-task.json")).read_bytes()
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
        "attention_dimensions": list(dimensions(tasks)),
        "kernel_launches": 3,
        "trusted_assumptions": [
            "Lean 4.19.0 kernel and printed standard axioms; pinned nonlinear machine",
            "Strict CUDA/HIP lowering and closed dense noncausal scaled-dot-product/GQA reference formalization",
            "Host layouts/disjoint allocations and ordered launches wiring the same FP32 intermediate buffers",
            "Abstract scalar/half operations; hardware correspondence and numerical error outside theorem",
            "External race-free-phase/GPU-interleaving correspondence",
        ],
        "scope": "Three actual launches prove completion, race freedom, grouped KV addresses, FP32 scores/probabilities, every valid intermediate read and every final output for all inputs/outside memories. Independent dense SDPA/GQA adaptation, not FlashAttention online softmax, original optimized sources, PTX proof or H100 measurement.",
    }
    write_json(output / "report.json", report)
    return report


def check(directory, *, lean=None, timeout=120):
    report = json.loads((directory / "report.json").read_text())
    if report.get("model_profile") != PROFILE or set(report["files"]) != FILES:
        raise Refusal("integrity", "unexpected attention profile/file set")
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
    dims = report.get("attention_dimensions")
    if (
        not isinstance(dims, list)
        or any(type(x) is not int for x in dims)
        or dims != list(dimensions(tasks))
        or type(report.get("kernel_launches")) is not int
        or report["kernel_launches"] != 3
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
