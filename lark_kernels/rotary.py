"""Full-size FP16 interleaved RoPE in the existing scalar machine."""

import ast
from dataclasses import replace
import json

from . import linear, matrix, pointwise
from .certificate import LAKEFILE, TOOLCHAIN, digest, lean_binary, model_path, run_lean, write_json
from .frontend import translate
from .ir import Buffer, Refusal, Task, lean_list, lean_node, node
from .spec import read_spec

PROFILE = "rotary-induction-v7"
FILES = pointwise.FILES


library_path = matrix.library_path


def parse_task(source):
    d = json.loads(source)
    buffers = d["buffers"]
    if len(buffers) != 4 or [b["role"] for b in buffers] != ["input"] * 3 + ["output"]:
        raise Refusal("rotary", "expected three inputs and one output")
    if any(
        b["dtype"] != "float16"
        or not isinstance(b["shape"], list)
        or len(b["shape"]) != 2
        or any(type(x) is not int or x <= 0 for x in b["shape"])
        for b in buffers
    ):
        raise Refusal("rotary", "expected positive rank-two FP16 shapes")
    x, c, s, out = [b["shape"] for b in buffers]
    m, dims = x
    if dims % 2 or c != [m, dims // 2] or s != c or out != x or m * dims >= 2147483648:
        raise Refusal(
            "rotary", "expected [M,D] input/output and [M,D/2] coefficients, even D, M*D<2^31"
        )
    warp = 32 if d.get("language", "cuda") == "cuda" else 64
    if d["launch"] != {"grid": m * dims, "block": 1, "warp": warp} or any(
        type(v) is not int for v in d["launch"].values()
    ):
        raise Refusal("rotary", "expected one scalar thread/block per output, native warp width")
    fuel = d.get("fuel", [8, 1, 1, 1])
    if fuel != [8, 1, 1, 1] or any(type(v) is not int for v in fuel):
        raise Refusal("rotary", "fuel must be [8,1,1,1]")
    small = json.loads(source)
    small["launch"]["grid"] = 2
    small["fuel"] = fuel
    for b, shape in zip(small["buffers"], ([1, 2], [1, 1], [1, 1], [1, 2])):
        b["shape"] = shape
    checked = Task.parse(json.dumps(small))
    return replace(
        checked,
        grid=m * dims,
        buffers=tuple(Buffer(b["name"], b["role"], tuple(b["shape"]), b["dtype"]) for b in buffers),
    )


def expected_program():
    ix = node("ivar", 0)
    pair = node("div", ix, node("const", 2))
    base = node("ivar", 1)

    def coeff(b):
        return node("un", "fromHalf", node("load", "global", b, pair))

    def body(even):
        return node(
            "un",
            "toHalf",
            node(
                "bin",
                "sub" if even else "add",
                node("bin", "mul", node("reg", 0), coeff(1 if even else 2)),
                node("bin", "mul", node("reg", 1), coeff(2 if even else 1)),
            ),
        )

    return [
        node("idx", 0, node("bid")),
        node("idx", 1, node("mul", pair, node("const", 2))),
        node("set", 0, node("un", "fromHalf", node("load", "global", 0, base))),
        node(
            "set",
            1,
            node("un", "fromHalf", node("load", "global", 0, node("add", base, node("const", 1)))),
        ),
        node("branch", node("eq", node("mod", ix, node("const", 2)), node("const", 0)), 7),
        node("store", "global", 3, ix, body(True)),
        node("jump", 8),
        node("store", "global", 3, ix, body(False)),
        node("halt"),
    ]


def reference_expression(m, d, names):
    x, c, s = names
    even = f"{x}.float().reshape({m},{d // 2},2).select(2,0)"
    odd = f"{x}.float().reshape({m},{d // 2},2).select(2,1)"
    return f"torch.stack(({even}*{c}.float()-{odd}*{s}.float(),{even}*{s}.float()+{odd}*{c}.float()),dim=-1).reshape({m},{d}).half()"


def prepare(source, reference, task_source):
    task = parse_task(task_source)
    tr = translate(source, task)
    if tr.shared or tr.program != expected_program():
        raise Refusal("rotary", "source differs from the proved interleaved-pair profile")
    tree = ast.parse(reference)
    fn = next((s for s in tree.body if isinstance(s, ast.FunctionDef)), None)
    if (
        fn is None
        or len(fn.body) != 1
        or not isinstance(fn.body[0], ast.Return)
        or fn.returns is not None
        or any(a.annotation is not None for a in fn.args.args)
    ):
        raise Refusal("rotary-reference", "expected one pure interleaved-pair return")
    names = [b.name for b in task.buffers[:3]]
    m, d = task.buffers[0].shape
    expected = ast.parse(reference_expression(m, d, names), mode="eval").body
    if ast.dump(fn.body[0].value) != ast.dump(expected):
        raise Refusal(
            "rotary-reference", "reference differs from the fixed reshape/select/stack operator"
        )
    # The full operator AST has already matched exactly. Validate the module,
    # imports, argument binding and dtypes using a minimal instance of that
    # same closed operator. Arbitrary shape-dependent code cannot reach here.
    fn.body[0].value = ast.parse(reference_expression(1, 2, names), mode="eval").body
    small = replace(
        task,
        grid=2,
        buffers=tuple(
            replace(b, shape=shape)
            for b, shape in zip(task.buffers, ((1, 2), (1, 1), (1, 1), (1, 2)))
        ),
    )
    read_spec(ast.unparse(tree), small)
    return task, tr


def model_hashes():
    return {
        **linear.model_hashes(),
        **{name.lower(): digest(library_path(name).read_bytes()) for name in ("Rotary",)},
    }


def render(task, tr):
    n = task.buffers[0].size // 2
    parts = [model_path(True).read_text()]
    for name, imported in [
        ("Pointwise", "Nonlinear"),
        ("Reduction", "Pointwise"),
        ("DotLoop", "Reduction"),
        ("Matrix", "DotLoop"),
        ("Bias", "Matrix"),
        ("Rotary", "Bias"),
    ]:
        text = library_path(name).read_text()
        prefix = "import Lark." + imported + "\n"
        if not text.startswith(prefix):
            raise Refusal("installation", "unexpected " + name + " library import")
        parts.append(text.removeprefix(prefix))
    return (
        "\n".join(parts)
        + f"""
namespace LarkCertificate
open LarkNonlinear
def layout : Layout := LarkRotary.layout {n}
def geometry : Geometry := LarkRotary.geometry {n} {task.warp}
def fuel : Fuel := LarkRotary.fuel
def program : List Instr := {lean_list(lean_node(i) for i in tr.program)}
def spec (ops : Ops α) (input : Nat → Nat → α) : List α :=
  LarkRotary.spec ops {n} input
def finalState (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) : State α :=
  LarkRotary.partialState ops {n} input outside {2 * n}
theorem segmentation_data : program = LarkRotary.program := by rfl
theorem segmentation (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) :
    runLaunch ops layout geometry fuel program (initial layout input outside) =
      some (finalState ops input outside) := by
  rw [segmentation_data]
  exact LarkRotary.launch_eq ops {n} {task.warp} input outside
    (by decide) (by decide) (by decide)
theorem race_free (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) :
    raceFree geometry (finalState ops input outside).trace = true := by
  exact LarkBias.owned_raceFree geometry _
    (LarkRotary.partialState_owned ops {n} input outside {2 * n})
theorem segment_equivalence (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) :
    extract layout (finalState ops input outside) = some (spec ops input) := by
  exact LarkRotary.partialState_extract ops {n} input outside
theorem kernel_eq_spec (ops : Ops α) :
    Correct ops layout geometry fuel program (spec ops) := by
  intro input outside
  exact ⟨finalState ops input outside, segmentation ops input outside,
    race_free ops input outside, segment_equivalence ops input outside⟩
theorem kernel_eq_spec_pre (ops : Ops α) (input : Nat → Nat → α) (s : State α)
    (pre : StdPre layout input s) :
    ∃ final, runLaunch ops layout geometry fuel program s = some final ∧
      raceFree geometry final.trace = true ∧ extract layout final = some (spec ops input) := by
  exact correct_from_pre ops layout geometry fuel program (spec ops)
    (kernel_eq_spec ops) input s pre
#print axioms segmentation_data
#print axioms segmentation
#print axioms race_free
#print axioms segment_equivalence
#print axioms kernel_eq_spec
#print axioms kernel_eq_spec_pre
end LarkCertificate
"""
    )


def verify(kernel, reference, task_path, output, *, lean=None, timeout=120):
    if output.exists() or timeout <= 0:
        raise Refusal("configuration", "fresh output directory and positive timeout required")
    sources = {
        "kernel.cu": kernel.read_bytes(),
        "reference.py": reference.read_bytes(),
        "task.json": task_path.read_bytes(),
    }
    task, tr = prepare(
        *(sources[x].decode("utf-8") for x in ("kernel.cu", "reference.py", "task.json"))
    )
    binary = lean_binary(lean)
    output.mkdir(parents=True)
    for name, data in sources.items():
        (output / name).write_bytes(data)
    (output / "Main.lean").write_text(render(task, tr))
    (output / "lean-toolchain").write_text(TOOLCHAIN)
    (output / "lakefile.toml").write_text(LAKEFILE)
    write_json(output / "translation.json", tr.data())
    ok, log = run_lean(output, binary, timeout)
    (output / "lean-1.log").write_text(log)
    report = {
        "schema": 1,
        "status": "verified" if ok else "unproved",
        "model_profile": PROFILE,
        "model_hashes": model_hashes(),
        "source_readback": True,
        "model_calls": 0,
        "files": {f: digest((output / f).read_bytes()) for f in sorted(FILES)},
        "axiom_audit": log,
        "rotary_shape": list(task.buffers[0].shape),
        "trusted_assumptions": [
            "Lean 4.19.0 kernel and printed standard axioms; pinned Nonlinear machine",
            "Strict CUDA/HIP lowering and the closed interleaved rotary Torch AST formalization",
            "Host launch, contiguous FP16 buffers, aligned disjoint named allocations",
            "Abstract scalar/half operations; hardware correspondence and floating-point error outside theorem",
            "External reduction from race-free phases to GPU interleavings",
        ],
        "scope": "Full branch and grid in existing runLaunch: completion, race freedom, every output, all inputs and arbitrary outside memory. One thread per output; independent scalar RoPE, not the optimized original paper kernel.",
    }
    write_json(output / "report.json", report)
    return report


def check(directory, *, lean=None, timeout=120):
    report = json.loads((directory / "report.json").read_text())
    if report.get("model_profile") != PROFILE or set(report["files"]) != FILES:
        raise Refusal("integrity", "unexpected rotary profile or file set")
    for name, expected in report["files"].items():
        if digest((directory / name).read_bytes()) != expected:
            raise Refusal("integrity", f"file changed: {name}")
    if report["model_hashes"] != model_hashes():
        raise Refusal("integrity", "different pinned machine or proof libraries")
    if (directory / "lean-toolchain").read_text() != TOOLCHAIN or (
        directory / "lakefile.toml"
    ).read_text() != LAKEFILE:
        raise Refusal("integrity", "unexpected standalone project configuration")
    task, tr = prepare(
        *((directory / x).read_text() for x in ("kernel.cu", "reference.py", "task.json"))
    )
    shape = report.get("rotary_shape")
    if (
        not isinstance(shape, list)
        or any(type(x) is not int for x in shape)
        or shape != list(task.buffers[0].shape)
    ):
        raise Refusal("integrity", "reported matrix dimensions differs from the fixed signature")
    if json.loads((directory / "translation.json").read_text()) != json.loads(
        json.dumps(tr.data())
    ):
        raise Refusal("integrity", "translation differs from source")
    if (directory / "Main.lean").read_text() != render(task, tr):
        raise Refusal("integrity", "theorem differs from the fixed source/reference statement")
    ok, log = run_lean(directory, lean_binary(lean), timeout)
    if not ok:
        raise Refusal("proof", log)
    return log
