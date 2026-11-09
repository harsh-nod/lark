"""Full-size valid square NCHW FP16 convolutions through checked dot-loop profiles."""

import ast
from dataclasses import replace
import json
from pathlib import Path
import sysconfig

from . import gemv, pointwise
from .certificate import LAKEFILE, TOOLCHAIN, digest, lean_binary, model_path, run_lean, write_json
from .frontend import translate
from .ir import Buffer, Refusal, Task, lean_list, lean_node, node
from .spec import read_spec

PROFILE = "convolution-induction-v8"
FILES = pointwise.FILES


def library_path(name):
    repo = Path(__file__).resolve().parent.parent / "lean/Lark" / (name + ".lean")
    if repo.exists():
        return repo
    installed = Path(sysconfig.get_path("data")) / "share/lark/lean/Lark" / (name + ".lean")
    if installed.exists():
        return installed
    raise Refusal("installation", "pinned " + name + " proof library is missing")


def is_depthwise(task):
    a, b, _ = task.buffers
    return b.shape[1] == 1 and b.shape[0] == a.shape[1]


def dimensions(task):
    a, b, _ = task.buffers
    cin, h, cout, k = a.shape[1], a.shape[2], b.shape[0], b.shape[2]
    return cin, cout, h, k, cin if is_depthwise(task) else 1


def parse_task(source):
    d = json.loads(source)
    buffers = d["buffers"]
    if len(buffers) != 3 or [b["role"] for b in buffers] != ["input", "input", "output"]:
        raise Refusal("convolution", "expected two inputs and one output")
    if any(
        b["dtype"] != "float16"
        or not isinstance(b["shape"], list)
        or len(b["shape"]) != 4
        or any(type(x) is not int or x <= 0 for x in b["shape"])
        for b in buffers
    ):
        raise Refusal("convolution", "expected positive rank-four FP16 shapes")
    x, w, out = [b["shape"] for b in buffers]
    batch, cin, h, width = x
    cout, cw, k, kw = w
    side = h - k + 1
    if (
        batch != 1
        or width != h
        or kw != k
        or k > h
        or not (cw == cin or (cw == 1 and cout == cin))
        or out != [1, cout, side, side]
    ):
        raise Refusal(
            "convolution",
            "expected valid square NCHW dense/depthwise convolution, batch=1, no padding/bias",
        )
    if max(cin * h * h, cout * cw * k * k, cout * side * side) >= 2147483648:
        raise Refusal("convolution", "all allocations must be below 2^31 cells")
    warp = 32 if d.get("language", "cuda") == "cuda" else 64
    if d["launch"] != {"grid": cout * side * side, "block": 1, "warp": warp} or any(
        type(v) is not int for v in d["launch"].values()
    ):
        raise Refusal(
            "convolution", "expected one scalar thread/block per output, native warp width"
        )
    fuel = d.get("fuel", [4 * cw * k * k + 6, 1, 1, 1])
    if fuel != [4 * cw * k * k + 6, 1, 1, 1] or any(type(v) is not int for v in fuel):
        raise Refusal("convolution", "fuel must match the complete counted reduction")
    small = json.loads(source)
    small["launch"]["grid"] = 1
    small["fuel"] = fuel
    for b in small["buffers"]:
        b["shape"] = [1, 1, 1, 1]
    checked = Task.parse(json.dumps(small))
    return replace(
        checked,
        grid=cout * side * side,
        buffers=tuple(Buffer(b["name"], b["role"], tuple(b["shape"]), b["dtype"]) for b in buffers),
    )


def expected_program(task):
    cin, cout, h, k, _ = dimensions(task)
    side = h - k + 1
    reduce = task.buffers[1].shape[1] * k * k
    ix, j = node("ivar", 0), node("ivar", 1)

    def c(v):
        return node("const", v)

    def mul(a, b):
        return node("mul", a, b)

    def add(a, b):
        return node("add", a, b)

    def div(a, b):
        return node("div", a, b)

    def mod(a, b):
        return node("mod", a, b)

    channel = div(ix, c(side * side)) if is_depthwise(task) else div(j, c(k * k))
    row = add(add(mul(channel, c(h)), mod(div(ix, c(side)), c(side))), mod(div(j, c(k)), c(k)))
    a_index = add(add(mul(row, c(h)), mod(ix, c(side))), mod(j, c(k)))
    b_index = add(mul(div(ix, c(side * side)), c(reduce)), j)
    program = gemv.expected_program(reduce)
    program[4] = node(
        "set",
        0,
        node(
            "bin",
            "add",
            node("reg", 0),
            node(
                "bin",
                "mul",
                node("un", "fromHalf", node("load", "global", 0, a_index)),
                node("un", "fromHalf", node("load", "global", 1, b_index)),
            ),
        ),
    )
    return program


def reference_expression(names, groups):
    a, b = names
    return f"torch.conv2d({a}.float(),{b}.float(),groups={groups}).half()"


def prepare(source, reference, task_source):
    task = parse_task(task_source)
    tr = translate(source, task)
    if tr.shared or tr.program != expected_program(task):
        raise Refusal("convolution", "source differs from the proved valid-convolution profile")
    tree = ast.parse(reference)
    fn = next((x for x in tree.body if isinstance(x, ast.FunctionDef)), None)
    if (
        fn is None
        or len(fn.body) != 1
        or not isinstance(fn.body[0], ast.Return)
        or fn.returns is not None
        or any(a.annotation is not None for a in fn.args.args)
    ):
        raise Refusal("convolution-reference", "expected one pure convolution return")
    names = [b.name for b in task.buffers[:2]]
    expected = ast.parse(reference_expression(names, dimensions(task)[4]), mode="eval").body
    if ast.dump(fn.body[0].value) != ast.dump(expected):
        raise Refusal(
            "convolution-reference", "expected the fixed valid convolution with matching groups"
        )
    # Match the full operator first, then validate imports/binding/dtype with
    # the same closed operator at its minimal shape. No arbitrary lifting.
    fn.body[0].value = ast.parse(reference_expression(names, 1), mode="eval").body
    small = replace(
        task, grid=1, buffers=tuple(replace(b, shape=(1, 1, 1, 1)) for b in task.buffers)
    )
    read_spec(ast.unparse(tree), small)
    return task, tr


def model_hashes():
    return {
        **gemv.model_hashes(),
        **{
            name.lower(): digest(library_path(name).read_bytes())
            for name in ("DotLoop", "Matrix", "Convolution")
        },
    }


def render(task, tr):
    cin, cout, h, k, _ = dimensions(task)
    parts = [model_path(True).read_text()]
    for name, imported in [
        ("Pointwise", "Nonlinear"),
        ("Reduction", "Pointwise"),
        ("DotLoop", "Reduction"),
        ("Matrix", "DotLoop"),
        ("Convolution", "Matrix"),
    ]:
        text = library_path(name).read_text()
        prefix = "import Lark." + imported + "\n"
        if not text.startswith(prefix):
            raise Refusal("installation", "unexpected " + name + " library import")
        parts.append(text.removeprefix(prefix))
    profile = (
        f"LarkConvolution.depthProfile {cin} {h} {k} " + " ".join(["(by decide)"] * 6)
        if is_depthwise(task)
        else f"LarkConvolution.denseProfile {cin} {cout} {h} {k} " + " ".join(["(by decide)"] * 7)
    )
    return (
        "\n".join(parts)
        + f"""
namespace LarkCertificate
open LarkNonlinear
def profile : LarkDot.Profile := {profile}
def layout : Layout := LarkDot.layout profile
def geometry : Geometry := LarkDot.geometry profile {task.warp}
def fuel : Fuel := LarkDot.fuel profile
def program : List Instr := {lean_list(lean_node(i) for i in tr.program)}
def spec (ops : Ops α) (input : Nat → Nat → α) : List α :=
  LarkDot.matrixSpec ops profile input
def finalState (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) : State α :=
  LarkDot.partialState ops input outside profile profile.n
theorem segmentation_data : program = LarkDot.program profile := by rfl
theorem segmentation (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) :
    runLaunch ops layout geometry fuel program (initial layout input outside) =
      some (finalState ops input outside) := by
  rw [segmentation_data]
  exact LarkDot.launch_eq ops input outside profile {task.warp}
    (by decide) (by decide) (by decide) (by decide)
theorem race_free (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) :
    raceFree geometry (finalState ops input outside).trace = true := by
  exact LarkReduction.owned_raceFree geometry _
    (LarkDot.partialState_owned ops input outside profile profile.n)
theorem segment_equivalence (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) :
    extract layout (finalState ops input outside) = some (spec ops input) := by
  have he := LarkDot.extract_eq ops input outside profile
  rw [LarkDot.spec_eq_matrixSpec] at he
  exact he
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
        "convolution_dimensions": list(dimensions(task)),
        "trusted_assumptions": [
            "Lean 4.19.0 kernel and printed standard axioms; pinned Nonlinear machine",
            "Strict CUDA/HIP lowering and the closed valid-convolution Torch AST formalization",
            "Host launch, contiguous FP16 buffers, aligned disjoint named allocations",
            "Abstract scalar/half operations; hardware correspondence and floating-point error outside theorem",
            "External reduction from race-free phases to GPU interleavings",
        ],
        "scope": "Full counted loop and grid in existing runLaunch: completion, race freedom, every output, all inputs and arbitrary outside memory. One thread per output; independent scalar valid convolution, not the optimized original paper kernel.",
    }
    write_json(output / "report.json", report)
    return report


def check(directory, *, lean=None, timeout=120):
    report = json.loads((directory / "report.json").read_text())
    if report.get("model_profile") != PROFILE or set(report["files"]) != FILES:
        raise Refusal("integrity", "unexpected convolution profile or file set")
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
    shape = report.get("convolution_dimensions")
    if (
        not isinstance(shape, list)
        or any(type(x) is not int for x in shape)
        or shape != list(dimensions(task))
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
