"""Deterministic statement generation, bounded proposal loop, and standalone export."""

from __future__ import annotations

from dataclasses import asdict
from hashlib import sha256
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sysconfig

from .frontend import translate
from .ir import Refusal, Task, lean_list, lean_node, lean_spec
from .machine import Machine, preflight
from .spec import read_spec


TOOLCHAIN = "leanprover/lean4:v4.19.0\n"
LAKEFILE = 'name = "lark_certificate"\nversion = "0.1.0"\ndefaultTargets = ["Main"]\n\n[[lean_lib]]\nname = "Main"\n'
AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
DEFAULT_PROOFS = {
    "segmentation_data": "by simp [flatten, flattenSegment, segments, program]",
    "race_free": (
        "by\n  refine ⟨finalState unitOps (fun _ _ => ()) (fun _ => some ()), rfl, ?_⟩\n"
        "  have htrace : (finalState unitOps (fun _ _ => ()) (fun _ => some ())).trace = traceData := by rfl\n"
        "  rw [htrace]\n  decide"
    ),
    "segment_equivalence": (
        "by\n  intro input outside\n  rw [segmentation_data]\n"
        "  refine ⟨finalState ops input outside, rfl, ?_, rfl⟩\n"
        "  have htrace : (finalState ops input outside).trace = traceData := by rfl\n"
        "  rw [htrace]\n  decide"
    ),
}
TRUST = [
    "Lean 4.19.0, its kernel and standard axioms (actual dependencies printed below)",
    "The pinned scalar GPU machine and its per-operation definitions",
    "Python CUDA/HIP parser, fixed lowering, and token read-back formatter",
    "Python PyTorch AST formalization of the independent reference module",
    "Host launch geometry, contiguous float32 layouts, aligned and disjoint named buffers",
    "Exact arithmetic interpretation: floating-point rounding and numerical error are outside the theorem",
    "Race-free phase reduction from the sequential folds to GPU interleavings (external metatheory)",
]
SCOPE = [
    "Bounded, concrete shapes and one-dimensional launches; all input scalar values",
    "Only float32 buffers; scalar +, -, *, max; exact nonnegative int32 index arithmetic",
    "Warp/block/grid folds; CUDA/HIP frontend exposes block barriers, full warp barriers, and halt",
    "No PTX, tensor-core collectives, async operations, atomics, data-dependent control, or numerical guarantee",
    "Full hardware conformance is not established; finite MI300X scalar samples are separate evidence",
    "Syntactic segment grouping and repetition; no general induction-based loop segmentation",
    "Only computations with the same scalar expression structure currently prove automatically",
]


def digest(data: bytes):
    return sha256(data).hexdigest()


def model_path(extended=False):
    filename = "Nonlinear.lean" if extended else "Model.lean"
    repo = Path(__file__).resolve().parent.parent / "lean" / "Lark" / filename
    if repo.exists():
        return repo
    installed = Path(sysconfig.get_path("data")) / "share" / "lark" / "lean" / "Lark" / filename
    if installed.exists():
        return installed
    raise Refusal("installation", "pinned Lean machine model is missing")


def extended_model(task, translation, spec):
    def visit(n):
        return (
            n.op == "un"
            or (n.op == "bin" and n.args[0] == "div")
            or any(visit(a) for a in n.args if hasattr(a, "op"))
        )

    return any(b.dtype == "float16" for b in task.buffers) or any(
        visit(n) for n in [*translation.program, *spec]
    )


def lean_binary(explicit=None):
    binary = explicit or os.environ.get("LARK_LEAN") or shutil.which("lean")
    if not binary:
        raise Refusal(
            "toolchain", "Lean is required for certification; install Lean 4.19.0 or set LARK_LEAN"
        )
    # Elan proxies dispatch on argv[0]; preserve the executable's symlink name.
    binary = str(Path(binary).absolute())
    try:
        r = subprocess.run([binary, "--version"], text=True, capture_output=True, timeout=30)
    except (OSError, subprocess.TimeoutExpired) as e:
        raise Refusal("toolchain", str(e)) from e
    if r.returncode or not re.search(r"version 4\.19\.0(?:\s|,)", r.stdout):
        raise Refusal(
            "toolchain", f"expected Lean 4.19.0, got {r.stdout.strip()} {r.stderr.strip()}"
        )
    return binary


def validate_proofs(proofs):
    if set(proofs) != set(DEFAULT_PROOFS):
        raise Refusal("proposal", "proof proposal must contain the three fixed proof slots")
    forbidden = re.compile(
        r"\b(sorry|admit|axiom|constant|unsafe|native_decide|run_tac|elab|macro|syntax|"
        r"def|abbrev|theorem|example|instance|inductive|structure|namespace|end|section|"
        r"variable|import|set_option|attribute|opaque|initialize)\b|#|/-|--"
    )
    for name, proof in proofs.items():
        if not isinstance(proof, str) or len(proof) > 20000 or not proof.strip().startswith("by"):
            raise Refusal(
                "proposal", f"{name}: expected a bounded tactic proof beginning with 'by'"
            )
        if forbidden.search(proof):
            raise Refusal(
                "proposal",
                f"{name}: declarations, unchecked evaluation, and admission are forbidden",
            )


def default_segments(program):
    # Keep barrier-delimited chunks visible. This proposal is checked, not trusted.
    chunks, chunk = [], []
    for i, instruction in enumerate(program):
        chunk.append(i)
        if instruction.op in {"barrier", "halt"}:
            chunks.append({"seq": [{"op": j} for j in chunk]})
            chunk = []
    if chunk:
        chunks.append({"seq": [{"op": j} for j in chunk]})
    return chunks


def emit_segment(s, program, depth=0):
    if depth > 16 or not isinstance(s, dict) or len(s) != 1:
        raise Refusal("segmentation", "invalid segment tree")
    if "op" in s:
        i = s["op"]
        if type(i) is not int or not 0 <= i < len(program):
            raise Refusal("segmentation", "instruction index out of range")
        return f"(.op {lean_node(program[i])})"
    if "seq" in s and isinstance(s["seq"], list):
        return f"(.seq {lean_list(emit_segment(x, program, depth + 1) for x in s['seq'])})"
    if "repeat" in s:
        r = s["repeat"]
        if not isinstance(r, dict) or set(r) != {"count", "body"}:
            raise Refusal("segmentation", "repeat requires count and instruction-index body")
        if type(r["count"]) is not int or not 0 <= r["count"] <= 4096:
            raise Refusal("segmentation", "repeat count must be in 0..4096")
        if not isinstance(r["body"], list):
            raise Refusal("segmentation", "repeat body must be a list")
        body = []
        for i in r["body"]:
            if type(i) is not int or not 0 <= i < len(program):
                raise Refusal("segmentation", "repeat instruction index out of range")
            body.append(lean_node(program[i]))
        return f"(.repeat {r['count']} {lean_list(body)})"
    raise Refusal("segmentation", "unknown segment form")


def render(task, translation, spec, proposal):
    extended = extended_model(task, translation, spec)
    namespace = "LarkNonlinear" if extended else "Lark"
    unit_ops = "⟨fun _ _ => (), fun _ _ => (), fun _ _ => (),\n  fun _ _ => (), fun _ _ => ()"
    if extended:
        unit_ops += (
            ", fun _ _ => (), fun _ => (), fun _ => (), fun _ => (), fun _ => (), fun _ => ()"
        )
    unit_ops += "⟩"
    proofs = proposal["proofs"]
    validate_proofs(proofs)
    if len(proposal["segments"]) > 4096:
        raise Refusal("segmentation", "too many segments")
    segments = lean_list(emit_segment(s, translation.program) for s in proposal["segments"])
    globals = lean_list(f"⟨.{b.role}, {b.size}⟩" for b in task.buffers)
    shared = lean_list(str(size) for _, size in translation.shared)
    # This is an untrusted footprint proposal. Both proof stages must establish
    # definitional equality with the trace of the actual Lean execution.
    try:
        trace = Machine(task, translation).run().trace
    except Refusal:
        trace = []
    trace_data = lean_list(
        f"⟨{a.thread}, ⟨.{a.location[0]}, {a.location[1]}, {a.location[2]}, {a.location[3]}⟩, "
        f"{'true' if a.write else 'false'}, ⟨{', '.join(map(str, a.epoch))}⟩⟩"
        for a in reversed(trace)
    )
    return (
        model_path(extended).read_text()
        + f"""

namespace LarkCertificate
open {namespace}
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def layout : Layout := ⟨{globals}, {shared}, []⟩
def geometry : Geometry := ⟨{task.grid}, {task.block}, {task.warp}⟩
def fuel : Fuel := ⟨{", ".join(map(str, task.fuel))}⟩
def program : List Instr := {lean_list(lean_node(i) for i in translation.program)}
def traceData : List Access := {trace_data}
def segments : List Segment := {segments}
def spec (ops : Ops α) (input : Nat → Nat → α) : List α :=
  {lean_list(lean_spec(s) for s in spec)}

def finalState (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) : State α :=
  (runLaunch ops layout geometry fuel program (initial layout input outside)).getD
    (initial layout input outside)

theorem segmentation_data : flatten segments = program :=
  {proofs["segmentation_data"]}

theorem segmentation (ops : Ops α) (s : State α) :
    runLaunch ops layout geometry fuel program s =
    runLaunch ops layout geometry fuel (flatten segments) s := by
  rw [segmentation_data]

def unitOps : Ops Unit := {unit_ops}

theorem race_free : ∃ final,
    runLaunch unitOps layout geometry fuel program
      (initial layout (fun _ _ => ()) (fun _ => some ())) = some final ∧
    raceFree geometry final.trace = true :=
  {proofs["race_free"]}

theorem segment_equivalence (ops : Ops α) :
    Correct ops layout geometry fuel (flatten segments) (spec ops) :=
  {proofs["segment_equivalence"]}

theorem kernel_eq_spec (ops : Ops α) :
    Correct ops layout geometry fuel program (spec ops) := by
  exact assemble ops layout geometry fuel program segments (spec ops)
    segmentation_data (segment_equivalence ops)

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


def run_lean(directory, binary, timeout):
    try:
        result = subprocess.run(
            [binary, "Main.lean"], cwd=directory, text=True, capture_output=True, timeout=timeout
        )
    except subprocess.TimeoutExpired as e:
        stdout = e.stdout.decode() if isinstance(e.stdout, bytes) else e.stdout or ""
        return False, stdout + "\nLean timed out; no certificate was issued.\n"
    log = result.stdout + result.stderr
    if result.returncode or "sorry" in log or "error:" in log:
        return False, log
    # Require every declaration and reject every nonstandard axiom.
    for name in (
        "segmentation_data",
        "segmentation",
        "race_free",
        "segment_equivalence",
        "kernel_eq_spec",
        "kernel_eq_spec_pre",
    ):
        tag = f"LarkCertificate.{name}"
        no_axioms = re.findall(
            "^" + re.escape(f"'{tag}' does not depend on any axioms") + r"\s*$", log, re.M
        )
        dependencies = re.findall(
            "^" + re.escape(f"'{tag}' depends on axioms:") + r"\s*\[([^]]*)\]", log, re.M
        )
        # A tactic's diagnostic output must not spoof the later #print audit.
        if len(no_axioms) + len(dependencies) != 1:
            return False, log + f"\nMissing or ambiguous axiom audit for {tag}\n"
        if no_axioms:
            continue
        names = {x.strip() for x in dependencies[0].split(",") if x.strip()}
        if not names <= AXIOMS:
            return False, log + f"\nForbidden axiom dependencies: {sorted(names - AXIOMS)}\n"
    return True, log


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False) + "\n")


def verify(
    kernel,
    reference,
    task_path,
    output,
    *,
    lean=None,
    timeout=120,
    provider=None,
    attempts=1,
    proposal_path=None,
):
    if not 1 <= attempts <= 20 or timeout <= 0:
        raise Refusal("configuration", "attempts must be 1..20 and timeout must be positive")
    # Existing directories are refused, preventing a failed run from leaving an old success report.
    if output.exists():
        raise Refusal("output", f"destination already exists: {output}")
    source_bytes, reference_bytes, task_bytes = (
        kernel.read_bytes(),
        reference.read_bytes(),
        task_path.read_bytes(),
    )
    task = Task.parse(task_bytes.decode("utf-8"))
    source = source_bytes.decode("utf-8")
    ref_source = reference_bytes.decode("utf-8")
    translation = translate(source, task)
    spec = read_spec(ref_source, task)
    machine = preflight(task, translation, spec)
    binary = lean_binary(lean)
    proposal = {"segments": default_segments(translation.program), "proofs": dict(DEFAULT_PROOFS)}
    if proposal_path:
        proposal = json.loads(proposal_path.read_text())
    output.mkdir(parents=True)
    (output / "kernel.cu").write_bytes(source_bytes)
    (output / "reference.py").write_bytes(reference_bytes)
    (output / "task.json").write_bytes(task_bytes)
    (output / "lean-toolchain").write_text(TOOLCHAIN)
    (output / "lakefile.toml").write_text(LAKEFILE)
    write_json(output / "translation.json", translation.data())
    history = []
    success = False
    for attempt in range(attempts):
        validate_proofs(proposal["proofs"])
        (output / "Main.lean").write_text(render(task, translation, spec, proposal))
        success, log = run_lean(output, binary, timeout)
        (output / f"lean-{attempt + 1}.log").write_text(log)
        history.append({"attempt": attempt + 1, "accepted": success})
        if success or not provider or attempt + 1 == attempts:
            break
        request = {
            "stage": "segmentation-and-equivalence",
            "task": asdict(task),
            "program": [i.data() for i in translation.program],
            "spec": [n.data() for n in spec],
            "proposal": proposal,
            "lean_source": (output / "Main.lean").read_text(),
            "lean_errors": log,
            "instruction": "Return JSON with segments and the three proof slots; statements are immutable.",
        }
        try:
            result = subprocess.run(
                provider,
                input=json.dumps(request),
                text=True,
                capture_output=True,
                timeout=timeout,
                check=True,
            )
            proposal = json.loads(result.stdout)
        except (subprocess.SubprocessError, json.JSONDecodeError) as e:
            history.append({"provider_error": str(e)})
            break
    write_json(output / "proposal.json", proposal)
    files = [
        "Main.lean",
        "kernel.cu",
        "reference.py",
        "task.json",
        "translation.json",
        "proposal.json",
        "lean-toolchain",
        "lakefile.toml",
    ]
    report = {
        "schema": 1,
        "status": "verified" if success else "unproved",
        "paper": "https://arxiv.org/abs/2611.02028",
        "implementation": "independent bounded scalar profile",
        "task": asdict(task),
        "trusted_assumptions": TRUST
        if not extended_model(task, translation, spec)
        else [
            *TRUST[:4],
            "Host launch, declared float16/float32 storage, aligned disjoint buffers; explicit half conversions",
            "Abstract div/exp/tanh/rsqrt/fromHalf/toHalf operations, not an IEEE implementation or error bound",
            TRUST[-1],
        ],
        "scope": SCOPE
        if not extended_model(task, translation, spec)
        else [
            SCOPE[0],
            "Float32 arithmetic with explicit float16 storage conversions; +, -, *, max, /, exp, tanh, rsqrt",
            *SCOPE[2:4],
            "Operation-to-hardware correspondence remains trusted; numerical samples are separate evidence",
            *SCOPE[5:],
        ],
        "source_readback": True,
        "model_sha256": digest(model_path(extended_model(task, translation, spec)).read_bytes()),
        "model_profile": "nonlinear-v2" if extended_model(task, translation, spec) else "scalar-v1",
        "files": {f: digest((output / f).read_bytes()) for f in files},
        "axiom_audit": log,
        "attempts": history,
        "accesses": len(machine.trace),
        "numerical_testing": "not performed; proof concerns exact operations",
        "recheck": "lake build (or lean Main.lean); lark check also validates source and artifact binding",
    }
    write_json(output / "report.json", report)
    return report


def check(directory, *, lean=None, timeout=120):
    report = json.loads((directory / "report.json").read_text())
    if report.get("model_profile") == "pointwise-induction-v3":
        from .pointwise import check as check_pointwise

        return check_pointwise(directory, lean=lean, timeout=timeout)
    if report.get("model_profile") == "gemv-induction-v4":
        from .gemv import check as check_gemv

        return check_gemv(directory, lean=lean, timeout=timeout)
    if report.get("model_profile") == "matrix-induction-v5":
        from .matrix import check as check_matrix

        return check_matrix(directory, lean=lean, timeout=timeout)
    if report.get("model_profile") == "linear-induction-v6":
        from .linear import check as check_linear

        return check_linear(directory, lean=lean, timeout=timeout)
    if report.get("model_profile") == "rotary-induction-v7":
        from .rotary import check as check_rotary

        return check_rotary(directory, lean=lean, timeout=timeout)
    if report.get("model_profile") == "normalization-induction-v9":
        from .normalization import check as check_normalization

        return check_normalization(directory, lean=lean, timeout=timeout)
    if report.get("model_profile") == "convolution-induction-v8":
        from .convolution import check as check_convolution

        return check_convolution(directory, lean=lean, timeout=timeout)
    required = {
        "Main.lean",
        "kernel.cu",
        "reference.py",
        "task.json",
        "translation.json",
        "proposal.json",
        "lean-toolchain",
        "lakefile.toml",
    }
    if set(report["files"]) != required:
        raise Refusal("integrity", "certificate manifest has an unexpected file set")
    for name, expected in report["files"].items():
        if digest((directory / name).read_bytes()) != expected:
            raise Refusal("integrity", f"file changed: {name}")
    if (directory / "lean-toolchain").read_text() != TOOLCHAIN or (
        directory / "lakefile.toml"
    ).read_text() != LAKEFILE:
        raise Refusal("integrity", "unexpected standalone project configuration")
    task = Task.read(directory / "task.json")
    tr = translate((directory / "kernel.cu").read_bytes().decode("utf-8"), task)
    spec = read_spec((directory / "reference.py").read_text(), task)
    if report["model_sha256"] != digest(model_path(extended_model(task, tr, spec)).read_bytes()):
        raise Refusal("integrity", "certificate was produced with a different model version")
    if json.loads((directory / "translation.json").read_text()) != json.loads(
        json.dumps(tr.data())
    ):
        raise Refusal("integrity", "translation data differs from source")
    proposal = json.loads((directory / "proposal.json").read_text())
    expected = render(task, tr, spec, proposal)
    if (directory / "Main.lean").read_text() != expected:
        raise Refusal(
            "integrity",
            "theorem source does not match the fixed statement generated from the artifacts",
        )
    ok, log = run_lean(directory, lean_binary(lean), timeout)
    if not ok:
        raise Refusal("proof", log)
    return log
