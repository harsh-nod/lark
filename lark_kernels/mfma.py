"""Opt-in full-wave64 MFMA with four half/float vector register components."""

from dataclasses import asdict
import json
from pathlib import Path
import shutil
import sysconfig

from . import certificate
from .frontend import Reader as ScalarReader, Translation
from .ir import Refusal, Task, lean_list, lean_node, lean_spec, literal, node
from .machine import Machine as ScalarMachine
from .spec import read_spec

PROFILE = "wave-mfma-v14"
BUILTIN = "__builtin_amdgcn_mfma_f32_16x16x16f16"

DEFAULT_PROOFS = {
    "segmentation_data": "by simp [LarkMFMA.flatten, LarkMFMA.flattenSegment, segments, program]",
    "race_free": (
        "by\n  have hp : program = LarkMFMA.Tile.program := by decide\n"
        "  obtain ⟨final, hr, hrf, hout⟩ := (LarkMFMA.Tile.correct unitOps) "
        "(fun _ _ => ()) (fun _ => some ())\n  refine ⟨final, ?_, hrf⟩\n"
        "  simpa only [hp] using hr"
    ),
    "segment_equivalence": (
        "by\n  rewrite [segmentation_data]\n"
        "  have hp : program = LarkMFMA.Tile.program := by decide\n"
        "  have hs : spec ops = LarkMFMA.Tile.spec ops := by rfl\n"
        "  rewrite [hp, hs]\n  exact LarkMFMA.Tile.correct ops"
    ),
}

FILES = {
    "Main.lean",
    "kernel.hip",
    "reference.py",
    "task.json",
    "translation.json",
    "proposal.json",
    "lean-toolchain",
    "lakefile.toml",
}


def task_profile(task):
    if task.language != "hip" or task.warp != 64 or task.block % 64:
        raise Refusal("mfma-geometry", "HIP full-wave64 blocks are required")


class Reader(ScalarReader):
    def __init__(self, source, task):
        super().__init__(source, task)
        self.reg_types = {}

    def name(self):
        value = super().name()
        if value in {"H4", "F4", "_Float16", BUILTIN, "using", "__attribute__", "ext_vector_type"}:
            raise Refusal("mfma-name", "MFMA type and builtin names are reserved")
        return value

    def scalar_type(self, value):
        if value.op == "reg":
            return self.reg_types.get(value.args[0], "float32")
        return super().scalar_type(value)

    def expr(self, mode, precedence=0):
        name = self.peek()
        if (
            mode != "scalar"
            or name not in self.symbols
            or not self.symbols[name][0].startswith("vector-")
        ):
            return super().expr(mode, precedence)
        self.pop()
        _, base, _ = self.symbols[name]
        self.pop("[")
        element = self.pop()
        if element not in {"0", "1", "2", "3"}:
            raise Refusal("mfma-component", "vector component must be a literal in 0..3")
        self.pop("]")
        value = node("reg", base + int(element))
        levels = {"+": 10, "-": 10, "*": 20, "/": 20, "%": 20}
        while self.peek() in levels and levels[self.peek()] > precedence:
            op = self.pop()
            if op == "%":
                raise Refusal("operation", "scalar remainder is not implemented")
            right = self.expr(mode, levels[op])
            value = node("bin", {"+": "add", "-": "sub", "*": "mul", "/": "div"}[op], value, right)
        return value

    def operation(self, dest):
        self.pop(BUILTIN)
        self.pop("(")
        args = []
        for i, expected in enumerate(("vector-float16", "vector-float16", "vector-float32")):
            if i:
                self.pop(",")
            name = self.pop()
            if name not in self.symbols or self.symbols[name][0] != expected:
                raise Refusal("mfma-type", "MFMA requires H4, H4 and F4 operand registers")
            args.append(self.symbols[name][1])
        for _ in range(3):
            self.pop(",")
            if self.pop() != "0":
                raise Refusal("mfma-modifier", "only literal modifiers (0,0,0) are supported")
        self.pop(")")
        self.pop(";")
        self.code.append(node("mfma", dest, *args))

    def statement(self):
        offset = 1 if self.peek() == "const" else 0
        upcoming = [t.text for t in self.tokens[self.i : self.i + 3]]
        if len(upcoming) > offset and upcoming[offset] in {"H4", "F4"}:
            constant = self.accept("const")
            dtype = "float16" if self.pop() == "H4" else "float32"
            name = self.name()
            base = self.nreg
            self.nreg += 4
            self.declare(name, "vector-" + dtype, base, constant)
            for r in range(base, base + 4):
                self.reg_types[r] = dtype
            if not self.accept("="):
                if constant:
                    raise Refusal("mfma-type", "const vectors need an initializer")
                self.pop(";")
            elif self.peek() == BUILTIN:
                if dtype != "float32":
                    raise Refusal("mfma-type", "MFMA destination must be F4")
                self.operation(base)
            else:
                self.pop("{")
                for e in range(4):
                    if e:
                        self.pop(",")
                    value = self.expr("scalar")
                    if self.scalar_type(value) != dtype:
                        raise Refusal("mfma-type", "vector initializer component dtype differs")
                    self.code.append(node("set", base + e, value))
                self.pop("}")
                self.pop(";")
        elif self.peek() in self.symbols and self.symbols[self.peek()][0].startswith("vector-"):
            kind, base, constant = self.symbols[self.pop()]
            if constant or kind != "vector-float32":
                raise Refusal("mfma-type", "MFMA assignment requires a mutable F4 destination")
            self.pop("=")
            self.operation(base)
        else:
            super().statement()

    def read(self):
        for name, dtype in (("H4", "_Float16"), ("F4", "float")):
            for token in (
                "using",
                name,
                "=",
                dtype,
                "__attribute__",
                "(",
                "(",
                "ext_vector_type",
                "(",
                "4",
                ")",
                ")",
                ")",
                ";",
            ):
                self.pop(token)
        if self.accept("extern"):
            self.pop('"C"')
        self.pop("__global__")
        self.pop("void")
        entry = self.name()
        if entry != self.task.entry:
            raise Refusal("entry", "kernel entry differs from task")
        self.pop("(")
        for i, buf in enumerate(self.task.buffers):
            if i:
                self.pop(",")
            constant = self.accept("const")
            self.pop("_Float16" if buf.dtype == "float16" else "float")
            self.pop("*")
            name = self.name()
            if name != buf.name:
                raise Refusal("signature", "buffer argument differs from task")
            self.declare(name, "global", i, constant)
        self.pop(")")
        self.body()
        if self.peek() != "<eof>":
            raise Refusal("syntax", "exactly one kernel and no trailing declarations required")
        self.code.append(node("halt"))
        for instruction in self.code:
            if instruction.op == "set":
                expected, value = (
                    self.reg_types.get(instruction.args[0], "float32"),
                    instruction.args[1],
                )
            elif instruction.op == "store":
                space, buffer, _, value = instruction.args
                expected = self.task.buffers[buffer].dtype if space == "global" else "float32"
            else:
                continue
            if self.scalar_type(value) != expected:
                raise Refusal("type", "assignment component dtype differs")
        return Translation(entry, self.tokens, self.trailing, self.code, self.shared)


def translate(source, task):
    task_profile(task)
    result = Reader(source, task).read()
    if result.readback() != source:
        raise Refusal("readback", "MFMA source does not reconstruct byte for byte")
    return result


class Machine(ScalarMachine):
    def cut(self, t):
        pc = self.threads[t].pc
        if 0 <= pc < len(self.translation.program) and self.translation.program[pc].op == "mfma":
            return "matrix"
        return super().cut(t)

    def matrix(self, ts):
        if self.task.warp != 64 or self.task.block % 64 or len(ts) != 64:
            raise Refusal("mfma-geometry", "partial waves are unsupported")
        dest, a, b, c = self.translation.program[self.threads[ts[0]].pc].args
        values = []
        for t in ts:
            lane = t % self.task.block % 64
            owner = t // self.task.block * self.task.block + (t % self.task.block // 64) * 64
            for e in range(4):
                row, col = 4 * (lane // 16) + e, lane % 16
                dot = literal(0)
                for k in range(16):
                    al, bl = owner + row + 16 * (k // 4), owner + col + 16 * (k // 4)
                    if (
                        al not in ts
                        or bl not in ts
                        or a + k % 4 not in self.threads[al].regs
                        or b + k % 4 not in self.threads[bl].regs
                    ):
                        raise Refusal(
                            "mfma-uninitialized", "matrix operand lane/register is unavailable"
                        )
                    av, bv = self.threads[al].regs[a + k % 4], self.threads[bl].regs[b + k % 4]
                    dot = node(
                        "bin",
                        "add",
                        dot,
                        node("bin", "mul", node("un", "fromHalf", av), node("un", "fromHalf", bv)),
                    )
                if c + e not in self.threads[t].regs:
                    raise Refusal("mfma-uninitialized", "accumulator register is unavailable")
                values.append((t, dest + e, node("bin", "add", dot, self.threads[t].regs[c + e])))
        for t, r, value in values:
            self.threads[t].regs[r] = value
        for t in ts:
            self.threads[t].pc += 1

    def warp(self, ts):
        for _ in range(self.task.fuel[1]):
            for t in ts:
                self.lane(t)
            cut = self.converged(ts)
            if cut == "matrix":
                self.matrix(ts)
            elif cut == "warp":
                self.resume(ts, cut)
            else:
                return
        raise Refusal("fuel", "warp fuel exhausted")


def preflight(task, tr, spec):
    machine = Machine(task, tr).run()
    if machine.race():
        raise Refusal("race", "unordered memory accesses conflict")
    if machine.outputs() != spec:
        raise Refusal("equivalence", "MFMA output differs from the independent tensor reference")
    return machine


def library(name="MFMA.lean"):
    path = Path(__file__).resolve().parents[1] / "lean/Lark" / name
    if not path.exists():
        path = Path(sysconfig.get_path("data")) / "share/lark/lean/Lark" / name
    if not path.exists():
        raise Refusal("installation", "pinned MFMA machine is missing")
    return path


def emit(instruction):
    if instruction.op == "mfma":
        dest, a, b, c = instruction.args
        return f"(.mfma {dest} {a} {b} {c})"
    return f"(.scalar {lean_node(instruction)})"


def segment(data, program, depth=0):
    if depth > 16 or not isinstance(data, dict) or len(data) != 1:
        raise Refusal("segmentation", "invalid segment tree")
    if "op" in data:
        i = data["op"]
        if type(i) is not int or not 0 <= i < len(program):
            raise Refusal("segmentation", "instruction index out of range")
        return f"(.op {emit(program[i])})"
    if "seq" in data and isinstance(data["seq"], list):
        return f"(.seq {lean_list(segment(s, program, depth + 1) for s in data['seq'])})"
    if "repeat" in data:
        r = data["repeat"]
        if (
            not isinstance(r, dict)
            or set(r) != {"count", "body"}
            or type(r["count"]) is not int
            or not 0 <= r["count"] <= 4096
            or not isinstance(r["body"], list)
        ):
            raise Refusal("segmentation", "invalid repetition")
        if any(type(i) is not int or not 0 <= i < len(program) for i in r["body"]):
            raise Refusal("segmentation", "repeated instruction index out of range")
        return f"(.repeat {r['count']} {lean_list(emit(program[i]) for i in r['body'])})"
    raise Refusal("segmentation", "unknown segment form")


def render(task, tr, spec, proposal):
    certificate.validate_proofs(proposal["proofs"])
    if not isinstance(proposal["segments"], list) or len(proposal["segments"]) > 4096:
        raise Refusal("segmentation", "bounded segment list required")
    try:
        trace = Machine(task, tr).run().trace
    except Refusal:
        trace = []
    trace_data = lean_list(
        f"⟨{a.thread}, ⟨.{a.location[0]}, {a.location[1]}, {a.location[2]}, {a.location[3]}⟩, {'true' if a.write else 'false'}, ⟨{', '.join(map(str, a.epoch))}⟩⟩"
        for a in reversed(trace)
    )
    proofs = proposal["proofs"]
    base = certificate.model_path(True).read_text()
    extension = library().read_text().replace("import Lark.Nonlinear\n", "", 1)
    transfer = library("MFMATile.lean").read_text().replace("import Lark.MFMA\n", "", 1)
    # Preserve every reference expression, but elaborate each cell separately.
    # A single expanded 256-cell declaration causes excessive Lean elaboration.
    reference_cells = "\n".join(
        f"noncomputable def referenceCell_{i} (ops : Ops α) (input : Nat → Nat → α) : α :=\n  {lean_spec(value)}\n"
        for i, value in enumerate(spec)
    )
    reference_list = lean_list(f"referenceCell_{i} ops input" for i in range(len(spec)))
    ops = "⟨" + ", ".join(["fun _ _ => ()"] * 6 + ["fun _ => ()"] * 5) + "⟩"
    return (
        base
        + "\n"
        + extension
        + "\n"
        + transfer
        + f"""

namespace LarkCertificate
open LarkNonlinear
abbrev Instr := LarkMFMA.Instr
abbrev Segment := LarkMFMA.Segment
abbrev flatten := LarkMFMA.flatten
abbrev flattenSegment := LarkMFMA.flattenSegment
abbrev runLaunch (ops : Ops α) := LarkMFMA.runLaunch ops
abbrev Correct (ops : Ops α) := LarkMFMA.Correct ops
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000

def layout : Layout := ⟨{lean_list(f"⟨.{b.role}, {b.size}⟩" for b in task.buffers)}, {lean_list(str(n) for _, n in tr.shared)}, []⟩
def geometry : Geometry := ⟨{task.grid}, {task.block}, {task.warp}⟩
def fuel : Fuel := ⟨{", ".join(map(str, task.fuel))}⟩
def program : List Instr := {lean_list(emit(i) for i in tr.program)}
def traceData : List Access := {trace_data}
def segments : List Segment := {lean_list(segment(s, tr.program) for s in proposal["segments"])}
{reference_cells}
noncomputable def spec (ops : Ops α) (input : Nat → Nat → α) : List α :=
  {reference_list}
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
def unitOps : Ops Unit := {ops}
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
  exact LarkMFMA.assemble ops layout geometry fuel program segments (spec ops)
    segmentation_data (segment_equivalence ops)
theorem kernel_eq_spec_pre (ops : Ops α) (input : Nat → Nat → α) (s : State α)
    (pre : StdPre layout input s) :
    ∃ final, runLaunch ops layout geometry fuel program s = some final ∧
      raceFree geometry final.trace = true ∧ extract layout final = some (spec ops input) := by
  exact LarkMFMA.correct_from_pre ops layout geometry fuel program (spec ops)
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


def verify(kernel, reference, task_path, output, *, lean=None, timeout=300, proposal_path=None):
    if timeout <= 0:
        raise Refusal("configuration", "positive Lean timeout required")
    if output.exists():
        raise Refusal("output", "fresh output directory required")
    task = Task.read(task_path)
    source, ref = kernel.read_bytes().decode("utf-8"), reference.read_text()
    tr, spec = translate(source, task), read_spec(ref, task)
    machine = preflight(task, tr, spec)
    proposal = (
        json.loads(proposal_path.read_text())
        if proposal_path
        else {
            "segments": certificate.default_segments(tr.program),
            "proofs": dict(DEFAULT_PROOFS),
        }
    )
    statement = render(task, tr, spec, proposal)
    output.mkdir(parents=True)
    for name, path in [
        ("kernel.hip", kernel),
        ("reference.py", reference),
        ("task.json", task_path),
    ]:
        shutil.copyfile(path, output / name)
    (output / "Main.lean").write_text(statement)
    (output / "lean-toolchain").write_text(certificate.TOOLCHAIN)
    (output / "lakefile.toml").write_text(certificate.LAKEFILE)
    certificate.write_json(output / "translation.json", tr.data())
    certificate.write_json(output / "proposal.json", proposal)
    accepted, log = certificate.run_lean(output, certificate.lean_binary(lean), timeout)
    (output / "lean-1.log").write_text(log)
    report = {
        "schema": 1,
        "model_profile": PROFILE,
        "status": "verified" if accepted else "unproved",
        "task": asdict(task),
        "models": {
            "nonlinear": certificate.digest(certificate.model_path(True).read_bytes()),
            "mfma": certificate.digest(library().read_bytes()),
            "tile": certificate.digest(library("MFMATile.lean").read_bytes()),
        },
        "files": {n: certificate.digest((output / n).read_bytes()) for n in sorted(FILES)},
        "axiom_audit": log,
        "accesses": len(machine.trace),
        "source_readback": True,
        "trusted_assumptions": [
            certificate.TRUST[0],
            "The pinned nonlinear scalar and full-wave64 MFMA machine definitions",
            "The opt-in HIP reader, four-component half/float vector lowering and lossless token readback",
            "The independent PyTorch AST formalization",
            "Declared aligned disjoint buffers and matching full-wave64 host geometry",
            "MFMA f32_16x16x16f16 with literal modifiers (0,0,0), logical operand layout and exact dot-plus-C correspondence",
            "Abstract scalar/half-conversion operations, not IEEE rounding or hardware accumulation-order semantics",
            certificate.TRUST[-1],
        ],
        "scope": "Independent full-wave64 HIP MFMA profile. The automatic theorem covers one 16x16 half-input/float-output tile, all input/outside values, actual launch completion and race freedom. Matrix operands are read from a register snapshot; no memory fence is added. Operation correspondence, source lowering and host contracts remain trusted. No partial masks, other shapes/modifiers, IEEE guarantee, original production kernel or model pass-rate claim.",
    }
    certificate.write_json(output / "report.json", report)
    return report


def check(directory, *, lean=None, timeout=300):
    report = json.loads((directory / "report.json").read_text())
    if report.get("model_profile") != PROFILE or set(report["files"]) != FILES:
        raise Refusal("integrity", "unexpected MFMA certificate profile/files")
    for name, expected in report["files"].items():
        if certificate.digest((directory / name).read_bytes()) != expected:
            raise Refusal("integrity", "file changed: " + name)
    if (directory / "lean-toolchain").read_text() != certificate.TOOLCHAIN or (
        directory / "lakefile.toml"
    ).read_text() != certificate.LAKEFILE:
        raise Refusal("integrity", "standalone project configuration changed")
    models = {
        "nonlinear": certificate.digest(certificate.model_path(True).read_bytes()),
        "mfma": certificate.digest(library().read_bytes()),
        "tile": certificate.digest(library("MFMATile.lean").read_bytes()),
    }
    if report["models"] != models:
        raise Refusal("integrity", "pinned MFMA machine differs")
    task = Task.read(directory / "task.json")
    tr = translate((directory / "kernel.hip").read_bytes().decode("utf-8"), task)
    spec = read_spec((directory / "reference.py").read_text(), task)
    proposal = json.loads((directory / "proposal.json").read_text())
    if json.loads((directory / "translation.json").read_text()) != json.loads(
        json.dumps(tr.data())
    ) or (directory / "Main.lean").read_text() != render(task, tr, spec, proposal):
        raise Refusal("integrity", "source-bound MFMA statement differs")
    accepted, log = certificate.run_lean(directory, certificate.lean_binary(lean), timeout)
    if not accepted:
        raise Refusal("proof", log)
    return log
