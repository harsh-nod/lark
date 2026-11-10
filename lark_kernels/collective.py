"""Opt-in full-wave64 HIP shuffles with snapshot register semantics."""

from dataclasses import asdict
import json
from pathlib import Path
import shutil
import sysconfig

from . import certificate
from .frontend import Reader as ScalarReader
from .ir import Refusal, Task, lean_list, lean_node, lean_spec, node
from .machine import Machine as ScalarMachine
from .spec import read_spec

PROFILE = "wave-shuffle-v13"
SHUFFLES = {"__shfl": "index", "__shfl_xor": "xor", "__shfl_up": "up", "__shfl_down": "down"}
WIDTHS = {1, 2, 4, 8, 16, 32, 64}
DEFAULT_PROOFS = {
    **certificate.DEFAULT_PROOFS,
    "segmentation_data": "by simp [LarkCollective.flatten, LarkCollective.flattenSegment, segments, program]",
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
        raise Refusal("shuffle-geometry", "HIP full-wave64 blocks are required")
    if any(b.dtype != "float32" for b in task.buffers):
        raise Refusal("shuffle-type", "this profile requires float32 buffers")


class Reader(ScalarReader):
    def name(self):
        value = super().name()
        if value in SHUFFLES:
            raise Refusal("shuffle-name", "shuffle builtin names are reserved")
        return value

    def shuffle(self, dest):
        kind = SHUFFLES[self.pop()]
        self.pop("(")
        source = self.pop()
        if source not in self.symbols or self.symbols[source][0] != "scalar":
            raise Refusal("shuffle-type", "shuffle source must be a float register")
        src = self.symbols[source][1]
        self.pop(",")
        selector = self.expr("index")
        self.pop(",")
        width = self.pop()
        if not width.isdecimal() or int(width) not in WIDTHS:
            raise Refusal("shuffle-width", "explicit literal width must be a power of two in 1..64")
        self.pop(")")
        self.pop(";")
        self.code.append(node("shuffle", kind, dest, src, selector, int(width)))

    def statement(self):
        remaining = [t.text for t in self.tokens[self.i : self.i + 6]]
        offset = 1 if remaining and remaining[0] == "const" else 0
        if (
            len(remaining) >= offset + 4
            and remaining[offset] == "float"
            and remaining[offset + 2] == "="
            and remaining[offset + 3] in SHUFFLES
        ):
            constant = self.accept("const")
            self.pop("float")
            name = self.name()
            dest = self.nreg
            self.nreg += 1
            self.declare(name, "scalar", dest, constant)
            self.pop("=")
            self.shuffle(dest)
        elif (
            len(remaining) >= 3
            and remaining[0] in self.symbols
            and remaining[1] == "="
            and remaining[2] in SHUFFLES
        ):
            kind, dest, constant = self.symbols[self.pop()]
            if kind != "scalar" or constant:
                raise Refusal(
                    "shuffle-type", "shuffle destination must be a mutable float register"
                )
            self.pop("=")
            self.shuffle(dest)
        else:
            super().statement()


def translate(source, task):
    task_profile(task)
    result = Reader(source, task).read()
    if result.readback() != source:
        raise Refusal("readback", "shuffle source does not reconstruct byte for byte")
    return result


def source_lane(kind, width, lane, argument):
    if width not in WIDTHS or not 0 <= lane < 64 or argument < 0:
        raise Refusal("shuffle-domain", "invalid lane, width or selector")
    position, base = lane % width, lane // width * width
    if kind in {"index", "xor"}:
        if argument >= width:
            raise Refusal("shuffle-domain", "index/xor argument must be smaller than width")
        selected = base + (argument if kind == "index" else position ^ argument)
    elif kind in {"up", "down"}:
        if argument > width:
            raise Refusal("shuffle-domain", "up/down argument must not exceed width")
        selected = (
            lane - argument
            if kind == "up" and argument <= position
            else lane + argument
            if kind == "down" and position + argument < width
            else lane
        )
    else:
        raise Refusal("shuffle-domain", "unknown shuffle form")
    if not 0 <= selected < 64 or selected // width != lane // width:
        raise Refusal("shuffle-domain", "shuffle left its declared subgroup")
    return selected


class Machine(ScalarMachine):
    def cut(self, t):
        pc = self.threads[t].pc
        if 0 <= pc < len(self.translation.program) and self.translation.program[pc].op == "shuffle":
            return "shuffle"
        return super().cut(t)

    def shuffle(self, ts):
        if self.task.warp != 64 or self.task.block % 64 or len(ts) != 64:
            raise Refusal("shuffle-geometry", "partial waves are unsupported")
        kind, dest, src, selector, width = self.translation.program[self.threads[ts[0]].pc].args
        values = []
        # Complete every read from the old register state before any write.
        for t in ts:
            selected = source_lane(kind, width, t % self.task.block % 64, self.ix(t, selector))
            owner = t // self.task.block * self.task.block + (t % self.task.block // 64) * 64
            source = owner + selected
            if source not in ts or src not in self.threads[source].regs:
                raise Refusal(
                    "shuffle-uninitialized", "shuffle source lane/register is unavailable"
                )
            values.append((t, self.threads[source].regs[src]))
        for t, value in values:
            self.threads[t].regs[dest] = value
            self.threads[t].pc += 1
        # No memory fence, epoch increment or memory access is introduced.

    def warp(self, ts):
        for _ in range(self.task.fuel[1]):
            for t in ts:
                self.lane(t)
            cut = self.converged(ts)
            if cut == "shuffle":
                self.shuffle(ts)
            elif cut == "warp":
                self.resume(ts, cut)
            else:
                return
        raise Refusal("fuel", "warp fuel exhausted")


def preflight(task, tr, spec):
    machine = Machine(task, tr).run()
    if machine.race():
        raise Refusal("race", f"unordered accesses conflict: {machine.race()}")
    if machine.outputs() != spec:
        raise Refusal("equivalence", "shuffle output differs from the independent reference")
    return machine


def default_proofs(task, tr, spec, trace):
    result = dict(DEFAULT_PROOFS)
    if (
        task.grid == 1
        and task.block == 64
        and task.fuel == (32, 8, 8, 8)
        and [(b.role, b.size) for b in task.buffers] == [("input", 64), ("output", 64)]
        and len(tr.program) == 5
        and tr.program[0] == node("idx", 0, node("tid"))
        and tr.program[1] == node("set", 0, node("load", "global", 0, node("ivar", 0)))
        and tr.program[2].op == "shuffle"
        and tr.program[4] == node("halt")
        and len(spec) == 64
        and all(s.op == "input" and s.args[0] == 0 and 0 <= s.args[1] < 64 for s in spec)
    ):
        kind, dest, src, selector, width = tr.program[2].args
        if src == 0 and tr.program[3] == node(
            "store", "global", 1, node("ivar", 0), node("reg", dest)
        ):
            values = lean_list(str(s.args[1]) for s in spec)
            chosen = f"(fun t => (({values} : List Nat)[t]?).getD 0)"
            arguments = (
                f".{kind} {dest} {lean_node(selector)} {width} {chosen} "
                "(by unfold LarkCollective.Transfer.Valid; decide)"
            )
            result["race_free"] = (
                "by\n  obtain ⟨final, hr, hrf, hout⟩ :=\n    "
                f"(LarkCollective.Transfer.correct unitOps {arguments}) "
                "(fun _ _ => ()) (fun _ => some ())\n  exact ⟨final, hr, hrf⟩"
            )
            result["segment_equivalence"] = (
                "by\n  rw [segmentation_data]\n  exact "
                f"LarkCollective.Transfer.correct ops {arguments}"
            )
            return result
    if all(a.location[3] == a.thread for a in trace):
        proof = "exact LarkCollective.owned_raceFree geometry traceData (by simp [LarkCollective.Owned, traceData])"
        for name in ("race_free", "segment_equivalence"):
            result[name] = result[name].replace("\n  decide", "\n  " + proof)
    return result


def library(name="Collective.lean"):
    path = Path(__file__).resolve().parents[1] / "lean/Lark" / name
    if not path.exists():
        path = Path(sysconfig.get_path("data")) / "share/lark/lean/Lark" / name
    if not path.exists():
        raise Refusal("installation", "pinned collective machine is missing")
    return path


def emit(instruction):
    if instruction.op == "shuffle":
        kind, dest, src, selector, width = instruction.args
        return f"(.shuffle .{kind} {dest} {src} {lean_node(selector)} {width})"
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
    transfer = (
        library("ShuffleTransfer.lean").read_text().replace("import Lark.Collective\n", "", 1)
    )
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
abbrev Instr := LarkCollective.Instr
abbrev Segment := LarkCollective.Segment
abbrev flatten := LarkCollective.flatten
abbrev flattenSegment := LarkCollective.flattenSegment
abbrev runLaunch (ops : Ops α) := LarkCollective.runLaunch ops
abbrev Correct (ops : Ops α) := LarkCollective.Correct ops
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000

def layout : Layout := ⟨{lean_list(f"⟨.{b.role}, {b.size}⟩" for b in task.buffers)}, {lean_list(str(n) for _, n in tr.shared)}, []⟩
def geometry : Geometry := ⟨{task.grid}, {task.block}, {task.warp}⟩
def fuel : Fuel := ⟨{", ".join(map(str, task.fuel))}⟩
def program : List Instr := {lean_list(emit(i) for i in tr.program)}
def traceData : List Access := {trace_data}
def segments : List Segment := {lean_list(segment(s, tr.program) for s in proposal["segments"])}
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
  exact LarkCollective.assemble ops layout geometry fuel program segments (spec ops)
    segmentation_data (segment_equivalence ops)
theorem kernel_eq_spec_pre (ops : Ops α) (input : Nat → Nat → α) (s : State α)
    (pre : StdPre layout input s) :
    ∃ final, runLaunch ops layout geometry fuel program s = some final ∧
      raceFree geometry final.trace = true ∧ extract layout final = some (spec ops input) := by
  exact LarkCollective.correct_from_pre ops layout geometry fuel program (spec ops)
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
            "proofs": default_proofs(task, tr, spec, machine.trace),
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
            "collective": certificate.digest(library().read_bytes()),
            "transfer": certificate.digest(library("ShuffleTransfer.lean").read_bytes()),
        },
        "files": {n: certificate.digest((output / n).read_bytes()) for n in sorted(FILES)},
        "axiom_audit": log,
        "accesses": len(machine.trace),
        "source_readback": True,
        "trusted_assumptions": [
            *certificate.TRUST[:2],
            "The opt-in HIP reader and scalar/shuffle lowering, with lossless token readback",
            "The independent PyTorch AST formalization",
            "Declared aligned disjoint float32 buffers, matching full-wave64 host geometry and subgroup widths",
            "The inherited abstract scalar operations; no IEEE numerical-error guarantee",
            certificate.TRUST[-1],
            "HIP shuffle-to-snapshot-register correspondence; finite hardware evidence is separate",
        ],
        "scope": "Independent bounded full-wave64 float32 HIP shuffle profile; snapshot register transport, all input/outside values, inherited scalar operations, no memory fence from a shuffle. No partial masks, tensor cores or original production-kernel claim. Operation correspondence and source lowering remain trusted; hardware checks are separate.",
    }
    certificate.write_json(output / "report.json", report)
    return report


def check(directory, *, lean=None, timeout=300):
    report = json.loads((directory / "report.json").read_text())
    if report.get("model_profile") != PROFILE or set(report["files"]) != FILES:
        raise Refusal("integrity", "unexpected collective certificate profile/files")
    for name, expected in report["files"].items():
        if certificate.digest((directory / name).read_bytes()) != expected:
            raise Refusal("integrity", "file changed: " + name)
    if (directory / "lean-toolchain").read_text() != certificate.TOOLCHAIN or (
        directory / "lakefile.toml"
    ).read_text() != certificate.LAKEFILE:
        raise Refusal("integrity", "standalone project configuration changed")
    models = {
        "nonlinear": certificate.digest(certificate.model_path(True).read_bytes()),
        "collective": certificate.digest(library().read_bytes()),
        "transfer": certificate.digest(library("ShuffleTransfer.lean").read_bytes()),
    }
    if report["models"] != models:
        raise Refusal("integrity", "pinned collective machine differs")
    task = Task.read(directory / "task.json")
    tr = translate((directory / "kernel.hip").read_bytes().decode("utf-8"), task)
    spec = read_spec((directory / "reference.py").read_text(), task)
    proposal = json.loads((directory / "proposal.json").read_text())
    if json.loads((directory / "translation.json").read_text()) != json.loads(
        json.dumps(tr.data())
    ) or (directory / "Main.lean").read_text() != render(task, tr, spec, proposal):
        raise Refusal("integrity", "source-bound collective statement differs")
    accepted, log = certificate.run_lean(directory, certificate.lean_binary(lean), timeout)
    if not accepted:
        raise Refusal("proof", log)
    return log
