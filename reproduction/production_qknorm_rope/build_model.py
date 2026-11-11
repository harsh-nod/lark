"""Emit the explicit independent native fused Q/K program declaration."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from lark_kernels import collective, native_qknorm_rope as native

HERE = Path(__file__).resolve().parent


def main():
    programs = {}
    for layout in native.LAYOUTS:
        case = HERE / "cases" / layout
        contract = native.parse_task((case / "task.json").read_text())
        tr = native.translate((case / "kernel.hip").read_text(), contract)
        programs[layout] = "[\n" + ",\n".join(collective.emit(i) for i in tr.program) + "\n]"
    text = '''import Lark.PartitionCollective

/-! Closed native out-of-place Q32/K8/V8 fused RMSNorm + RoPE interface.
These are full source programs; complete execution/reference proofs are separate. -/
namespace LarkNativeQKNormRope
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

structure Shape where
  rows : Nat
  positive : 0 < rows
  bound : rows < 65536

def layout (p : Shape) : Layout :=
  ⟨[⟨.output, p.rows * 5120⟩, ⟨.input, p.rows * 6144⟩,
    ⟨.input, 128⟩, ⟨.input, 128⟩, ⟨.input, p.rows * 128⟩], [], []⟩
def geometry (p : Shape) : Geometry := ⟨p.rows * 5, 256, 64⟩
def fuel : Fuel := ⟨256, 16, 1, 1⟩

def program (neox : Bool) : List LarkCollective.Instr :=
  if neox then SPLIT_PROGRAM else INTERLEAVED_PROGRAM

def isShuffle : LarkCollective.Instr → Bool
  | .shuffle .. => true
  | _ => false
def isWarpBarrier : LarkCollective.Instr → Bool
  | .scalar (.barrier .warp) => true
  | _ => false

theorem program_length (neox : Bool) : (program neox).length = if neox then 107 else 88 := by
  cases neox <;> decide
theorem program_shuffles (neox : Bool) : ((program neox).filter isShuffle).length = if neox then 9 else 5 := by
  cases neox <;> decide
theorem program_warp_barriers (neox : Bool) : ((program neox).filter isWarpBarrier).length = if neox then 2 else 0 := by
  cases neox <;> decide
theorem program_halt (neox : Bool) : (program neox).getLast? = some (.scalar .halt) := by
  cases neox <;> decide
theorem native_threads (p : Shape) : (geometry p).grid * (geometry p).block = p.rows * 1280 := by
  simp [geometry, Nat.mul_assoc]
theorem native_complete_waves (p : Shape) :
    (geometry p).block % (geometry p).warp = 0 ∧ (geometry p).block / (geometry p).warp = 4 := by
  change (256 : Nat) % 64 = 0 ∧ (256 : Nat) / 64 = 4
  decide
theorem output_size (p : Shape) : (layout p).global[0]? = some ⟨.output, p.rows * 5120⟩ := rfl

#print axioms program_length
#print axioms program_shuffles
#print axioms program_warp_barriers
#print axioms program_halt
#print axioms native_threads
#print axioms native_complete_waves
#print axioms output_size
end LarkNativeQKNormRope
'''
    text = text.replace("SPLIT_PROGRAM", programs["split-half"]).replace("INTERLEAVED_PROGRAM", programs["interleaved"])
    (ROOT / "lean/Lark/NativeQKNormRopeProgram.lean").write_text(text)


if __name__ == "__main__":
    main()
