import Lark.PtxBatched

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/- Single-instruction initialization witnesses keep intermediate machine states
opaque. Their Steps proofs execute the original program; no loop or instruction
summary is assumed. This module is under development, not a kernel certificate. -/
namespace LarkPtxBatched.Bmm.Init
open LarkNonlinear LarkPtxPointwise
open LarkPtxDot (Machine setPointer setIndex32 setFloat unsigned32)
open LarkPtxMatrix (Steps setIndex64)

structure Frame (t : Nat) (base : State α) (s : Machine α) : Prop where
  active : s.registers.stopped = false
  memory : s.registers.base = base
  index : s.registers.i32 1 = some (t : Int)
  batch : s.registers.i32 8 = some ((t/32768 : Nat) : Int)
  batchA : s.registers.i32 9 = some ((t/32768*16384 : Nat) : Int)
  lane : s.registers.i32 11 = some (t : Int)
  row : s.registers.i32 12 = some ((t/512 : Nat) : Int)
  a : s.registers.pointer 17 = some ⟨0, 0, true⟩
  b : s.registers.pointer 18 = some ⟨1, 0, true⟩
  out : s.registers.pointer 9 = some ⟨2, 0, false⟩

theorem prefix_frame (t : Nat) (base : State α) : Frame t base (globalRow t base) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem frame32 (t : Nat) (base : State α) (s : Machine α) (d : Nat) (v : Int)
    (h : Frame t base s) (hd : d ≠ 1 ∧ d ≠ 8 ∧ d ≠ 9 ∧ d ≠ 11 ∧ d ≠ 12) :
    Frame t base (setIndex32 s d v) := by
  rcases hd with ⟨h1, h8, h9, h11, h12⟩
  refine ⟨h.active, h.memory, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [LarkPtxDot.setIndex32_i32, if_neg (Ne.symm h1)] using h.index
  · simpa only [LarkPtxDot.setIndex32_i32, if_neg (Ne.symm h8)] using h.batch
  · simpa only [LarkPtxDot.setIndex32_i32, if_neg (Ne.symm h9)] using h.batchA
  · simpa only [LarkPtxDot.setIndex32_i32, if_neg (Ne.symm h11)] using h.lane
  · simpa only [LarkPtxDot.setIndex32_i32, if_neg (Ne.symm h12)] using h.row
  · simpa only [LarkPtxMatrix.setIndex32_pointer] using h.a
  · simpa only [LarkPtxMatrix.setIndex32_pointer] using h.b
  · simpa only [LarkPtxMatrix.setIndex32_pointer] using h.out

theorem frame64 (t : Nat) (base : State α) (s : Machine α) (d : Nat) (v : Int)
    (h : Frame t base s) (hd : d ≠ 17 ∧ d ≠ 18 ∧ d ≠ 9) :
    Frame t base (setIndex64 s d v) := by
  rcases hd with ⟨ha, hb, ho⟩
  refine ⟨h.active, h.memory, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [LarkPtxMatrix.setIndex64_i32] using h.index
  · simpa only [LarkPtxMatrix.setIndex64_i32] using h.batch
  · simpa only [LarkPtxMatrix.setIndex64_i32] using h.batchA
  · simpa only [LarkPtxMatrix.setIndex64_i32] using h.lane
  · simpa only [LarkPtxMatrix.setIndex64_i32] using h.row
  · simpa only [LarkPtxMatrix.setIndex64_pointer, if_neg (Ne.symm ha)] using h.a
  · simpa only [LarkPtxMatrix.setIndex64_pointer, if_neg (Ne.symm hb)] using h.b
  · simpa only [LarkPtxMatrix.setIndex64_pointer, if_neg (Ne.symm ho)] using h.out

theorem frame_float (t : Nat) (base : State α) (s : Machine α) (d : Nat) (v : α)
    (h : Frame t base s) : Frame t base (setFloat s d v) := by
  have hi (r : Nat) : (setFloat s d v).registers.i32 r = s.registers.i32 r := by
    simp [LarkPtxDot.setFloat, LarkPtxDot.advance, putScalar, putValue, Registers.i32]
  refine ⟨h.active, h.memory, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hi] using h.index
  · simpa only [hi] using h.batch
  · simpa only [hi] using h.batchA
  · simpa only [hi] using h.lane
  · simpa only [hi] using h.row
  · simpa only [LarkPtxDot.setFloat_pointer] using h.a
  · simpa only [LarkPtxDot.setFloat_pointer] using h.b
  · simpa only [LarkPtxDot.setFloat_pointer] using h.out

def Result (ops : Ops α) (t : Nat) (base : State α) (s : Machine α)
    (pc : Nat) (update : Machine α → Machine α) : Prop :=
  ∃ next, Steps ops layout geometry t program s next ∧ Frame t base next ∧
    next.pc = pc+1 ∧ next = update s

theorem instruction_step (ops : Ops α) (t pc : Nat) (s next : Machine α)
    (ins : LarkPtxMatrix.Instruction) (hpc : s.pc = pc) (hs : s.registers.stopped = false)
    (hi : program[pc]? = some ins)
    (he : LarkPtxMatrix.execute ops layout geometry t ins s = some next) :
    Steps ops layout geometry t program s next := by
  apply LarkPtxMatrix.one_step
  rw [LarkPtxMatrix.transition_at ops layout geometry t program s ins hs (by rw [hpc]; exact hi)]
  exact he

theorem produce32 (ops : Ops α) (t : Nat) (base : State α) (s : Machine α)
    (pc d : Nat) (v : Int) (ins : LarkPtxMatrix.Instruction)
    (h : Frame t base s) (hpc : s.pc = pc) (hi : program[pc]? = some ins)
    (he : LarkPtxMatrix.execute ops layout geometry t ins s = some (setIndex32 s d v))
    (hd : d ≠ 1 ∧ d ≠ 8 ∧ d ≠ 9 ∧ d ≠ 11 ∧ d ≠ 12) :
    Result ops t base s pc (fun m => setIndex32 m d v) := by
  refine ⟨setIndex32 s d v, instruction_step ops t pc s _ ins hpc h.active hi he,
    frame32 t base s d v h hd, ?_, rfl⟩
  change s.pc+1 = pc+1
  rw [hpc]

theorem produce64 (ops : Ops α) (t : Nat) (base : State α) (s : Machine α)
    (pc d : Nat) (v : Int) (ins : LarkPtxMatrix.Instruction)
    (h : Frame t base s) (hpc : s.pc = pc) (hi : program[pc]? = some ins)
    (he : LarkPtxMatrix.execute ops layout geometry t ins s = some (setIndex64 s d v))
    (hd : d ≠ 17 ∧ d ≠ 18 ∧ d ≠ 9) :
    Result ops t base s pc (fun m => setIndex64 m d v) := by
  refine ⟨setIndex64 s d v, instruction_step ops t pc s _ ins hpc h.active hi he,
    frame64 t base s d v h hd, ?_, rfl⟩
  change s.pc+1 = pc+1
  rw [hpc]

theorem produce_float (ops : Ops α) (t : Nat) (base : State α) (s : Machine α)
    (pc d : Nat) (v : α) (ins : LarkPtxMatrix.Instruction)
    (h : Frame t base s) (hpc : s.pc = pc) (hi : program[pc]? = some ins)
    (he : LarkPtxMatrix.execute ops layout geometry t ins s = some (setFloat s d v)) :
    Result ops t base s pc (fun m => setFloat m d v) := by
  refine ⟨setFloat s d v, instruction_step ops t pc s _ ins hpc h.active hi he,
    frame_float t base s d v h, ?_, rfl⟩
  change s.pc+1 = pc+1
  rw [hpc]

end LarkPtxBatched.Bmm.Init

#print axioms LarkPtxBatched.Bmm.Init.prefix_frame
#print axioms LarkPtxBatched.Bmm.Init.frame32
#print axioms LarkPtxBatched.Bmm.Init.frame64
#print axioms LarkPtxBatched.Bmm.Init.frame_float
#print axioms LarkPtxBatched.Bmm.Init.produce32
#print axioms LarkPtxBatched.Bmm.Init.produce64
#print axioms LarkPtxBatched.Bmm.Init.produce_float
