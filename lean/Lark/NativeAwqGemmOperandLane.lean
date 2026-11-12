import Lark.NativeAwqGemmOperandLoop

/-! Complete scalar visit from a matrix-pass/bank entry to its native MFMA
cut. Only the first bank loads A; every bank loads its own B fragment. -/
namespace LarkNativeAwqGemm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option autoImplicit false
variable {α : Type}
attribute [local irreducible] operandLoop operandLoaded

def operandLaneStart (p : Shape) (half bank : Nat) : Nat :=
  if bank=0 then passPC p half else operandStart p half bank false
def operandLaneCost (bank : Nat) : Nat := if bank=0 then 8 else 4
def operandBeforeB (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile t half bank : Nat) (s : State α) : State α :=
  if bank=0 then operandLoop p ops input tile t half bank true 0 4 s else s
def operandLaneState (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile t half bank : Nat) (s : State α) : State α :=
  operandLoop p ops input tile t half bank false 0 4 (operandBeforeB p ops input tile t half bank s)

theorem operand_before_b_frames (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile t half bank : Nat) (s : State α) :
    (operandBeforeB p ops input tile t half bank s).memory=s.memory ∧
      (operandBeforeB p ops input tile t half bank s).indices=s.indices ∧
        (operandBeforeB p ops input tile t half bank s).epochs=s.epochs := by
  unfold operandBeforeB
  split
  · exact operand_loop_frames p ops input tile t half bank 0 4 true s
  · exact ⟨rfl,rfl,rfl⟩

theorem operand_before_b_pc (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile t half bank : Nat) (s : State α) (hp : s.pc t=operandLaneStart p half bank) :
    (operandBeforeB p ops input tile t half bank s).pc t=operandStart p half bank false := by
  by_cases zero : bank=0
  · subst bank
    have start : s.pc t=operandStart p half 0 true+0 := by simpa [operandStart,operandLaneStart] using hp
    have finish := operand_loop_pc p ops input tile t half 0 0 4 true s start
    simpa [operandBeforeB,operandStart] using finish
  · simpa [operandBeforeB,operandLaneStart,zero] using hp

theorem operand_lane_frames (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile t half bank : Nat) (s : State α) :
    (operandLaneState p ops input tile t half bank s).memory=s.memory ∧
      (operandLaneState p ops input tile t half bank s).indices=s.indices ∧
        (operandLaneState p ops input tile t half bank s).epochs=s.epochs := by
  have a := operand_before_b_frames p ops input tile t half bank s
  have b := operand_loop_frames p ops input tile t half bank 0 4 false (operandBeforeB p ops input tile t half bank s)
  exact ⟨b.1.trans a.1,b.2.1.trans a.2.1,b.2.2.trans a.2.2⟩

theorem operand_lane_pc (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile t half bank : Nat) (s : State α) (hp : s.pc t=operandLaneStart p half bank) :
    (operandLaneState p ops input tile t half bank s).pc t=matrixPC p half bank := by
  have ready := operand_before_b_pc p ops input tile t half bank s hp
  have finish := operand_loop_pc p ops input tile t half bank 0 4 false (operandBeforeB p ops input tile t half bank s)
    (by simpa only [Nat.add_zero] using ready)
  rw [show operandStart p half bank false+(0+4)=matrixPC p half bank by
    unfold operandStart matrixPC; simp only [Bool.false_eq_true,ite_false]; omega] at finish
  exact finish

theorem operand_lane_eq (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b t half bank extra : Nat) (s : State α) (hb : blockId t=b) (hh : half<2) (hbank : bank<banks p)
    (hi : s.indices t 0=some ((laneId t : Nat) : Int)) (reads : TileReads p ops input tile b s)
    (hp : s.pc t=operandLaneStart p half bank) :
    LarkMFMA.runLane ops (layout p) (geometry p) (program p) t (extra+operandLaneCost bank) s=
      LarkMFMA.runLane ops (layout p) (geometry p) (program p) t extra (operandLaneState p ops input tile t half bank s) := by
  let beforeB := operandBeforeB p ops input tile t half bank s
  have frame := operand_before_b_frames p ops input tile t half bank s
  have bIndex : beforeB.indices t 0=some ((laneId t : Nat) : Int) := by rw [frame.2.1]; exact hi
  have bReads : TileReads p ops input tile b beforeB := tile_reads_of_memory p ops input tile b s beforeB reads frame.1
  have bPC : beforeB.pc t=operandStart p half bank false+0 := by
    simpa only [Nat.add_zero] using operand_before_b_pc p ops input tile t half bank s hp
  have bStep := operand_loop_eq p ops input tile b t half bank 0 4 extra false beforeB hb hh hbank (by decide) bIndex bReads bPC
  by_cases zero : bank=0
  · rw [operandLaneCost,if_pos zero]
    have aPC : s.pc t=operandStart p half bank true+0 := by simpa [operandStart,operandLaneStart,zero] using hp
    rewrite [show extra+8=(extra+4)+4 by omega,
      operand_loop_eq p ops input tile b t half bank 0 4 (extra+4) true s hb hh hbank (by decide) hi reads aPC]
    have same : beforeB=operandLoop p ops input tile t half bank true 0 4 s := by simp [beforeB,operandBeforeB,zero]
    simpa only [operandLaneState,←same] using bStep
  · rw [operandLaneCost,if_neg zero]
    have same : beforeB=s := by simp [beforeB,operandBeforeB,zero]
    change LarkMFMA.runLane ops (layout p) (geometry p) (program p) t (extra+4) s=
      LarkMFMA.runLane ops (layout p) (geometry p) (program p) t extra
        (operandLoop p ops input tile t half bank false 0 4 beforeB)
    rw [same] at bStep ⊢
    exact bStep

theorem operand_lane_run (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b t half bank : Nat) (s : State α) (hb : blockId t=b) (hh : half<2) (hbank : bank<banks p)
    (hi : s.indices t 0=some ((laneId t : Nat) : Int)) (reads : TileReads p ops input tile b s)
    (hp : s.pc t=operandLaneStart p half bank) :
    LarkMFMA.runLane ops (layout p) (geometry p) (program p) t (fuel p).lane s=
      some (operandLaneState p ops input tile t half bank s) := by
  have cost : operandLaneCost bank<512 := by unfold operandLaneCost; split <;> omega
  have step := operand_lane_eq p ops input tile b t half bank (512-operandLaneCost bank) s hb hh hbank hi reads hp
  rw [show 512-operandLaneCost bank+operandLaneCost bank=512 by omega] at step
  change LarkMFMA.runLane ops (layout p) (geometry p) (program p) t 512 s=_
  rw [step]
  exact run_lane_parked p ops t _ _ .matrix (by omega)
    (by simp only [LarkMFMA.parked,operand_lane_pc p ops input tile t half bank s hp,
      matrix_instruction_site p half bank hh hbank])

theorem operand_lane_b_value (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile t half bank e : Nat) (s : State α) (he : e<4) :
    (operandLaneState p ops input tile t half bank s).regs t (rightBase p half bank+e)=
      some (bOperand p input tile t half bank e) :=
  operand_loop_reg_written p ops input tile t half bank 0 4 e false (operandBeforeB p ops input tile t half bank s) (by omega) he

theorem operand_lane_a_value (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile t half bank e : Nat) (s : State α) (he : e<4)
    (prior : bank≠0 → ∀ q, q<4 → s.regs t (leftBase p half+q)=some (aOperand p ops input tile t half q)) :
    (operandLaneState p ops input tile t half bank s).regs t (leftBase p half+e)=
      some (aOperand p ops input tile t half e) := by
  have a : (operandBeforeB p ops input tile t half bank s).regs t (leftBase p half+e)=some (aOperand p ops input tile t half e) := by
    unfold operandBeforeB
    split
    · exact operand_loop_reg_written p ops input tile t half bank 0 4 e true s (by omega) he
    · rename_i nonzero; exact prior nonzero e he
  have b := operand_loop_reg_outside p ops input tile t t half bank 0 4 (leftBase p half+e) false
    (operandBeforeB p ops input tile t half bank s) (by intro q hlo hhi; unfold operandBase rightBase; simp only [Bool.false_eq_true,ite_false]; omega)
  exact b.trans a

theorem operand_base_lower (p : Shape) (half bank : Nat) (left : Bool) : 4*banks p≤operandBase p half bank left := by
  have lower : 4*banks p≤leftBase p half := by unfold leftBase; split <;> omega
  cases left <;> simp only [operandBase,ite_true,ite_false,Bool.false_eq_true,rightBase] <;> omega

theorem operand_loop_accumulator (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile t u half bank e n r : Nat) (left : Bool) (s : State α) (hr : r<4*banks p) :
    (operandLoop p ops input tile t half bank left e n s).regs u r=s.regs u r :=
  operand_loop_reg_outside p ops input tile t u half bank e n r left s
    (by intro q hlo hhi; have lower := operand_base_lower p half bank left; omega)

theorem operand_lane_accumulator (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile t u half bank r : Nat) (s : State α) (hr : r<4*banks p) :
    (operandLaneState p ops input tile t half bank s).regs u r=s.regs u r := by
  unfold operandLaneState
  rw [operand_loop_accumulator p ops input tile t u half bank 0 4 r false _ hr]
  unfold operandBeforeB
  split
  · exact operand_loop_accumulator p ops input tile t u half bank 0 4 r true s hr
  · rfl

#print axioms operand_before_b_frames
#print axioms operand_before_b_pc
#print axioms operand_lane_frames
#print axioms operand_lane_pc
#print axioms operand_lane_eq
#print axioms operand_lane_run
#print axioms operand_lane_b_value
#print axioms operand_lane_a_value
#print axioms operand_base_lower
#print axioms operand_loop_accumulator
#print axioms operand_lane_accumulator
end LarkNativeAwqGemm
