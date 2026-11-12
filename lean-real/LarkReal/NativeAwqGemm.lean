import LarkReal.NativeAwqGemmSums
import Lark.NativeAwqGemmCorrect

/-! Independent dense exact-real matrix-product reference for the complete
native AWQ departure. This idealization gives no IEEE rounding error bound. -/
namespace LarkReal.NativeAwqGemm
open LarkNativeAwqGemm
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option autoImplicit false
attribute [local irreducible] kAccum

def denseRow (p : Shape) (b t e : Nat) : Nat :=
  (b/columnTiles p)*16+LarkMFMA.outputRow (laneId t) e
def denseCol (p : Shape) (b bank t : Nat) : Nat :=
  (b%columnTiles p)*tileN p+bank*16+LarkMFMA.outputCol (laneId t)

noncomputable def denseResult (p : Shape) (input : Nat → Nat → ℝ) (row col : Nat) : ℝ :=
  ((List.range p.k).map (denseTerm p input row col)).sum

noncomputable def denseSpec (p : Shape) (input : Nat → Nat → ℝ) : List ℝ :=
  (List.range (p.m*p.n)).map (fun offset => denseResult p input (offset/p.n) (offset%p.n))

theorem accumulator_real (p : Shape) (input : Nat → Nat → ℝ) (b n bank t e : Nat)
    (guard : denseRow p b t e<p.m) :
    kAccum p LarkReal.ops input b n bank t e=
      intervalSum (denseTerm p input (denseRow p b t e) (denseCol p b bank t)) 0 (n*32) := by
  induction n with
  | zero => simp only [kAccum,LarkReal.ops,Int.cast_zero,Nat.cast_one,div_one,Nat.zero_mul,interval_zero]
  | succ n ih =>
    rw [kAccum]
    change matrixDot p LarkReal.ops input n b 1 bank (LarkMFMA.outputRow (laneId t) e) (LarkMFMA.outputCol (laneId t))+
      (matrixDot p LarkReal.ops input n b 0 bank (LarkMFMA.outputRow (laneId t) e) (LarkMFMA.outputCol (laneId t))+
        kAccum p LarkReal.ops input b n bank t e)=_
    rw [matrix_dot_real p input n b 1 bank _ _ guard,matrix_dot_real p input n b 0 bank _ _ guard,ih]
    have whole := interval_add (denseTerm p input (denseRow p b t e) (denseCol p b bank t)) 0 (n*32) 32
    have halves : intervalSum (denseTerm p input (denseRow p b t e) (denseCol p b bank t)) (n*32) 32=
        intervalSum (denseTerm p input (denseRow p b t e) (denseCol p b bank t)) (n*32) 16+
        intervalSum (denseTerm p input (denseRow p b t e) (denseCol p b bank t)) (n*32+16) 16 :=
      interval_add _ (n*32) 16 16
    rw [show (n+1)*32=n*32+32 by omega,whole]
    simp only [Nat.zero_add,Nat.zero_mul,Nat.one_mul,Nat.add_zero]
    rw [halves]
    unfold denseRow denseCol
    ac_rfl

theorem source_output_real (p : Shape) (input : Nat → Nat → ℝ) (offset : Nat) (hi : offset<p.m*p.n) :
    sourceOutput p LarkReal.ops input offset=denseResult p input (offset/p.n) (offset%p.n) := by
  have row : denseRow p (blockId (writer p offset)) (writer p offset) (outputSlot p offset%4)=offset/p.n :=
    writer_output_row p offset
  have col : denseCol p (blockId (writer p offset)) (outputSlot p offset/4) (writer p offset)=offset%p.n := by
    simpa only [denseCol,columnTileId,outputLocalCol,LarkMFMA.outputCol,Nat.add_assoc] using writer_output_column p offset
  have guard : denseRow p (blockId (writer p offset)) (writer p offset) (outputSlot p offset%4)<p.m :=
    writer_output_guard p offset hi
  unfold sourceOutput
  change kAccum p LarkReal.ops input (blockId (writer p offset)) (p.k/32)
    (outputSlot p offset/4) (writer p offset) (outputSlot p offset%4)=_
  rw [accumulator_real p input _ _ _ _ _ guard,row,col]
  have aligned : p.k/32*32=p.k := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero p.k_aligned)
  rw [aligned]
  simp only [intervalSum,denseResult,Nat.zero_add]

theorem source_spec_real (p : Shape) : sourceSpec p LarkReal.ops=denseSpec p := by
  funext input
  unfold sourceSpec denseSpec
  apply List.map_congr_left
  intro offset hi
  exact source_output_real p input offset (List.mem_range.mp hi)

theorem canonical_correct (p : Shape) :
    LarkMFMA.Correct LarkReal.ops (layout p) (geometry p) (fuel p) (program p) (denseSpec p) := by
  rw [← source_spec_real]
  exact source_correct p LarkReal.ops

#print axioms accumulator_real
#print axioms source_output_real
#print axioms source_spec_real
#print axioms canonical_correct
end LarkReal.NativeAwqGemm
