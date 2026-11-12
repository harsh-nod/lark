import Lark.NativeAwqGemmMMAElement
import LarkReal.Ops

/-! Canonical dense real terms and finite-interval algebra for the unchanged
native matrix operation. Storage conversions are identities over reals. -/
namespace LarkReal.NativeAwqGemm
open LarkNativeAwqGemm
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option autoImplicit false

noncomputable def denseTerm (p : Shape) (input : Nat → Nat → ℝ) (row col k : Nat) : ℝ :=
  input 0 (row*p.k+k)*input 1 (k*p.n+col)

noncomputable def intervalSum (f : Nat → ℝ) (start n : Nat) : ℝ :=
  ((List.range n).map (fun k => f (start+k))).sum

theorem interval_zero (f : Nat → ℝ) (start : Nat) : intervalSum f start 0=0 := rfl

theorem interval_succ (f : Nat → ℝ) (start n : Nat) :
    intervalSum f start (n+1)=intervalSum f start n+f (start+n) :=
  List.sum_range_succ (fun k => f (start+k)) n

theorem interval_add (f : Nat → ℝ) (start m n : Nat) :
    intervalSum f start (m+n)=intervalSum f start m+intervalSum f (start+m) n := by
  induction n with
  | zero => simp only [Nat.add_zero,interval_zero,add_zero]
  | succ n ih =>
    rw [show m+(n+1)=(m+n)+1 by omega,interval_succ,ih,interval_succ]
    simp only [Nat.add_assoc,add_assoc]

theorem mfma_real_dot (left right : Nat → ℝ) :
    LarkMFMA.dot LarkReal.ops left right=((List.range 16).map (fun k => left k*right k)).sum := by
  simp only [LarkMFMA.dot,LarkReal.ops,id_eq,Int.cast_zero,Nat.cast_one,div_one]
  simpa using LarkReal.fold_add ((List.range 16).map (fun k => left k*right k)) id 0

theorem matrix_dot_real (p : Shape) (input : Nat → Nat → ℝ)
    (tile b half bank row col : Nat) (guard : (b/columnTiles p)*16+row<p.m) :
    matrixDot p LarkReal.ops input tile b half bank row col=
      intervalSum (denseTerm p input ((b/columnTiles p)*16+row)
        ((b%columnTiles p)*tileN p+bank*16+col)) (tile*32+half*16) 16 := by
  unfold matrixDot
  rw [mfma_real_dot]
  simp only [aTileValue,if_pos guard,bTileValue,intervalSum,denseTerm,Nat.add_assoc]

#print axioms interval_zero
#print axioms interval_succ
#print axioms interval_add
#print axioms mfma_real_dot
#print axioms matrix_dot_real
end LarkReal.NativeAwqGemm
