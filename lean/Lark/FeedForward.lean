import Lark.Pipeline

/-! ReLU(X W1), stored in FP16, followed by the second matrix product. -/
namespace LarkFeedForward
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 20000000

structure Shape where
  m : Nat
  k : Nat
  h : Nat
  n : Nat
  mPos : 0<m
  kPos : 0<k
  hPos : 0<h
  nPos : 0<n
  xBound : m*k<2147483648
  upBound : k*h<2147483648
  hiddenBound : m*h<2147483648
  downBound : h*n<2147483648
  outBound : m*n<2147483648

def reluHalf : LarkPointwise.Scalar := .un .toHalf (.bin .max .input (.lit 0 1))
def stage1 (s : Shape) : LarkDotMap.Profile where
  toProfile:=LarkMatrix.profile s.m s.h s.k s.mPos s.hPos
    (LarkReduction.k_bound s.m s.h s.mPos s.hiddenBound) s.xBound s.upBound
  aHalf:=true
  bHalf:=true
  post:=reluHalf
  validPost:=by simp [reluHalf,LarkPointwise.Valid]
def stage2 (s : Shape) : LarkDotMap.Profile where
  toProfile:=LarkMatrix.profile s.m s.n s.h s.mPos s.nPos
    (LarkReduction.k_bound s.m s.n s.mPos s.outBound) s.hiddenBound s.downBound
  aHalf:=true
  bHalf:=true
  post:=.un .toHalf .input
  validPost:=by trivial
def chain (s : Shape) : LarkPipeline.Chain := ⟨stage1 s,stage2 s,rfl⟩

theorem hidden_eq (s : Shape) (ops : Ops α) (input : Nat → Nat → α) (i : Nat) :
    LarkPipeline.hidden (chain s) ops input i=
      ops.toHalf (ops.max (LarkDotMap.dotSpec ops input (stage1 s) i) (ops.literal 0 1)) := by
  unfold LarkPipeline.hidden
  rw [LarkDotMap.result_eq_dot]
  rfl

theorem correct (s : Shape) (ops : Ops α) (w : Nat) (hw : 0<w) :
    LarkPipeline.Correct (chain s) ops w := by
  apply LarkPipeline.correct
  · exact Nat.mul_pos s.mPos s.hPos
  · exact s.kPos
  · exact ⟨s.hiddenBound,LarkReduction.k_bound s.m s.k s.mPos s.xBound⟩
  · exact Nat.mul_pos s.mPos s.nPos
  · exact s.hPos
  · exact ⟨s.outBound,LarkReduction.k_bound s.m s.h s.mPos s.hiddenBound⟩
  · exact hw

#print axioms hidden_eq
#print axioms correct
end LarkFeedForward
