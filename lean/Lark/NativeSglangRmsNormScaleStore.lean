import Lark.NativeSglangRmsNormScaleLoad

/-! Four source-ordered multiplies followed by two explicit half conversions
and private output stores. The input and weight caches remain raw and unchanged.
-/
namespace LarkNativeSglangRmsNorm
open LarkNonlinear
open LarkReduction (setReg execute_pure_of)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def scaleProduct (ops : Ops α) (x weight inverse : α) : α :=
  ops.toHalf (ops.mul (ops.mul x inverse) weight)

def scaleCompute (ops : Ops α) (t slot : Nat) (x y u v inverse : α) (s : State α) : State α :=
  let s := setReg s t 17 (ops.mul x inverse) 88
  let s := setReg s t 18 (ops.mul (ops.mul x inverse) u) 89
  let s := setReg s t 19 (ops.mul y inverse) 90
  let s := setReg s t 20 (ops.mul (ops.mul y inverse) v) 91
  let s := cacheWritten t 92 (privateCell t 2 slot) (scaleProduct ops x u inverse) s
  cacheWritten t 93 (privateCell t 2 (slot+1)) (scaleProduct ops y v inverse) s

theorem store_private_half (p : Shape) (ops : Ops α) (t slot reg pc : Nat) (ix : Index)
    (value : α) (s : State α) (hs : slot<16)
    (hi : evalIndex (geometry p) t s ix=some (slot : Int)) (hv : s.regs t reg=some value)
    (hp : s.pc t=pc) :
    execute ops (layout p) (geometry p) t (.store .local 2 ix (.un .toHalf (.reg reg))) s=
      some (cacheWritten t (pc+1) (privateCell t 2 slot) (ops.toHalf value) s) := by
  simp [execute,hi,private_location p t 2 slot true (by decide) hs,evalExpr,applyUnary,hv,hp,cacheWritten,privateCell,record]

theorem scale_compute_eq (p : Shape) (ops : Ops α) (t slot extra : Nat) (x y u v inverse : α)
    (s : State α) (hs : slot+1<16) (hi : s.indices t 18=some (slot : Int)) (hp : s.pc t=87)
    (hx : s.regs t 13=some x) (hy : s.regs t 14=some y) (hu : s.regs t 15=some u)
    (hv : s.regs t 16=some v) (hi12 : s.regs t 12=some inverse) :
    LarkCollective.runLane ops (layout p) (geometry p) (program true) t (extra+6) s=
    LarkCollective.runLane ops (layout p) (geometry p) (program true) t extra (scaleCompute ops t slot x y u v inverse s) := by
  let s1 := setReg s t 17 (ops.mul x inverse) 88
  let s2 := setReg s1 t 18 (ops.mul (ops.mul x inverse) u) 89
  let s3 := setReg s2 t 19 (ops.mul y inverse) 90
  let s4 := setReg s3 t 20 (ops.mul (ops.mul y inverse) v) 91
  let s5 := cacheWritten t 92 (privateCell t 2 slot) (scaleProduct ops x u inverse) s4
  have e1 := execute_pure_of ops (layout p) (geometry p) t 17 88 (.bin .mul (.reg 13) (.reg 12)) s
    (ops.mul x inverse) (by simp [evalExpr,applyBinary,hx,hi12]) (by omega)
  have e2 := execute_pure_of ops (layout p) (geometry p) t 18 89 (.bin .mul (.reg 17) (.reg 15)) s1
    (ops.mul (ops.mul x inverse) u) (by simp [evalExpr,applyBinary,s1,setReg,advance,hu]) (by simp [s1,setReg,advance])
  have e3 := execute_pure_of ops (layout p) (geometry p) t 19 90 (.bin .mul (.reg 14) (.reg 12)) s2
    (ops.mul y inverse) (by simp [evalExpr,applyBinary,s2,s1,setReg,advance,hy,hi12]) (by simp [s2,setReg,advance])
  have e4 := execute_pure_of ops (layout p) (geometry p) t 20 91 (.bin .mul (.reg 19) (.reg 16)) s3
    (ops.mul (ops.mul y inverse) v) (by simp [evalExpr,applyBinary,s3,s2,s1,setReg,advance,hv]) (by simp [s3,setReg,advance])
  have e5 : execute ops (layout p) (geometry p) t (.store .local 2 (.ivar 18) (.un .toHalf (.reg 18))) s4=some s5 :=
    store_private_half p ops t slot 18 91 (.ivar 18) _ s4 (by omega) hi
      (by simp [s4,s3,s2,setReg,advance]) (by simp [s4,setReg,advance])
  have plus : evalIndex (geometry p) t s5 (.add (.ivar 18) (.const 1))=some ((slot+1 : Nat) : Int) :=
    eval_nat_sum (geometry p) t slot 1 s5 (.ivar 18) (.const 1) hi rfl (by omega)
  have e6 : execute ops (layout p) (geometry p) t
      (.store .local 2 (.add (.ivar 18) (.const 1)) (.un .toHalf (.reg 20))) s5=
      some (scaleCompute ops t slot x y u v inverse s) :=
    store_private_half p ops t (slot+1) 20 92 _ _ s5 hs plus
      (by simp [s5,cacheWritten,s4,setReg,advance,record]) (by simp [s5,cacheWritten,advance])
  rw [scalar_step p true ops t 87 (extra+5) _ s s1 (by decide) hp e1]
  rw [scalar_step p true ops t 88 (extra+4) _ s1 s2 (by decide) (by simp [s1,setReg,advance]) e2]
  rw [scalar_step p true ops t 89 (extra+3) _ s2 s3 (by decide) (by simp [s2,setReg,advance]) e3]
  rw [scalar_step p true ops t 90 (extra+2) _ s3 s4 (by decide) (by simp [s3,setReg,advance]) e4]
  rw [scalar_step p true ops t 91 (extra+1) _ s4 s5 (by decide) (by simp [s4,setReg,advance]) e5]
  rw [scalar_step p true ops t 92 extra _ s5 _ (by decide) (by simp [s5,cacheWritten,advance]) e6]

theorem scale_compute_fields (ops : Ops α) (t slot : Nat) (x y u v inverse : α) (s : State α) :
    (scaleCompute ops t slot x y u v inverse s).pc t=93 ∧
    (scaleCompute ops t slot x y u v inverse s).regs t 12=s.regs t 12 ∧
    (scaleCompute ops t slot x y u v inverse s).indices=s.indices ∧
    (scaleCompute ops t slot x y u v inverse s).epochs=s.epochs := by
  simp [scaleCompute,setReg,advance,cacheWritten,record]

theorem scale_compute_other (ops : Ops α) (t slot other : Nat) (x y u v inverse : α)
    (s : State α) (ht : other≠t) :
    (scaleCompute ops t slot x y u v inverse s).pc other=s.pc other ∧
    (scaleCompute ops t slot x y u v inverse s).regs other=s.regs other := by
  simp [scaleCompute,setReg,advance,cacheWritten,record,ht]

theorem scale_compute_memory (ops : Ops α) (t slot : Nat) (x y u v inverse : α) (s : State α) (l : Location) :
    (scaleCompute ops t slot x y u v inverse s).memory l=
      if l=privateCell t 2 (slot+1) then some (scaleProduct ops y v inverse)
      else if l=privateCell t 2 slot then some (scaleProduct ops x u inverse) else s.memory l := rfl

theorem scale_compute_written (ops : Ops α) (t slot : Nat) (x y u v inverse : α) (s : State α) :
    (scaleCompute ops t slot x y u v inverse s).memory (privateCell t 2 slot)=some (scaleProduct ops x u inverse) ∧
    (scaleCompute ops t slot x y u v inverse s).memory (privateCell t 2 (slot+1))=some (scaleProduct ops y v inverse) := by
  simp [scale_compute_memory,privateCell]

theorem scale_compute_trace (ops : Ops α) (t slot : Nat) (x y u v inverse : α) (s : State α) :
    (scaleCompute ops t slot x y u v inverse s).trace=
      ⟨t,privateCell t 2 (slot+1),true,s.epochs t⟩::⟨t,privateCell t 2 slot,true,s.epochs t⟩::s.trace := rfl

theorem scale_compute_good (ops : Ops α) (t slot : Nat) (x y u v inverse : α) (s : State α)
    (good : ∀ event∈s.trace,Good event) :
    ∀ event∈(scaleCompute ops t slot x y u v inverse s).trace,Good event := by
  intro event he
  rw [scale_compute_trace] at he
  rcases List.mem_cons.mp he with rfl | he
  · exact Good.localAccess rfl rfl
  rcases List.mem_cons.mp he with rfl | he
  · exact Good.localAccess rfl rfl
  · exact good event he

#print axioms store_private_half
#print axioms scale_compute_eq
#print axioms scale_compute_fields
#print axioms scale_compute_other
#print axioms scale_compute_memory
#print axioms scale_compute_written
#print axioms scale_compute_trace
#print axioms scale_compute_good
end LarkNativeSglangRmsNorm
