import Lark.NativeAwqGemmGeometry

/-! Scalar stepping for the actual source-bound native MFMA machine. -/
namespace LarkNativeAwqGemm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option autoImplicit false
variable {α : Type}

def setIndex (s : State α) (t r : Nat) (value : Int) (pc : Nat) : State α :=
  advance {s with indices := fun u q => if u=t ∧ q=r then some value else s.indices u q} t pc

def setReg (s : State α) (t r : Nat) (value : α) (pc : Nat) : State α :=
  advance {s with regs := fun u q => if u=t ∧ q=r then some value else s.regs u q} t pc

theorem int32_nat (value : Nat) (h : value<2147483648) :
    int32 (value : Int)=some (value : Int) := by
  have h0 : (0 : Int)≤(value : Int) := by omega
  have h1 : (value : Int)<2147483648 := by omega
  simp only [int32, h0, h1, and_self, ite_true]

theorem execute_index_of (ops : Ops α) (p : Shape) (t r pc : Nat)
    (index : Index) (s : State α) (value : Int)
    (he : evalIndex (geometry p) t s index=some value) (hp : s.pc t+1=pc) :
    execute ops (layout p) (geometry p) t (.index r index) s=some (setIndex s t r value pc) := by
  simp only [execute, he, hp, bind, pure, Option.bind]
  rfl

theorem scalar_step (p : Shape) (ops : Ops α) (t pc extra : Nat)
    (instruction : LarkNonlinear.Instr) (s next : State α)
    (hi : (program p)[pc]?=some (.scalar instruction)) (hp : s.pc t=pc)
    (he : execute ops (layout p) (geometry p) t instruction s=some next) :
    LarkMFMA.runLane ops (layout p) (geometry p) (program p) t (extra+1) s=
      LarkMFMA.runLane ops (layout p) (geometry p) (program p) t extra next := by
  have parked : LarkMFMA.parked (program p) s t=none := by
    cases instruction <;> simp_all [LarkMFMA.parked,execute]
  rewrite [LarkMFMA.runLane,parked]
  simp only [hp,hi,bind,pure,Option.bind,he]

theorem eval_nat_div (g : Geometry) (t value divisor : Nat) (s : State α) (index : Index)
    (he : evalIndex g t s index=some (value : Int))
    (hd : 0<divisor) (hb : divisor<2147483648) :
    evalIndex g t s (.div index (c divisor))=some ((value/divisor : Nat) : Int) := by
  change (do
    let x ← evalIndex g t s index
    let y ← int32 (divisor : Int)
    if y=0 ∨ x<0 ∨ y<0 then none else some (x/y)) = _
  rw [he,int32_nat divisor hb]
  change (if (divisor : Int)=0 ∨ (value : Int)<0 ∨ (divisor : Int)<0 then none
    else some ((value : Int)/(divisor : Int))) = _
  rw [if_neg (by omega),←Int.ofNat_ediv]

theorem eval_nat_mod (g : Geometry) (t value divisor : Nat) (s : State α) (index : Index)
    (he : evalIndex g t s index=some (value : Int))
    (hd : 0<divisor) (hb : divisor<2147483648) :
    evalIndex g t s (.mod index (c divisor))=some ((value%divisor : Nat) : Int) := by
  change (do
    let x ← evalIndex g t s index
    let y ← int32 (divisor : Int)
    if y=0 ∨ x<0 ∨ y<0 then none else some (x%y)) = _
  rw [he,int32_nat divisor hb]
  change (if (divisor : Int)=0 ∨ (value : Int)<0 ∨ (divisor : Int)<0 then none
    else some ((value : Int)%(divisor : Int))) = _
  rw [if_neg (by omega),←Int.ofNat_emod]

#print axioms int32_nat
#print axioms execute_index_of
#print axioms scalar_step
#print axioms eval_nat_div
#print axioms eval_nat_mod
end LarkNativeAwqGemm
