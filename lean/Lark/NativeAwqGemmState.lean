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

theorem eval_nat_const (g : Geometry) (t value : Nat) (s : State α)
    (hb : value<2147483648) : evalIndex g t s (c value)=some (value : Int) := by
  change int32 (value : Int)=some (value : Int)
  exact int32_nat value hb

theorem eval_int_add (g : Geometry) (t : Nat) (s : State α) (a b : Index) (x y z : Int)
    (ha : evalIndex g t s a=some x) (hb : evalIndex g t s b=some y)
    (hs : int32 (x+y)=some z) : evalIndex g t s (.add a b)=some z := by
  change (do
    let x ← evalIndex g t s a
    let y ← evalIndex g t s b
    int32 (x+y)) = _
  rw [ha,hb]
  exact hs

theorem eval_int_mul (g : Geometry) (t : Nat) (s : State α) (a b : Index) (x y z : Int)
    (ha : evalIndex g t s a=some x) (hb : evalIndex g t s b=some y)
    (hs : int32 (x*y)=some z) : evalIndex g t s (.mul a b)=some z := by
  change (do
    let x ← evalIndex g t s a
    let y ← evalIndex g t s b
    int32 (x*y)) = _
  rw [ha,hb]
  exact hs

theorem eval_nat_add (g : Geometry) (t left right : Nat) (s : State α) (a b : Index)
    (ha : evalIndex g t s a=some (left : Int))
    (hb : evalIndex g t s b=some (right : Int)) (hs : left+right<2147483648) :
    evalIndex g t s (.add a b)=some ((left+right : Nat) : Int) :=
  eval_int_add g t s a b (left : Int) (right : Int) ((left+right : Nat) : Int) ha hb
    ((congrArg int32 (Int.natCast_add left right).symm).trans (int32_nat _ hs))

theorem eval_nat_mul (g : Geometry) (t left right : Nat) (s : State α) (a b : Index)
    (ha : evalIndex g t s a=some (left : Int))
    (hb : evalIndex g t s b=some (right : Int)) (hs : left*right<2147483648) :
    evalIndex g t s (.mul a b)=some ((left*right : Nat) : Int) :=
  eval_int_mul g t s a b (left : Int) (right : Int) ((left*right : Nat) : Int) ha hb
    ((congrArg int32 (Int.natCast_mul left right).symm).trans (int32_nat _ hs))

theorem execute_pure_of (ops : Ops α) (p : Shape) (t r pc : Nat)
    (expression : Expr) (s : State α) (value : α)
    (he : evalExpr ops (layout p) (geometry p) t expression s=some (value,s))
    (hp : s.pc t+1=pc) :
    execute ops (layout p) (geometry p) t (.assign r expression) s=some (setReg s t r value pc) := by
  simp only [execute,he,hp,bind,pure,Option.bind]
  rfl

theorem eval_int_lt_true (g : Geometry) (t : Nat) (s : State α) (a b : Index) (x y : Int)
    (ha : evalIndex g t s a=some x) (hb : evalIndex g t s b=some y) (hlt : x<y) :
    evalPredicate g t s (.lt a b)=some true := by
  change (do
    let left ← evalIndex g t s a
    let right ← evalIndex g t s b
    pure (decide (left<right))) = _
  rw [ha,hb]
  simp [hlt]

theorem execute_branch_true (ops : Ops α) (p : Shape) (t target : Nat)
    (condition : Predicate) (s : State α) (he : evalPredicate (geometry p) t s condition=some true) :
    execute ops (layout p) (geometry p) t (.branch condition target) s=
      some (advance s t (s.pc t+1)) := by
  simp only [execute,he,bind,pure,Option.bind,ite_true]

#print axioms int32_nat
#print axioms execute_index_of
#print axioms scalar_step
#print axioms eval_nat_div
#print axioms eval_nat_mod
#print axioms eval_nat_const
#print axioms eval_int_add
#print axioms eval_int_mul
#print axioms eval_nat_add
#print axioms eval_nat_mul
#print axioms execute_pure_of
#print axioms eval_int_lt_true
#print axioms execute_branch_true
end LarkNativeAwqGemm
