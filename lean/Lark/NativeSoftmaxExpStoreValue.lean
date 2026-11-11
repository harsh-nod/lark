import Lark.NativeSoftmaxExpStoreHead

/-! Actual private read and exponential value in the output loop. Private
storage already contains the converted input; the subtraction uses that value
as its left operand and the broadcast maximum as its right operand. -/
namespace LarkNativeSoftmax
open LarkNonlinear
open LarkReduction (setReg execute_pure_of)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def expComponentValue (ops : Ops α) (input : Nat → Nat → α) (offset : α)
    (row tid iteration component : Nat) : α :=
  ops.exp (ops.sub (expInputValue ops input row tid iteration component) offset)

def expStoreValues (ops : Ops α) (value offset : α) (t component : Nat) (s : State α) : State α :=
  let s := setReg (record s t (localCell 0 t component) false) t 7 value 61
  setReg s t 8 (ops.exp (ops.sub value offset)) 62

theorem local_value_eval_of (ops : Ops α) (l : Layout) (g : Geometry)
    (t component indexReg : Nat) (value : α) (s : State α)
    (hl : location l g t .local 0 (component : Int) false=some (localCell 0 t component))
    (hi : s.indices t indexReg=some (component : Int))
    (hm : s.memory (localCell 0 t component)=some value) :
    evalExpr ops l g t (.load .local 0 (.ivar indexReg)) s =
      some (value,record s t (localCell 0 t component) false) := by
  simp only [evalExpr,evalIndex,hi,hl,hm,bind,pure,Option.bind]

theorem exp_value_eval_of (ops : Ops α) (l : Layout) (g : Geometry)
    (t : Nat) (value offset : α) (s : State α)
    (h7 : s.regs t 7=some value) (h5 : s.regs t 5=some offset) :
    evalExpr ops l g t (.un .exp (.bin .sub (.reg 7) (.reg 5))) s=
      some (ops.exp (ops.sub value offset),s) := by
  simp only [evalExpr,applyBinary,applyUnary,h7,h5,bind,pure,Option.bind]

theorem exp_store_values_eq (p : Shape) (guarded : Bool) (ops : Ops α)
    (value offset : α) (t component extra : Nat) (s : State α) (hc : component<8)
    (hp : s.pc t=60) (h13 : s.indices t 13=some (component : Int))
    (hm : s.memory (localCell 0 t component)=some value) (h5 : s.regs t 5=some offset) :
    LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t (extra+2) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t extra
        (expStoreValues ops value offset t component s) := by
  let next := setReg (record s t (localCell 0 t component) false) t 7 value 61
  have load := local_value_eval_of ops (layout p) (geometry p) t component 13 value s
    (exp_local_location p t component hc false) h13 hm
  have e1 : execute ops (layout p) (geometry p) t (.assign 7 (.load .local 0 (.ivar 13))) s=some next := by
    simp only [execute,load,hp,bind,pure,Option.bind]
    rfl
  have h7 : next.regs t 7=some value := by simp [next,setReg,advance]
  have h5next : next.regs t 5=some offset := by simpa [next,setReg,record,advance] using h5
  have e2 := execute_pure_of ops (layout p) (geometry p) t 8 62
    (.un .exp (.bin .sub (.reg 7) (.reg 5))) next (ops.exp (ops.sub value offset))
    (exp_value_eval_of ops (layout p) (geometry p) t value offset next h7 h5next)
    (by simp [next,setReg,advance])
  rewrite [show extra+2=(extra+1)+1 by omega,
    scalar_step p guarded ops t 60 _ _ s next (by cases guarded <;> rfl) hp e1]
  exact scalar_step p guarded ops t 61 extra _ next _ (by cases guarded <;> rfl)
    (by simp [next,setReg,advance]) e2

theorem exp_store_values_fields (ops : Ops α) (value offset : α) (t component : Nat) (s : State α) :
    (expStoreValues ops value offset t component s).pc t=62 ∧
    (expStoreValues ops value offset t component s).regs t 8=some (ops.exp (ops.sub value offset)) ∧
    (expStoreValues ops value offset t component s).memory=s.memory ∧
    (expStoreValues ops value offset t component s).indices=s.indices ∧
    (expStoreValues ops value offset t component s).epochs=s.epochs ∧
    (expStoreValues ops value offset t component s).trace=⟨t,localCell 0 t component,false,s.epochs t⟩::s.trace := by
  simp [expStoreValues,setReg,record,advance]

theorem exp_store_values_reg_other (ops : Ops α) (value offset : α) (t component r : Nat) (s : State α)
    (h7 : r ≠ 7) (h8 : r ≠ 8) :
    (expStoreValues ops value offset t component s).regs t r=s.regs t r := by
  simp [expStoreValues,setReg,record,advance,h7,h8]

theorem exp_store_values_other (ops : Ops α) (value offset : α) (t component u : Nat) (s : State α) (hu : u ≠ t) :
    OtherThread t u s (expStoreValues ops value offset t component s) := by
  simp [OtherThread,expStoreValues,setReg,record,advance,hu]

theorem exp_store_values_good (ops : Ops α) (value offset : α) (t component : Nat) (s : State α)
    (good : ∀ a ∈ s.trace, Good a) : ∀ a ∈ (expStoreValues ops value offset t component s).trace, Good a := by
  intro a ha
  rewrite [(exp_store_values_fields ops value offset t component s).2.2.2.2.2] at ha
  rcases List.mem_cons.mp ha with rfl | ha
  · exact Good.privateAccess rfl rfl
  · exact good a ha

theorem exp_component_value_in_bounds (ops : Ops α) (input : Nat → Nat → α) (offset : α)
    (row tid iteration component : Nat) (hc : column tid iteration component<50257) :
    expComponentValue ops input offset row tid iteration component=
      ops.exp (ops.sub (ops.fromHalf (input 1 (address row (column tid iteration component)))) offset) := by
  simp only [expComponentValue,expInputValue,in_bounds_clamp _ hc]

#print axioms local_value_eval_of
#print axioms exp_value_eval_of
#print axioms exp_store_values_eq
#print axioms exp_store_values_fields
#print axioms exp_store_values_reg_other
#print axioms exp_store_values_other
#print axioms exp_store_values_good
#print axioms exp_component_value_in_bounds
end LarkNativeSoftmax
