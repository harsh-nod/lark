import Lark.NativeSoftmaxExpStoreEmit

/-! Composition of the five valid-column instructions: private read,
exponential, address, converted store and unrounded sum. -/
namespace LarkNativeSoftmax
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def expStoreBody (ops : Ops α) (input : Nat → Nat → α) (offset acc : α)
    (row tid iteration component t : Nat) (s : State α) : State α :=
  expStoreEmit ops (expComponentValue ops input offset row tid iteration component) acc
    row (column tid iteration component) t
    (expStoreValues ops (expInputValue ops input row tid iteration component) offset t component s)

theorem exp_store_body_eq (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α) (offset acc : α)
    (row tid iteration component t extra : Nat) (s : State α) (hr : row<p.rows) (hc : component<8)
    (hcol : column tid iteration component<50257) (hp : s.pc t=60)
    (h0 : s.indices t 0=some (row : Int))
    (h14 : s.indices t 14=some ((column tid iteration component : Nat) : Int))
    (h13 : s.indices t 13=some (component : Int))
    (hm : s.memory (localCell 0 t component)=some (expInputValue ops input row tid iteration component))
    (h5 : s.regs t 5=some offset) (h6 : s.regs t 6=some acc) :
    LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t (extra+5) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t extra
        (expStoreBody ops input offset acc row tid iteration component t s) := by
  have values := exp_store_values_fields ops (expInputValue ops input row tid iteration component) offset t component s
  have accValue := (exp_store_values_reg_other ops (expInputValue ops input row tid iteration component)
    offset t component 6 s (by decide) (by decide)).trans h6
  have rowIndex := (congrArg (fun indices => indices t 0) values.2.2.2.1).trans h0
  have colIndex := (congrArg (fun indices => indices t 14) values.2.2.2.1).trans h14
  rewrite [show extra+5=(extra+3)+2 by omega,
    exp_store_values_eq p guarded ops (expInputValue ops input row tid iteration component) offset t component
      (extra+3) s hc hp h13 hm h5]
  exact exp_store_emit_eq p guarded ops (expComponentValue ops input offset row tid iteration component) acc
    row (column tid iteration component) t extra _ hr hcol values.1 rowIndex colIndex values.2.1 accValue

theorem exp_store_body_fields (ops : Ops α) (input : Nat → Nat → α) (offset acc : α)
    (row tid iteration component t : Nat) (s : State α) :
    (expStoreBody ops input offset acc row tid iteration component t s).pc t=65 ∧
    (expStoreBody ops input offset acc row tid iteration component t s).regs t 6=
      some (ops.add acc (expComponentValue ops input offset row tid iteration component)) ∧
    (expStoreBody ops input offset acc row tid iteration component t s).epochs=s.epochs ∧
    (expStoreBody ops input offset acc row tid iteration component t s).trace=
      ⟨t,globalCell 0 (address row (column tid iteration component)),true,s.epochs t⟩::
      ⟨t,localCell 0 t component,false,s.epochs t⟩::s.trace := by
  have values := exp_store_values_fields ops (expInputValue ops input row tid iteration component) offset t component s
  have emit := exp_store_emit_fields ops (expComponentValue ops input offset row tid iteration component) acc
    row (column tid iteration component) t
    (expStoreValues ops (expInputValue ops input row tid iteration component) offset t component s)
  refine ⟨emit.1,emit.2.2.1,emit.2.2.2.1.trans values.2.2.2.2.1,?_⟩
  change (expStoreEmit _ _ _ _ _ _ _).trace=_
  rewrite [emit.2.2.2.2,values.2.2.2.2.1,values.2.2.2.2.2]
  rfl

theorem exp_store_body_memory (ops : Ops α) (input : Nat → Nat → α) (offset acc : α)
    (row tid iteration component t : Nat) (s : State α) (l : Location) :
    (expStoreBody ops input offset acc row tid iteration component t s).memory l=
      if l=globalCell 0 (address row (column tid iteration component)) then
        some (ops.toHalf (expComponentValue ops input offset row tid iteration component)) else s.memory l :=
  exp_store_emit_memory ops (expComponentValue ops input offset row tid iteration component) acc
    row (column tid iteration component) t _ l

theorem exp_store_body_index_other (ops : Ops α) (input : Nat → Nat → α) (offset acc : α)
    (row tid iteration component t r : Nat) (s : State α) (hr : r ≠ 15) :
    (expStoreBody ops input offset acc row tid iteration component t s).indices t r=s.indices t r :=
  (exp_store_emit_index_other ops (expComponentValue ops input offset row tid iteration component) acc
    row (column tid iteration component) t r _ hr).trans
    (congrArg (fun indices => indices t r)
      (exp_store_values_fields ops (expInputValue ops input row tid iteration component) offset t component s).2.2.2.1)

theorem exp_store_body_reg_other (ops : Ops α) (input : Nat → Nat → α) (offset acc : α)
    (row tid iteration component t r : Nat) (s : State α) (h6 : r ≠ 6) (h7 : r ≠ 7) (h8 : r ≠ 8) :
    (expStoreBody ops input offset acc row tid iteration component t s).regs t r=s.regs t r :=
  (exp_store_emit_reg_other ops (expComponentValue ops input offset row tid iteration component) acc
    row (column tid iteration component) t r _ h6).trans
    (exp_store_values_reg_other ops (expInputValue ops input row tid iteration component) offset t component r s h7 h8)

theorem exp_store_body_good (ops : Ops α) (input : Nat → Nat → α) (offset acc : α)
    (row tid iteration component t : Nat) (s : State α) (ht : tid<1024)
    (hc : column tid iteration component<50257) (hthread : t=row*1024+tid) (good : ∀ a ∈ s.trace, Good a) :
    ∀ a ∈ (expStoreBody ops input offset acc row tid iteration component t s).trace, Good a :=
  exp_store_emit_good ops (expComponentValue ops input offset row tid iteration component) acc
    row tid iteration component t _ ht hc hthread
    (exp_store_values_good ops (expInputValue ops input row tid iteration component) offset t component s good)

#print axioms exp_store_body_eq
#print axioms exp_store_body_fields
#print axioms exp_store_body_memory
#print axioms exp_store_body_index_other
#print axioms exp_store_body_reg_other
#print axioms exp_store_body_good
end LarkNativeSoftmax
