import Lark.NativeSoftmaxExpStoreValue

/-! Actual output address, converted global store, and unrounded sum update.
The stored scalar uses toHalf; the accumulator uses the original exponential.
No algebraic or IEEE properties of those operations are assumed. -/
namespace LarkNativeSoftmax
open LarkNonlinear
open LarkReduction (setIndex setReg execute_index_of execute_pure_of)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem exp_output_location_of (l : Layout) (g : Geometry) (t offset size : Nat)
    (hl : l.global[0]?=some ⟨.output,size⟩) (hb : offset<size) :
    location l g t .global 0 (offset : Int) true=some (globalCell 0 offset) := by
  simp [location,hl,globalCell,hb,show (Role.output == Role.input)=false by rfl]

theorem exp_output_location (p : Shape) (t offset : Nat) (hb : offset<p.rows*50257) :
    location (layout p) (geometry p) t .global 0 (offset : Int) true=some (globalCell 0 offset) :=
  exp_output_location_of (layout p) (geometry p) t offset (p.rows*50257) rfl hb

theorem eval_exp_store_address (p : Shape) (t row col : Nat) (s : State α)
    (hr : row<p.rows) (hc : col<50257) (h0 : s.indices t 0=some (row : Int))
    (h14 : s.indices t 14=some (col : Int)) :
    evalIndex (geometry p) t s (.add (.mul (.ivar 0) (.const 50257)) (.ivar 14))=
      some ((address row col : Nat) : Int) := by
  have hb := p.bound
  have hm := eval_nat_mul (geometry p) t row 50257 s (.ivar 0) h0 (by decide) (by omega)
  exact eval_nat_sum (geometry p) t (row*50257) col s _ _ hm h14 (by omega)

theorem exp_half_eval_of (ops : Ops α) (l : Layout) (g : Geometry) (t : Nat) (value : α) (s : State α)
    (h8 : s.regs t 8=some value) :
    evalExpr ops l g t (.un .toHalf (.reg 8)) s=some (ops.toHalf value,s) := by
  simp only [evalExpr,h8,applyUnary,bind,pure,Option.bind]

theorem exp_sum_eval_of (ops : Ops α) (l : Layout) (g : Geometry) (t : Nat) (value acc : α) (s : State α)
    (h6 : s.regs t 6=some acc) (h8 : s.regs t 8=some value) :
    evalExpr ops l g t (.bin .add (.reg 6) (.reg 8)) s=some (ops.add acc value,s) := by
  simp only [evalExpr,h6,h8,applyBinary,bind,pure,Option.bind]

def expStoreEmit (ops : Ops α) (value acc : α) (row col t : Nat) (s : State α) : State α :=
  let s := setIndex s t 15 ((address row col : Nat) : Int) 63
  let s := written t 64 (globalCell 0 (address row col)) (ops.toHalf value) s
  setReg s t 6 (ops.add acc value) 65

theorem exp_store_emit_eq (p : Shape) (guarded : Bool) (ops : Ops α) (value acc : α)
    (row col t extra : Nat) (s : State α) (hr : row<p.rows) (hc : col<50257)
    (hp : s.pc t=62) (h0 : s.indices t 0=some (row : Int)) (h14 : s.indices t 14=some (col : Int))
    (h8 : s.regs t 8=some value) (h6 : s.regs t 6=some acc) :
    LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t (extra+3) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t extra
        (expStoreEmit ops value acc row col t s) := by
  let s1 := setIndex s t 15 ((address row col : Nat) : Int) 63
  let s2 := written t 64 (globalCell 0 (address row col)) (ops.toHalf value) s1
  have ix := eval_exp_store_address p t row col s hr hc h0 h14
  have e1 := execute_index_of ops (layout p) (geometry p) t 15 63
    (.add (.mul (.ivar 0) (.const 50257)) (.ivar 14)) s _ ix (by omega)
  change execute _ _ _ _ _ s=some s1 at e1
  have h81 : s1.regs t 8=some value := h8
  have h15 : s1.indices t 15=some ((address row col : Nat) : Int) := by simp [s1,setIndex,advance]
  have e2 := execute_store_effect ops (layout p) (geometry p) t 64 .global 0 (.ivar 15)
    (.un .toHalf (.reg 8)) s1 s1 _ (globalCell 0 (address row col)) (ops.toHalf value)
    h15 (exp_output_location p t _ (address_bound p row col hr hc))
    (exp_half_eval_of ops (layout p) (geometry p) t value s1 h81) (by simp [s1,setIndex,advance])
  change execute _ _ _ _ _ s1=some s2 at e2
  have h62 : s2.regs t 6=some acc := h6
  have h82 : s2.regs t 8=some value := h8
  have e3 := execute_pure_of ops (layout p) (geometry p) t 6 65 (.bin .add (.reg 6) (.reg 8)) s2 (ops.add acc value)
    (exp_sum_eval_of ops (layout p) (geometry p) t value acc s2 h62 h82)
    (by simp [s2,written,record,advance])
  rewrite [show extra+3=(extra+2)+1 by omega,
    scalar_step p guarded ops t 62 _ _ s s1 (by cases guarded <;> rfl) hp e1]
  rewrite [show extra+2=(extra+1)+1 by omega,
    scalar_step p guarded ops t 63 _ _ s1 s2 (by cases guarded <;> rfl) (by simp [s1,setIndex,advance]) e2]
  exact scalar_step p guarded ops t 64 extra _ s2 _ (by cases guarded <;> rfl)
    (by simp [s2,written,record,advance]) e3

theorem exp_store_emit_fields (ops : Ops α) (value acc : α) (row col t : Nat) (s : State α) :
    (expStoreEmit ops value acc row col t s).pc t=65 ∧
    (expStoreEmit ops value acc row col t s).indices t 15=some ((address row col : Nat) : Int) ∧
    (expStoreEmit ops value acc row col t s).regs t 6=some (ops.add acc value) ∧
    (expStoreEmit ops value acc row col t s).epochs=s.epochs ∧
    (expStoreEmit ops value acc row col t s).trace=⟨t,globalCell 0 (address row col),true,s.epochs t⟩::s.trace := by
  simp [expStoreEmit,setIndex,setReg,written,record,advance]

theorem exp_store_emit_memory (ops : Ops α) (value acc : α) (row col t : Nat) (s : State α) (l : Location) :
    (expStoreEmit ops value acc row col t s).memory l=
      if l=globalCell 0 (address row col) then some (ops.toHalf value) else s.memory l := rfl

theorem exp_store_emit_reg_other (ops : Ops α) (value acc : α) (row col t r : Nat) (s : State α) (hr : r ≠ 6) :
    (expStoreEmit ops value acc row col t s).regs t r=s.regs t r := by
  simp [expStoreEmit,setIndex,setReg,written,record,advance,hr]

theorem exp_store_emit_index_other (ops : Ops α) (value acc : α) (row col t r : Nat) (s : State α) (hr : r ≠ 15) :
    (expStoreEmit ops value acc row col t s).indices t r=s.indices t r := by
  simp [expStoreEmit,setIndex,setReg,written,record,advance,hr]

theorem exp_store_emit_other (ops : Ops α) (value acc : α) (row col t u : Nat) (s : State α) (hu : u ≠ t) :
    OtherThread t u s (expStoreEmit ops value acc row col t s) := by
  simp [OtherThread,expStoreEmit,setIndex,setReg,written,record,advance,hu]

theorem exp_store_emit_good (ops : Ops α) (value acc : α) (row tid iteration component t : Nat) (s : State α)
    (ht : tid<1024) (hc : column tid iteration component<50257) (hthread : t=row*1024+tid)
    (good : ∀ a ∈ s.trace, Good a) :
    ∀ a ∈ (expStoreEmit ops value acc row (column tid iteration component) t s).trace, Good a := by
  intro a ha
  rewrite [(exp_store_emit_fields ops value acc row (column tid iteration component) t s).2.2.2.2] at ha
  rcases List.mem_cons.mp ha with rfl | ha
  · exact Good.output rfl rfl rfl (hthread.trans (address_writer row tid iteration component ht hc).symm)
  · exact good a ha

#print axioms exp_output_location_of
#print axioms exp_output_location
#print axioms eval_exp_store_address
#print axioms exp_half_eval_of
#print axioms exp_sum_eval_of
#print axioms exp_store_emit_eq
#print axioms exp_store_emit_fields
#print axioms exp_store_emit_memory
#print axioms exp_store_emit_reg_other
#print axioms exp_store_emit_index_other
#print axioms exp_store_emit_other
#print axioms exp_store_emit_good
end LarkNativeSoftmax
