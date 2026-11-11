import Lark.NativeSoftmaxNormStoreValue

/-! Actual normalization output address and toHalf(value/rowSum) store. The
division operand order and both preceding half conversions stay explicit. -/
namespace LarkNativeSoftmax
open LarkNonlinear
open LarkReduction (setIndex execute_index_of)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def normOutputValue (ops : Ops α) (input : Nat → Nat → α) (row col : Nat) : α :=
  ops.toHalf (ops.div (ops.fromHalf (expOutputValue ops input row col)) (rowExpSum ops input row))

theorem eval_norm_store_address (p : Shape) (t row col : Nat) (s : State α)
    (hr : row<p.rows) (hc : col<50257) (h0 : s.indices t 0=some (row : Int))
    (h22 : s.indices t 22=some (col : Int)) :
    evalIndex (geometry p) t s (.add (.mul (.ivar 0) (.const 50257)) (.ivar 22))=
      some ((address row col : Nat) : Int) := by
  have hb := p.bound
  have hm := eval_nat_mul (geometry p) t row 50257 s (.ivar 0) h0 (by decide) (by omega)
  exact eval_nat_sum (geometry p) t (row*50257) col s _ _ hm h22 (by omega)

theorem norm_div_output_eval_of (ops : Ops α) (l : Layout) (g : Geometry) (t : Nat)
    (value denominator : α) (s : State α) (h13 : s.regs t 13=some value) (h12 : s.regs t 12=some denominator) :
    evalExpr ops l g t (.un .toHalf (.bin .div (.reg 13) (.reg 12))) s=
      some (ops.toHalf (ops.div value denominator),s) := by
  simp only [evalExpr,h13,h12,applyBinary,applyUnary,bind,pure,Option.bind]

def normStoreEmit (guarded : Bool) (ops : Ops α) (value denominator : α) (row col t : Nat) (s : State α) : State α :=
  written t (normPc guarded 111) (globalCell 0 (address row col)) (ops.toHalf (ops.div value denominator))
    (setIndex s t 23 ((address row col : Nat) : Int) (normPc guarded 110))

theorem norm_store_emit_eq (p : Shape) (guarded : Bool) (ops : Ops α) (value denominator : α)
    (row col t extra : Nat) (s : State α) (hr : row<p.rows) (hc : col<50257)
    (hp : s.pc t=normPc guarded 109) (h0 : s.indices t 0=some (row : Int))
    (h22 : s.indices t 22=some (col : Int)) (h13 : s.regs t 13=some value) (h12 : s.regs t 12=some denominator) :
    LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t (extra+2) s=
      LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t extra
        (normStoreEmit guarded ops value denominator row col t s) := by
  let s1 := setIndex s t 23 ((address row col : Nat) : Int) (normPc guarded 110)
  have ix := eval_norm_store_address p t row col s hr hc h0 h22
  have e1 := execute_index_of ops (layout p) (geometry p) t 23 (normPc guarded 110)
    (.add (.mul (.ivar 0) (.const 50257)) (.ivar 22)) s _ ix
    ((congrArg (·+1) hp).trans (norm_pc_next guarded 109).symm)
  change execute _ _ _ _ _ s=some s1 at e1
  have h23 : s1.indices t 23=some ((address row col : Nat) : Int) := by simp [s1,setIndex,advance]
  have e2 := execute_store_effect ops (layout p) (geometry p) t (normPc guarded 111) .global 0 (.ivar 23)
    (.un .toHalf (.bin .div (.reg 13) (.reg 12))) s1 s1 _ (globalCell 0 (address row col)) _
    h23 (exp_output_location p t _ (address_bound p row col hr hc))
    (norm_div_output_eval_of ops (layout p) (geometry p) t value denominator s1 h13 h12)
    (by simp only [s1,setIndex,advance,↓reduceIte]; exact (norm_pc_next guarded 110).symm)
  rewrite [show extra+2=(extra+1)+1 by omega,
    scalar_step p guarded ops t (normPc guarded 109) _ _ s s1 (norm_store_emit_codes guarded).1 hp e1]
  exact scalar_step p guarded ops t (normPc guarded 110) extra _ s1 _ (norm_store_emit_codes guarded).2.1
    (by simp [s1,setIndex,advance]) e2

theorem norm_store_emit_fields (guarded : Bool) (ops : Ops α) (value denominator : α)
    (row col t : Nat) (s : State α) :
    (normStoreEmit guarded ops value denominator row col t s).pc t=normPc guarded 111 ∧
    (normStoreEmit guarded ops value denominator row col t s).indices t 23=some ((address row col : Nat) : Int) ∧
    (normStoreEmit guarded ops value denominator row col t s).regs=s.regs ∧
    (normStoreEmit guarded ops value denominator row col t s).epochs=s.epochs ∧
    (normStoreEmit guarded ops value denominator row col t s).trace=⟨t,globalCell 0 (address row col),true,s.epochs t⟩::s.trace := by
  simp [normStoreEmit,written,record,setIndex,advance]

theorem norm_store_emit_memory (guarded : Bool) (ops : Ops α) (value denominator : α)
    (row col t : Nat) (s : State α) (l : Location) :
    (normStoreEmit guarded ops value denominator row col t s).memory l=
      if l=globalCell 0 (address row col) then some (ops.toHalf (ops.div value denominator)) else s.memory l := rfl

theorem norm_store_emit_index_other (guarded : Bool) (ops : Ops α) (value denominator : α)
    (row col t r : Nat) (s : State α) (hr : r ≠ 23) :
    (normStoreEmit guarded ops value denominator row col t s).indices t r=s.indices t r := by
  simp [normStoreEmit,written,record,setIndex,advance,hr]

theorem norm_store_emit_other (guarded : Bool) (ops : Ops α) (value denominator : α)
    (row col t u : Nat) (s : State α) (hu : u ≠ t) :
    OtherThread t u s (normStoreEmit guarded ops value denominator row col t s) := by
  simp [OtherThread,normStoreEmit,written,record,setIndex,advance,hu]

theorem norm_store_emit_good (guarded : Bool) (ops : Ops α) (value denominator : α)
    (row tid iteration component : Nat) (s : State α) (ht : tid<1024) (hc : column tid iteration component<50257)
    (good : ∀ a ∈ s.trace, Good a) :
    ∀ a ∈ (normStoreEmit guarded ops value denominator row (column tid iteration component) (row*1024+tid) s).trace, Good a := by
  intro a ha
  rewrite [(norm_store_emit_fields guarded ops value denominator row (column tid iteration component) (row*1024+tid) s).2.2.2.2] at ha
  rcases List.mem_cons.mp ha with rfl | ha
  · exact Good.output rfl rfl rfl (address_writer row tid iteration component ht hc).symm
  · exact good a ha

#print axioms eval_norm_store_address
#print axioms norm_div_output_eval_of
#print axioms norm_store_emit_eq
#print axioms norm_store_emit_fields
#print axioms norm_store_emit_memory
#print axioms norm_store_emit_index_other
#print axioms norm_store_emit_other
#print axioms norm_store_emit_good
end LarkNativeSoftmax
