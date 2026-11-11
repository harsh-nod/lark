import Lark.NativeSoftmaxNormStoreEmit

/-! The actual private read, output-address calculation and converted division
store, followed separately by the component counter and store-loop back-edge. -/
namespace LarkNativeSoftmax
open LarkNonlinear
open LarkReduction (setIndex execute_index_of)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def normStoreBody (guarded : Bool) (ops : Ops α) (value denominator : α)
    (row col component t : Nat) (s : State α) : State α :=
  normStoreEmit guarded ops value denominator row col t (normStoreValue guarded value t component s)

theorem norm_store_body_eq (p : Shape) (guarded : Bool) (ops : Ops α) (value denominator : α)
    (row col component t extra : Nat) (s : State α) (hr : row<p.rows) (hcol : col<50257) (hc : component<8)
    (hp : s.pc t=normPc guarded 108) (h0 : s.indices t 0=some (row : Int))
    (h21 : s.indices t 21=some (component : Int)) (h22 : s.indices t 22=some (col : Int))
    (hm : s.memory (localCell 1 t component)=some value) (h12 : s.regs t 12=some denominator) :
    LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t (extra+3) s=
      LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t extra
        (normStoreBody guarded ops value denominator row col component t s) := by
  have fields := norm_store_value_fields guarded value t component s
  have hd := (norm_store_value_reg_other guarded value t component 12 s (by decide)).trans h12
  rewrite [show extra+3=(extra+2)+1 by omega,
    norm_store_value_eq p guarded ops value t component (extra+2) s hc hp h21 hm]
  exact norm_store_emit_eq p guarded ops value denominator row col t extra _ hr hcol fields.1
    ((congrArg (fun ix => ix t 0) fields.2.2.2.1).trans h0)
    ((congrArg (fun ix => ix t 22) fields.2.2.2.1).trans h22) fields.2.1 hd

theorem norm_store_body_fields (guarded : Bool) (ops : Ops α) (value denominator : α)
    (row col component t : Nat) (s : State α) :
    (normStoreBody guarded ops value denominator row col component t s).pc t=normPc guarded 111 ∧
    (normStoreBody guarded ops value denominator row col component t s).regs t 12=s.regs t 12 ∧
    (normStoreBody guarded ops value denominator row col component t s).epochs=s.epochs ∧
    (normStoreBody guarded ops value denominator row col component t s).trace=
      ⟨t,globalCell 0 (address row col),true,s.epochs t⟩::⟨t,localCell 1 t component,false,s.epochs t⟩::s.trace := by
  simp [normStoreBody,normStoreEmit,normStoreValue,written,record,setIndex,LarkReduction.setReg,advance]

theorem norm_store_body_memory (guarded : Bool) (ops : Ops α) (value denominator : α)
    (row col component t : Nat) (s : State α) (l : Location) :
    (normStoreBody guarded ops value denominator row col component t s).memory l=
      if l=globalCell 0 (address row col) then some (ops.toHalf (ops.div value denominator)) else s.memory l := rfl

theorem norm_store_body_index_other (guarded : Bool) (ops : Ops α) (value denominator : α)
    (row col component t r : Nat) (s : State α) (hr : r ≠ 23) :
    (normStoreBody guarded ops value denominator row col component t s).indices t r=s.indices t r :=
  (norm_store_emit_index_other guarded ops value denominator row col t r _ hr).trans rfl

def normStoreNext (guarded : Bool) (t component : Nat) (s : State α) : State α :=
  advance (setIndex s t 21 ((component+1 : Nat) : Int) (normPc guarded 112)) t (normPc guarded 105)

theorem norm_store_next_eq (p : Shape) (guarded : Bool) (ops : Ops α)
    (t component extra : Nat) (s : State α) (hc : component<8)
    (hp : s.pc t=normPc guarded 111) (hi : s.indices t 21=some (component : Int)) :
    LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t (extra+2) s=
      LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t extra (normStoreNext guarded t component s) := by
  let next := setIndex s t 21 ((component+1 : Nat) : Int) (normPc guarded 112)
  have ix := eval_nat_sum (geometry p) t component 1 s (.ivar 21) (.const 1) hi rfl (by omega)
  have e1 := execute_index_of ops (layout p) (geometry p) t 21 (normPc guarded 112)
    (.add (.ivar 21) (.const 1)) s _ ix ((congrArg (·+1) hp).trans (norm_pc_next guarded 111).symm)
  have e2 : execute ops (layout p) (geometry p) t (.jump (normPc guarded 105)) next=
      some (normStoreNext guarded t component s) := rfl
  rewrite [show extra+2=(extra+1)+1 by omega,
    scalar_step p guarded ops t (normPc guarded 111) _ _ s next (norm_store_emit_codes guarded).2.2.1 hp e1]
  exact scalar_step p guarded ops t (normPc guarded 112) extra _ next _ (norm_store_emit_codes guarded).2.2.2
    (by simp [next,setIndex,advance]) e2

theorem norm_store_next_fields (guarded : Bool) (t component : Nat) (s : State α) :
    (normStoreNext guarded t component s).pc t=normPc guarded 105 ∧
    (normStoreNext guarded t component s).indices t 21=some ((component+1 : Nat) : Int) ∧
    (normStoreNext guarded t component s).memory=s.memory ∧
    (normStoreNext guarded t component s).regs=s.regs ∧
    (normStoreNext guarded t component s).epochs=s.epochs ∧
    (normStoreNext guarded t component s).trace=s.trace := by simp [normStoreNext,setIndex,advance]

theorem norm_store_next_index_other (guarded : Bool) (t component r : Nat) (s : State α) (hr : r ≠ 21) :
    (normStoreNext guarded t component s).indices t r=s.indices t r := by simp [normStoreNext,setIndex,advance,hr]

theorem norm_store_body_other (guarded : Bool) (ops : Ops α) (value denominator : α)
    (row col component t u : Nat) (s : State α) (hu : u ≠ t) :
    OtherThread t u s (normStoreBody guarded ops value denominator row col component t s) :=
  other_thread_trans t u _ _ _ (norm_store_value_other guarded value t component u s hu)
    (norm_store_emit_other guarded ops value denominator row col t u _ hu)

theorem norm_store_next_other (guarded : Bool) (t component u : Nat) (s : State α) (hu : u ≠ t) :
    OtherThread t u s (normStoreNext guarded t component s) := by simp [OtherThread,normStoreNext,setIndex,advance,hu]

#print axioms norm_store_body_eq
#print axioms norm_store_body_fields
#print axioms norm_store_body_memory
#print axioms norm_store_body_index_other
#print axioms norm_store_next_eq
#print axioms norm_store_next_fields
#print axioms norm_store_next_index_other
#print axioms norm_store_body_other
#print axioms norm_store_next_other
end LarkNativeSoftmax
