import Lark.NativeSoftmaxNormStoreBody

/-! One complete actual normalization output component for either source.
Valid stores use eight instructions and two accesses; invalid components use
five instructions and make no accesses. This is still a component obligation. -/
namespace LarkNativeSoftmax
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def normStoreMiddle (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component : Nat) (s : State α) : State α :=
  let head := normStoreHead guarded tid iteration component (row*1024+tid) s
  if column tid iteration component<50257 then
    normStoreBody guarded ops (ops.fromHalf (expOutputValue ops input row (column tid iteration component)))
      (rowExpSum ops input row) row (column tid iteration component) component (row*1024+tid) head
  else head

def normStoreAfter (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component : Nat) (s : State α) : State α :=
  normStoreNext guarded (row*1024+tid) component (normStoreMiddle guarded ops input row tid iteration component s)

def normStoreCost (tid iteration component : Nat) : Nat := if column tid iteration component<50257 then 8 else 5

theorem norm_store_middle_pc (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component : Nat) (s : State α) :
    (normStoreMiddle guarded ops input row tid iteration component s).pc (row*1024+tid)=normPc guarded 111 := by
  by_cases hc : column tid iteration component<50257
  · simp only [normStoreMiddle,if_pos hc]
    exact (norm_store_body_fields guarded ops _ _ row _ component (row*1024+tid) _).1
  · simpa only [normStoreMiddle,if_neg hc] using
      (norm_store_head_fields guarded tid iteration component (row*1024+tid) s).1

theorem norm_store_middle_index_other (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component r : Nat) (s : State α) (h22 : r ≠ 22) (h23 : r ≠ 23) :
    (normStoreMiddle guarded ops input row tid iteration component s).indices (row*1024+tid) r=s.indices (row*1024+tid) r := by
  by_cases hc : column tid iteration component<50257
  · simp only [normStoreMiddle,if_pos hc]
    exact (norm_store_body_index_other guarded ops _ _ row _ component (row*1024+tid) r _ h23).trans
      (norm_store_head_index_other guarded tid iteration component (row*1024+tid) r s h22)
  · simpa only [normStoreMiddle,if_neg hc] using
      norm_store_head_index_other guarded tid iteration component (row*1024+tid) r s h22

theorem norm_store_component_eq (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component extra : Nat) (s : State α) (hi : iteration<7) (hc : component<8)
    (ready : NormStoreReady p guarded ops input row tid iteration component s) :
    LarkCollective.runLane ops (layout p) (geometry p) (program guarded) (row*1024+tid)
      (extra+normStoreCost tid iteration component) s=
      LarkCollective.runLane ops (layout p) (geometry p) (program guarded) (row*1024+tid) extra
        (normStoreAfter guarded ops input row tid iteration component s) := by
  let t := row*1024+tid
  let col := column tid iteration component
  let head := normStoreHead guarded tid iteration component t s
  have hf := norm_store_head_fields guarded tid iteration component t s
  have hi21 : head.indices t 21=some (component : Int) :=
    (norm_store_head_index_other guarded tid iteration component t 21 s (by decide)).trans ready.componentIndex
  by_cases hcol : col<50257
  · dsimp only [col] at hcol
    let value := ops.fromHalf (expOutputValue ops input row col)
    let denominator := rowExpSum ops input row
    let body := normStoreBody guarded ops value denominator row col component t head
    have hp : head.pc t=normPc guarded 108 := by simpa only [if_pos hcol] using hf.1
    have ht := ready.bound
    have hr : t/1024=row := by dsimp only [t]; omega
    have h0 : s.indices t 0=some (row : Int) := by
      have hn := ready.native.1
      change s.indices t 0=some ((t/1024 : Nat) : Int) at hn
      simpa only [hr] using hn
    have hh0 := (norm_store_head_index_other guarded tid iteration component t 0 s (by decide)).trans h0
    have hm : head.memory (localCell 1 t component)=some value :=
      (congrFun (norm_store_head_frames guarded tid iteration component t s).1 _).trans (ready.buffered component hc hcol)
    have hd := (congrArg (fun regs => regs t 12) (norm_store_head_frames guarded tid iteration component t s).2.1).trans ready.denominator
    have hb21 : body.indices t 21=some (component : Int) :=
      (norm_store_body_index_other guarded ops value denominator row col component t 21 head (by decide)).trans hi21
    rewrite [show extra+normStoreCost tid iteration component=((extra+2)+3)+3 by
      simp only [normStoreCost,if_pos hcol],
      norm_store_head_eq p guarded ops tid iteration component t _ s ready.bound hi hc ready.pc ready.base ready.componentIndex,
      norm_store_body_eq p guarded ops value denominator row col component t (extra+2) head ready.valid hcol hc hp hh0 hi21 hf.2 hm hd]
    have tail := norm_store_next_eq p guarded ops t component extra body hc
      (norm_store_body_fields guarded ops value denominator row col component t head).1 hb21
    simpa only [normStoreAfter,normStoreMiddle,if_pos hcol] using tail
  · dsimp only [col] at hcol
    have hp : head.pc t=normPc guarded 111 := by simpa only [if_neg hcol] using hf.1
    rewrite [show extra+normStoreCost tid iteration component=(extra+2)+3 by
      simp only [normStoreCost,if_neg hcol],
      norm_store_head_eq p guarded ops tid iteration component t _ s ready.bound hi hc ready.pc ready.base ready.componentIndex]
    have tail := norm_store_next_eq p guarded ops t component extra head hc hp hi21
    simpa only [normStoreAfter,normStoreMiddle,if_neg hcol] using tail

theorem norm_store_component_fields (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component : Nat) (s : State α) :
    (normStoreAfter guarded ops input row tid iteration component s).pc (row*1024+tid)=normPc guarded 105 ∧
    (normStoreAfter guarded ops input row tid iteration component s).indices (row*1024+tid) 21=some ((component+1 : Nat) : Int) := by
  exact ⟨(norm_store_next_fields guarded (row*1024+tid) component _).1,
    (norm_store_next_fields guarded (row*1024+tid) component _).2.1⟩

theorem norm_store_component_memory (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component : Nat) (s : State α) (l : Location) :
    (normStoreAfter guarded ops input row tid iteration component s).memory l=
      if column tid iteration component<50257 then
        if l=globalCell 0 (address row (column tid iteration component)) then
          some (normOutputValue ops input row (column tid iteration component)) else s.memory l
      else s.memory l := by
  by_cases hc : column tid iteration component<50257 <;>
    simp [normStoreAfter,normStoreMiddle,hc,normStoreNext,LarkReduction.setIndex,advance,norm_store_body_memory,
      (norm_store_head_frames guarded tid iteration component (row*1024+tid) s).1,normOutputValue]

theorem norm_store_component_index_other (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component r : Nat) (s : State α) (h21 : r ≠ 21) (h22 : r ≠ 22) (h23 : r ≠ 23) :
    (normStoreAfter guarded ops input row tid iteration component s).indices (row*1024+tid) r=s.indices (row*1024+tid) r :=
  (norm_store_next_index_other guarded (row*1024+tid) component r _ h21).trans
    (norm_store_middle_index_other guarded ops input row tid iteration component r s h22 h23)

theorem norm_store_component_denominator (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component : Nat) (s : State α) :
    (normStoreAfter guarded ops input row tid iteration component s).regs (row*1024+tid) 12=s.regs (row*1024+tid) 12 := by
  by_cases hc : column tid iteration component<50257 <;>
    simp [normStoreAfter,normStoreMiddle,hc,normStoreNext,LarkReduction.setIndex,advance,
      (norm_store_body_fields guarded ops _ _ row _ component (row*1024+tid) _).2.1,
      (norm_store_head_frames guarded tid iteration component (row*1024+tid) s).2.1]

theorem norm_store_component_epochs (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component : Nat) (s : State α) :
    (normStoreAfter guarded ops input row tid iteration component s).epochs=s.epochs := by
  by_cases hc : column tid iteration component<50257 <;>
    simp [normStoreAfter,normStoreMiddle,hc,normStoreNext,LarkReduction.setIndex,advance,
      (norm_store_body_fields guarded ops _ _ row _ component (row*1024+tid) _).2.2.1,
      (norm_store_head_frames guarded tid iteration component (row*1024+tid) s).2.2.1]

theorem norm_store_component_trace (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component : Nat) (s : State α) :
    (normStoreAfter guarded ops input row tid iteration component s).trace=
      if column tid iteration component<50257 then
        ⟨row*1024+tid,globalCell 0 (address row (column tid iteration component)),true,s.epochs (row*1024+tid)⟩::
          ⟨row*1024+tid,localCell 1 (row*1024+tid) component,false,s.epochs (row*1024+tid)⟩::s.trace
      else s.trace := by
  by_cases hc : column tid iteration component<50257 <;>
    simp [normStoreAfter,normStoreMiddle,hc,normStoreNext,LarkReduction.setIndex,advance,
      (norm_store_body_fields guarded ops _ _ row _ component (row*1024+tid) _).2.2.2,
      (norm_store_head_frames guarded tid iteration component (row*1024+tid) s).2.2.1,
      (norm_store_head_frames guarded tid iteration component (row*1024+tid) s).2.2.2]

theorem norm_store_component_good (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component : Nat) (s : State α) (ht : tid<1024) (good : ∀ a ∈ s.trace, Good a) :
    ∀ a ∈ (normStoreAfter guarded ops input row tid iteration component s).trace, Good a := by
  intro a ha
  rewrite [norm_store_component_trace] at ha
  by_cases hc : column tid iteration component<50257
  · rewrite [if_pos hc] at ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact Good.output rfl rfl rfl (address_writer row tid iteration component ht hc).symm
    · rcases List.mem_cons.mp ha with rfl | ha
      · exact Good.privateAccess rfl rfl
      · exact good a ha
  · rewrite [if_neg hc] at ha
    exact good a ha

#print axioms norm_store_middle_pc
#print axioms norm_store_middle_index_other
#print axioms norm_store_component_eq
#print axioms norm_store_component_fields
#print axioms norm_store_component_memory
#print axioms norm_store_component_index_other
#print axioms norm_store_component_denominator
#print axioms norm_store_component_epochs
#print axioms norm_store_component_trace
#print axioms norm_store_component_good
end LarkNativeSoftmax
