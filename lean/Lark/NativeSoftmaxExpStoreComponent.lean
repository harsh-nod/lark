import Lark.NativeSoftmaxExpStoreBody

/-! Complete actual exponential output component. Valid columns consume ten
instructions and produce a private read plus an output write. Invalid columns
consume five instructions, preserve the sum and make no accesses. -/
namespace LarkNativeSoftmax
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def expStoreMiddle (ops : Ops α) (input : Nat → Nat → α) (offset acc : α)
    (row tid iteration component t : Nat) (s : State α) : State α :=
  if column tid iteration component<50257 then
    expStoreBody ops input offset acc row tid iteration component t (expStoreHead tid iteration component t s)
  else expStoreHead tid iteration component t s

def expStoreAfter (ops : Ops α) (input : Nat → Nat → α) (offset acc : α)
    (row tid iteration component t : Nat) (s : State α) : State α :=
  expStoreNext t component (expStoreMiddle ops input offset acc row tid iteration component t s)

def expStoreAcc (ops : Ops α) (input : Nat → Nat → α) (offset acc : α)
    (row tid iteration component : Nat) : α :=
  if column tid iteration component<50257 then ops.add acc (expComponentValue ops input offset row tid iteration component)
  else acc

def expStoreCost (tid iteration component : Nat) : Nat :=
  if column tid iteration component<50257 then 10 else 5

theorem exp_store_middle_pc (ops : Ops α) (input : Nat → Nat → α) (offset acc : α)
    (row tid iteration component t : Nat) (s : State α) :
    (expStoreMiddle ops input offset acc row tid iteration component t s).pc t=65 := by
  by_cases hc : column tid iteration component<50257
  · simp only [expStoreMiddle,if_pos hc]
    exact (exp_store_body_fields ops input offset acc row tid iteration component t _).1
  · simpa only [expStoreMiddle,if_neg hc] using (exp_store_head_fields tid iteration component t s).1

theorem exp_store_middle_index_other (ops : Ops α) (input : Nat → Nat → α) (offset acc : α)
    (row tid iteration component t r : Nat) (s : State α) (h14 : r ≠ 14) (h15 : r ≠ 15) :
    (expStoreMiddle ops input offset acc row tid iteration component t s).indices t r=s.indices t r := by
  by_cases hc : column tid iteration component<50257
  · simp only [expStoreMiddle,if_pos hc]
    exact (exp_store_body_index_other ops input offset acc row tid iteration component t r _ h15).trans
      (exp_store_head_index_other tid iteration component t r s h14)
  · simpa only [expStoreMiddle,if_neg hc] using exp_store_head_index_other tid iteration component t r s h14

theorem exp_store_middle_reg_other (ops : Ops α) (input : Nat → Nat → α) (offset acc : α)
    (row tid iteration component t r : Nat) (s : State α) (h6 : r ≠ 6) (h7 : r ≠ 7) (h8 : r ≠ 8) :
    (expStoreMiddle ops input offset acc row tid iteration component t s).regs t r=s.regs t r := by
  have head := congrArg (fun regs => regs t r) (exp_store_head_fields tid iteration component t s).2.2.2.1
  by_cases hc : column tid iteration component<50257
  · simpa only [expStoreMiddle,if_pos hc] using
      (exp_store_body_reg_other ops input offset acc row tid iteration component t r _ h6 h7 h8).trans head
  · simpa only [expStoreMiddle,if_neg hc] using head

theorem exp_store_middle_acc (ops : Ops α) (input : Nat → Nat → α) (offset acc : α)
    (row tid iteration component t : Nat) (s : State α) (ha : s.regs t 6=some acc) :
    (expStoreMiddle ops input offset acc row tid iteration component t s).regs t 6=
      some (expStoreAcc ops input offset acc row tid iteration component) := by
  by_cases hc : column tid iteration component<50257
  · simpa only [expStoreMiddle,expStoreAcc,if_pos hc] using
      (exp_store_body_fields ops input offset acc row tid iteration component t _).2.1
  · simpa only [expStoreMiddle,expStoreAcc,if_neg hc] using
      (congrArg (fun regs => regs t 6) (exp_store_head_fields tid iteration component t s).2.2.2.1).trans ha

theorem exp_store_after_pc (ops : Ops α) (input : Nat → Nat → α) (offset acc : α)
    (row tid iteration component t : Nat) (s : State α) :
    (expStoreAfter ops input offset acc row tid iteration component t s).pc t=57 :=
  (exp_store_next_fields t component _).1

theorem exp_store_after_component (ops : Ops α) (input : Nat → Nat → α) (offset acc : α)
    (row tid iteration component t : Nat) (s : State α) :
    (expStoreAfter ops input offset acc row tid iteration component t s).indices t 13=some ((component+1 : Nat) : Int) :=
  (exp_store_next_fields t component _).2.1

theorem exp_store_after_index_other (ops : Ops α) (input : Nat → Nat → α) (offset acc : α)
    (row tid iteration component t r : Nat) (s : State α) (h13 : r ≠ 13) (h14 : r ≠ 14) (h15 : r ≠ 15) :
    (expStoreAfter ops input offset acc row tid iteration component t s).indices t r=s.indices t r :=
  (exp_store_next_index_other t component r _ h13).trans
    (exp_store_middle_index_other ops input offset acc row tid iteration component t r s h14 h15)

theorem exp_store_after_maximum (ops : Ops α) (input : Nat → Nat → α) (offset acc : α)
    (row tid iteration component t : Nat) (s : State α) :
    (expStoreAfter ops input offset acc row tid iteration component t s).regs t 5=s.regs t 5 :=
  (congrArg (fun regs => regs t 5) (exp_store_next_fields t component _).2.2.2.1).trans
    (exp_store_middle_reg_other ops input offset acc row tid iteration component t 5 s (by decide) (by decide) (by decide))

theorem exp_store_after_acc (ops : Ops α) (input : Nat → Nat → α) (offset acc : α)
    (row tid iteration component t : Nat) (s : State α) (ha : s.regs t 6=some acc) :
    (expStoreAfter ops input offset acc row tid iteration component t s).regs t 6=
      some (expStoreAcc ops input offset acc row tid iteration component) :=
  (congrArg (fun regs => regs t 6) (exp_store_next_fields t component _).2.2.2.1).trans
    (exp_store_middle_acc ops input offset acc row tid iteration component t s ha)

theorem exp_store_after_memory (ops : Ops α) (input : Nat → Nat → α) (offset acc : α)
    (row tid iteration component t : Nat) (s : State α) (l : Location) :
    (expStoreAfter ops input offset acc row tid iteration component t s).memory l=
      if column tid iteration component<50257 then
        if l=globalCell 0 (address row (column tid iteration component)) then
          some (ops.toHalf (expComponentValue ops input offset row tid iteration component)) else s.memory l
      else s.memory l := by
  change (expStoreNext t component _).memory l=_
  rewrite [(exp_store_next_fields t component _).2.2.1]
  by_cases hc : column tid iteration component<50257
  · simp only [expStoreMiddle,if_pos hc]
    rewrite [exp_store_body_memory,(exp_store_head_fields tid iteration component t s).2.2.1]
    rfl
  · simp only [expStoreMiddle,if_neg hc]
    exact congrArg (fun memory => memory l) (exp_store_head_fields tid iteration component t s).2.2.1

theorem exp_store_after_memory_other (ops : Ops α) (input : Nat → Nat → α) (offset acc : α)
    (row tid iteration component t : Nat) (s : State α) (l : Location)
    (hl : l ≠ globalCell 0 (address row (column tid iteration component))) :
    (expStoreAfter ops input offset acc row tid iteration component t s).memory l=s.memory l := by
  rewrite [exp_store_after_memory]
  split <;> simp only [if_neg hl]

theorem exp_store_after_epochs (ops : Ops α) (input : Nat → Nat → α) (offset acc : α)
    (row tid iteration component t : Nat) (s : State α) :
    (expStoreAfter ops input offset acc row tid iteration component t s).epochs=s.epochs := by
  have head := (exp_store_head_fields tid iteration component t s).2.2.2.2.1
  change (expStoreNext t component _).epochs=_
  rewrite [(exp_store_next_fields t component _).2.2.2.2.1]
  by_cases hc : column tid iteration component<50257
  · simpa only [expStoreMiddle,if_pos hc] using
      (exp_store_body_fields ops input offset acc row tid iteration component t _).2.2.1.trans head
  · simpa only [expStoreMiddle,if_neg hc] using head

theorem exp_store_after_trace_length (ops : Ops α) (input : Nat → Nat → α) (offset acc : α)
    (row tid iteration component t : Nat) (s : State α) :
    (expStoreAfter ops input offset acc row tid iteration component t s).trace.length=
      s.trace.length+(if column tid iteration component<50257 then 2 else 0) := by
  change (expStoreNext t component _).trace.length=_
  rewrite [(exp_store_next_fields t component _).2.2.2.2.2]
  by_cases hc : column tid iteration component<50257
  · simp only [expStoreMiddle,if_pos hc]
    rewrite [(exp_store_body_fields ops input offset acc row tid iteration component t _).2.2.2,
      (exp_store_head_fields tid iteration component t s).2.2.2.2.2]
    simp only [List.length_cons]
  · simpa only [expStoreMiddle,if_neg hc,Nat.add_zero] using
      congrArg List.length (exp_store_head_fields tid iteration component t s).2.2.2.2.2

theorem exp_store_after_good (ops : Ops α) (input : Nat → Nat → α) (offset acc : α)
    (row tid iteration component t : Nat) (s : State α) (ht : tid<1024) (hthread : t=row*1024+tid)
    (good : ∀ a ∈ s.trace, Good a) :
    ∀ a ∈ (expStoreAfter ops input offset acc row tid iteration component t s).trace, Good a := by
  have head : ∀ a ∈ (expStoreHead tid iteration component t s).trace, Good a := by
    rewrite [(exp_store_head_fields tid iteration component t s).2.2.2.2.2]
    exact good
  change ∀ a ∈ (expStoreNext t component _).trace, Good a
  rewrite [(exp_store_next_fields t component _).2.2.2.2.2]
  by_cases hc : column tid iteration component<50257
  · simpa only [expStoreMiddle,if_pos hc] using
      exp_store_body_good ops input offset acc row tid iteration component t _ ht hc hthread head
  · simpa only [expStoreMiddle,if_neg hc] using head

theorem exp_store_component_eq (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component t extra : Nat) (offset acc : α) (s : State α)
    (hr : row<p.rows) (ht : tid<1024) (hi : iteration<7) (hc : component<8)
    (ready : ExpStoreReady p ops input row tid iteration component t offset acc s) :
    LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t
        (extra+expStoreCost tid iteration component) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t extra
        (expStoreAfter ops input offset acc row tid iteration component t s) := by
  have head := exp_store_head_fields tid iteration component t s
  have rowIndex := (exp_store_head_index_other tid iteration component t 0 s (by decide)).trans ready.rowIndex
  have componentIndex := (exp_store_head_index_other tid iteration component t 13 s (by decide)).trans ready.componentIndex
  have maximum := (congrArg (fun regs => regs t 5) head.2.2.2.1).trans ready.maximum
  have accumulator := (congrArg (fun regs => regs t 6) head.2.2.2.1).trans ready.accumulator
  have buffered := (congrArg (fun memory => memory (localCell 0 t component)) head.2.2.1).trans (ready.buffered component hc)
  by_cases hcol : column tid iteration component<50257
  · simp only [expStoreCost,expStoreAfter,expStoreMiddle,if_pos hcol]
    rewrite [show extra+10=((extra+2)+5)+3 by omega,
      exp_store_head_eq p guarded ops tid iteration component t _ s ht hi hc ready.pc ready.baseIndex ready.componentIndex]
    rewrite [exp_store_body_eq p guarded ops input offset acc row tid iteration component t (extra+2) _ hr hc hcol
      (by simpa only [if_pos hcol] using head.1) rowIndex head.2.1 componentIndex buffered maximum accumulator]
    exact exp_store_next_eq p guarded ops t component extra _ hc
      (exp_store_body_fields ops input offset acc row tid iteration component t _).1
      ((exp_store_body_index_other ops input offset acc row tid iteration component t 13 _ (by decide)).trans componentIndex)
  · simp only [expStoreCost,expStoreAfter,expStoreMiddle,if_neg hcol]
    rewrite [show extra+5=(extra+2)+3 by omega,
      exp_store_head_eq p guarded ops tid iteration component t _ s ht hi hc ready.pc ready.baseIndex ready.componentIndex]
    exact exp_store_next_eq p guarded ops t component extra _ hc
      (by simpa only [if_neg hcol] using head.1) componentIndex

theorem exp_store_component_ready (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component t : Nat) (offset acc : α) (s : State α) (ht : tid<1024)
    (ready : ExpStoreReady p ops input row tid iteration component t offset acc s) :
    ExpStoreReady p ops input row tid iteration (component+1) t offset
      (expStoreAcc ops input offset acc row tid iteration component)
      (expStoreAfter ops input offset acc row tid iteration component t s) := by
  exact {
    pc := exp_store_after_pc ops input offset acc row tid iteration component t s
    thread := ready.thread
    rowIndex := (exp_store_after_index_other ops input offset acc row tid iteration component t 0 s
      (by decide) (by decide) (by decide)).trans ready.rowIndex
    tidIndex := (exp_store_after_index_other ops input offset acc row tid iteration component t 1 s
      (by decide) (by decide) (by decide)).trans ready.tidIndex
    baseIndex := (exp_store_after_index_other ops input offset acc row tid iteration component t 9 s
      (by decide) (by decide) (by decide)).trans ready.baseIndex
    componentIndex := exp_store_after_component ops input offset acc row tid iteration component t s
    maximum := (exp_store_after_maximum ops input offset acc row tid iteration component t s).trans ready.maximum
    accumulator := exp_store_after_acc ops input offset acc row tid iteration component t s ready.accumulator
    buffered := by
      intro slot hs
      rewrite [exp_store_after_memory_other ops input offset acc row tid iteration component t s _ (by
        intro h; have hc := congrArg Location.space h; simp [localCell,globalCell] at hc)]
      exact ready.buffered slot hs
    reads := by
      intro i hb
      rewrite [exp_store_after_memory_other ops input offset acc row tid iteration component t s _ (by
        intro h; have hc := congrArg Location.buffer h; simp [globalCell] at hc)]
      exact ready.reads i hb
    good := exp_store_after_good ops input offset acc row tid iteration component t s ht ready.thread ready.good }

#print axioms exp_store_middle_pc
#print axioms exp_store_middle_index_other
#print axioms exp_store_middle_reg_other
#print axioms exp_store_middle_acc
#print axioms exp_store_after_pc
#print axioms exp_store_after_component
#print axioms exp_store_after_index_other
#print axioms exp_store_after_maximum
#print axioms exp_store_after_acc
#print axioms exp_store_after_memory
#print axioms exp_store_after_memory_other
#print axioms exp_store_after_epochs
#print axioms exp_store_after_trace_length
#print axioms exp_store_after_good
#print axioms exp_store_component_eq
#print axioms exp_store_component_ready
end LarkNativeSoftmax
