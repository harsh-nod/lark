import Lark.NativeSoftmaxExpRound

/-! Induction over all source outer iterations of exponentiation and sum.
Past output values are preserved as later iterations write distinct columns. -/
namespace LarkNativeSoftmax
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def expRoundsFold (ops : Ops α) (input : Nat → Nat → α) (offset : α) (row tid : Nat) : Nat → Nat → α → α
  | _,0,acc => acc
  | iteration,count+1,acc => expRoundsFold ops input offset row tid (iteration+1) count
      (expRoundFold ops input offset row tid iteration acc)

def expRounds (ops : Ops α) (input : Nat → Nat → α) (offset : α) (row tid t : Nat) :
    Nat → Nat → α → State α → State α
  | _,0,_,s => s
  | iteration,count+1,acc,s => expRounds ops input offset row tid t (iteration+1) count
      (expRoundFold ops input offset row tid iteration acc) (expRoundState ops input offset row tid iteration t acc s)

def expRoundsCost (tid : Nat) : Nat → Nat → Nat
  | _,0 => 0
  | iteration,count+1 => expRoundCost tid iteration+expRoundsCost tid (iteration+1) count

def expRoundsCount (tid : Nat) : Nat → Nat → Nat
  | _,0 => 0
  | iteration,count+1 => expStoresCount tid iteration 0 8+expRoundsCount tid (iteration+1) count

def ExpPastOutputs (ops : Ops α) (input : Nat → Nat → α) (offset : α) (row tid upto : Nat) (s : State α) : Prop :=
  ∀ iteration, iteration<upto → ExpOutputs ops input offset row tid iteration 8 s

theorem exp_round_past_outputs (ops : Ops α) (input : Nat → Nat → α) (offset : α)
    (row tid iteration t : Nat) (acc : α) (s : State α) (ht : tid<1024)
    (past : ExpPastOutputs ops input offset row tid iteration s) :
    ExpPastOutputs ops input offset row tid (iteration+1) (expRoundState ops input offset row tid iteration t acc s) := by
  intro oldIter hi slot hs hcol
  by_cases he : oldIter=iteration
  · subst oldIter
    exact exp_round_outputs ops input offset row tid iteration t acc s slot hs hcol
  · have hmem : (expRoundState ops input offset row tid iteration t acc s).memory
        (globalCell 0 (address row (column tid oldIter slot)))=
          s.memory (globalCell 0 (address row (column tid oldIter slot))) := by
      apply exp_round_memory_frame ops input offset row tid iteration t acc s _ (Or.inl (by change Space.global ≠ Space.local; decide))
      intro component hc _ h
      have had := congrArg Location.offset h
      change address row (column tid oldIter slot)=address row (column tid iteration component) at had
      have hcols : column tid oldIter slot=column tid iteration component := by unfold address at had; omega
      have heq := (column_injective tid oldIter slot tid iteration component ht ht hs hc hcols).2.1
      exact he heq
    rewrite [hmem]
    exact past oldIter (by omega) slot hs hcol

theorem exp_rounds_ready (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (offset : α)
    (row tid t iteration count : Nat) (acc : α) (s : State α) (ht : tid<1024)
    (ready : ExpRoundReady p input row tid iteration t offset acc s) :
    ExpRoundReady p input row tid (iteration+count) t offset
      (expRoundsFold ops input offset row tid iteration count acc)
      (expRounds ops input offset row tid t iteration count acc s) := by
  induction count generalizing iteration acc s with
  | zero => simpa only [expRoundsFold,expRounds,Nat.add_zero] using ready
  | succ count ih =>
    have head := exp_round_ready p ops input offset row tid iteration t acc s ht ready
    have tail := ih (iteration+1) _ _ head
    simpa only [expRoundsFold,expRounds,show iteration+1+count=iteration+(count+1) by omega] using tail

theorem exp_rounds_eq (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α) (offset : α)
    (row tid t iteration count extra : Nat) (acc : α) (s : State α)
    (hr : row<p.rows) (ht : tid<1024) (hi : iteration+count≤7)
    (ready : ExpRoundReady p input row tid iteration t offset acc s) :
    LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t (extra+expRoundsCost tid iteration count) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t extra
        (expRounds ops input offset row tid t iteration count acc s) := by
  induction count generalizing iteration acc s with
  | zero => rfl
  | succ count ih =>
    have head := exp_round_ready p ops input offset row tid iteration t acc s ht ready
    simp only [expRoundsCost,expRounds]
    rewrite [show extra+(expRoundCost tid iteration+expRoundsCost tid (iteration+1) count)=
      (extra+expRoundsCost tid (iteration+1) count)+expRoundCost tid iteration by omega]
    rewrite [exp_round_eq p guarded ops input offset row tid iteration t _ acc s hr ht (by omega) ready]
    exact ih (iteration+1) _ _ (by omega) head

theorem exp_rounds_outputs (ops : Ops α) (input : Nat → Nat → α) (offset : α)
    (row tid t iteration count : Nat) (acc : α) (s : State α) (ht : tid<1024)
    (past : ExpPastOutputs ops input offset row tid iteration s) :
    ExpPastOutputs ops input offset row tid (iteration+count) (expRounds ops input offset row tid t iteration count acc s) := by
  induction count generalizing iteration acc s with
  | zero => simpa only [expRounds,Nat.add_zero] using past
  | succ count ih =>
    have tail := ih (iteration+1) (expRoundFold ops input offset row tid iteration acc)
      (expRoundState ops input offset row tid iteration t acc s) (exp_round_past_outputs ops input offset row tid iteration t acc s ht past)
    simpa only [expRounds,show iteration+1+count=iteration+(count+1) by omega] using tail

theorem exp_rounds_trace_length (ops : Ops α) (input : Nat → Nat → α) (offset : α)
    (row tid t iteration count : Nat) (acc : α) (s : State α) :
    (expRounds ops input offset row tid t iteration count acc s).trace.length=
      s.trace.length+16*count+2*expRoundsCount tid iteration count := by
  induction count generalizing iteration acc s with
  | zero => simp [expRounds,expRoundsCount]
  | succ count ih =>
    have tail := ih (iteration+1) (expRoundFold ops input offset row tid iteration acc)
      (expRoundState ops input offset row tid iteration t acc s)
    change (expRounds ops input offset row tid t (iteration+1) count _ _).trace.length=_
    rewrite [tail,exp_round_trace_length]
    simp only [expRoundsCount]
    omega

theorem exp_rounds_epochs (ops : Ops α) (input : Nat → Nat → α) (offset : α)
    (row tid t iteration count : Nat) (acc : α) (s : State α) :
    (expRounds ops input offset row tid t iteration count acc s).epochs=s.epochs := by
  induction count generalizing iteration acc s with
  | zero => rfl
  | succ count ih =>
    exact (ih (iteration+1) _ _).trans (exp_round_epochs ops input offset row tid iteration t acc s)

theorem exp_rounds_index_other (ops : Ops α) (input : Nat → Nat → α) (offset : α)
    (row tid t iteration count r : Nat) (acc : α) (s : State α)
    (h9 : r ≠ 9) (h10 : r ≠ 10) (h11 : r ≠ 11) (h12 : r ≠ 12) (h13 : r ≠ 13) (h14 : r ≠ 14) (h15 : r ≠ 15) :
    (expRounds ops input offset row tid t iteration count acc s).indices t r=s.indices t r := by
  induction count generalizing iteration acc s with
  | zero => rfl
  | succ count ih =>
    exact (ih (iteration+1) _ _).trans (exp_round_index_other ops input offset row tid iteration t r acc s h9 h10 h11 h12 h13 h14 h15)

theorem exp_rounds_memory_frame (ops : Ops α) (input : Nat → Nat → α) (offset : α)
    (row tid t iteration count : Nat) (acc : α) (s : State α) (l : Location)
    (hprivate : l.space ≠ .local ∨ l.owner ≠ t ∨ l.buffer ≠ 0)
    (houtput : ∀ it, iteration≤it → it<iteration+count → ∀ component, component<8 → column tid it component<50257 →
      l ≠ globalCell 0 (address row (column tid it component))) :
    (expRounds ops input offset row tid t iteration count acc s).memory l=s.memory l := by
  induction count generalizing iteration acc s with
  | zero => rfl
  | succ count ih =>
    have tail := ih (iteration+1) (expRoundFold ops input offset row tid iteration acc)
      (expRoundState ops input offset row tid iteration t acc s) (by
        intro it hlo hhi component hc hcol
        exact houtput it (by omega) (by omega) component hc hcol)
    exact tail.trans (exp_round_memory_frame ops input offset row tid iteration t acc s l hprivate
      (by intro component hc hcol; exact houtput iteration (by omega) (by omega) component hc hcol))

theorem exp_rounds_count_bound (tid iteration count : Nat) : expRoundsCount tid iteration count≤8*count := by
  induction count generalizing iteration with
  | zero => simp [expRoundsCount]
  | succ count ih =>
    have head := exp_stores_count_bound tid iteration 0 8
    have tail := ih (iteration+1)
    simp only [expRoundsCount]
    omega

theorem exp_rounds_cost_bound (tid iteration count : Nat) : expRoundsCost tid iteration count≤151*count := by
  induction count generalizing iteration with
  | zero => simp [expRoundsCost]
  | succ count ih =>
    have head := exp_round_cost_bound tid iteration
    have tail := ih (iteration+1)
    simp only [expRoundsCost]
    omega

#print axioms exp_round_past_outputs
#print axioms exp_rounds_ready
#print axioms exp_rounds_eq
#print axioms exp_rounds_outputs
#print axioms exp_rounds_trace_length
#print axioms exp_rounds_epochs
#print axioms exp_rounds_index_other
#print axioms exp_rounds_memory_frame
#print axioms exp_rounds_count_bound
#print axioms exp_rounds_cost_bound
end LarkNativeSoftmax
