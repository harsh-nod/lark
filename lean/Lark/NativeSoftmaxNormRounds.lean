import Lark.NativeSoftmaxNormRound

/-! Induction over actual normalization outer iterations. Completed valid
outputs survive later iterations; every remaining valid input stays available.
The original clamp path and repaired skip path keep their separate counts. -/
namespace LarkNativeSoftmax
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def NormPast (ops : Ops α) (input : Nat → Nat → α) (row tid upto : Nat) (s : State α) : Prop :=
  ∀ iteration, iteration<upto → ∀ component, component<8 → column tid iteration component<50257 →
    s.memory (globalCell 0 (address row (column tid iteration component)))=
      some (normOutputValue ops input row (column tid iteration component))

theorem norm_round_past (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration : Nat) (s : State α) (past : NormPast ops input row tid iteration s) :
    NormPast ops input row tid (iteration+1) (normRoundState guarded ops input row tid iteration s) := by
  intro it hi c hc hcol
  by_cases he : it=iteration
  · subst it
    exact norm_round_outputs guarded ops input row tid iteration s c hc hcol
  · rewrite [norm_round_memory_frame guarded ops input row tid iteration s _
      (Or.inl (by change Space.global ≠ Space.local; decide)) (by
        intro slot hs hslot heq
        have ho := congrArg Location.offset heq
        change address row (column tid it c)=address row (column tid iteration slot) at ho
        unfold address column at ho
        omega)]
    exact past it (by omega) c hc hcol

def normRounds (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α) (row tid : Nat) :
    Nat → Nat → State α → State α
  | _,0,s => s
  | iteration,count+1,s => normRounds guarded ops input row tid (iteration+1) count
      (normRoundState guarded ops input row tid iteration s)

def normRoundsCost (guarded : Bool) (tid : Nat) : Nat → Nat → Nat
  | _,0 => 0
  | iteration,count+1 => normRoundCost guarded tid iteration+normRoundsCost guarded tid (iteration+1) count

def normRoundsCount (guarded : Bool) (tid : Nat) : Nat → Nat → Nat
  | _,0 => 0
  | iteration,count+1 => normLoadsCount guarded tid iteration 0 8+normStoresCount tid iteration 0 8+
      normRoundsCount guarded tid (iteration+1) count

theorem norm_rounds_ready (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration count : Nat) (s : State α) (hi : iteration+count≤7)
    (ready : NormRoundReady p ops input row tid iteration s) :
    NormRoundReady p ops input row tid (iteration+count) (normRounds guarded ops input row tid iteration count s) := by
  induction count generalizing iteration s with
  | zero => simpa only [normRounds,Nat.add_zero] using ready
  | succ count ih =>
    have head := norm_round_ready p guarded ops input row tid iteration s (by omega) ready
    have tail := ih (iteration+1) _ (by omega) head
    simpa only [normRounds,show iteration+1+count=iteration+(count+1) by omega] using tail

theorem norm_rounds_eq (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration count extra : Nat) (s : State α) (hi : iteration+count≤7)
    (ready : NormRoundReady p ops input row tid iteration s) :
    LarkCollective.runLane ops (layout p) (geometry p) (program guarded) (row*1024+tid)
      (extra+normRoundsCost guarded tid iteration count) s=
      LarkCollective.runLane ops (layout p) (geometry p) (program guarded) (row*1024+tid) extra
        (normRounds guarded ops input row tid iteration count s) := by
  induction count generalizing iteration s with
  | zero => rfl
  | succ count ih =>
    have head := norm_round_ready p guarded ops input row tid iteration s (by omega) ready
    simp only [normRoundsCost,normRounds]
    rewrite [show extra+(normRoundCost guarded tid iteration+normRoundsCost guarded tid (iteration+1) count)=
      (extra+normRoundsCost guarded tid (iteration+1) count)+normRoundCost guarded tid iteration by omega,
      norm_round_eq p guarded ops input row tid iteration _ s (by omega) ready]
    exact ih (iteration+1) _ (by omega) head

theorem norm_rounds_past (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration count : Nat) (s : State α) (past : NormPast ops input row tid iteration s) :
    NormPast ops input row tid (iteration+count) (normRounds guarded ops input row tid iteration count s) := by
  induction count generalizing iteration s with
  | zero => simpa only [normRounds,Nat.add_zero] using past
  | succ count ih =>
    have tail := ih (iteration+1) _ (norm_round_past guarded ops input row tid iteration s past)
    simpa only [normRounds,show iteration+1+count=iteration+(count+1) by omega] using tail

theorem norm_rounds_epochs (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration count : Nat) (s : State α) :
    (normRounds guarded ops input row tid iteration count s).epochs=s.epochs := by
  induction count generalizing iteration s with
  | zero => rfl
  | succ count ih =>
    exact (ih (iteration+1) _).trans (norm_round_epochs guarded ops input row tid iteration s)

theorem norm_rounds_denominator (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration count : Nat) (s : State α) :
    (normRounds guarded ops input row tid iteration count s).regs (row*1024+tid) 12=s.regs (row*1024+tid) 12 := by
  induction count generalizing iteration s with
  | zero => rfl
  | succ count ih =>
    exact (ih (iteration+1) _).trans (norm_round_denominator guarded ops input row tid iteration s)

theorem norm_rounds_index_other (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration count r : Nat) (s : State α)
    (h17 : r ≠ 17) (h18 : r ≠ 18) (h19 : r ≠ 19) (h20 : r ≠ 20) (h21 : r ≠ 21) (h22 : r ≠ 22) (h23 : r ≠ 23) :
    (normRounds guarded ops input row tid iteration count s).indices (row*1024+tid) r=s.indices (row*1024+tid) r := by
  induction count generalizing iteration s with
  | zero => rfl
  | succ count ih =>
    exact (ih (iteration+1) _).trans (norm_round_index_other guarded ops input row tid iteration r s h17 h18 h19 h20 h21 h22 h23)

theorem norm_rounds_memory_frame (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration count : Nat) (s : State α) (l : Location)
    (hprivate : l.space ≠ .local ∨ l.owner ≠ row*1024+tid ∨ l.buffer ≠ 1)
    (houtput : ∀ it, iteration≤it → it<iteration+count → ∀ c, c<8 → column tid it c<50257 →
      l ≠ globalCell 0 (address row (column tid it c))) :
    (normRounds guarded ops input row tid iteration count s).memory l=s.memory l := by
  induction count generalizing iteration s with
  | zero => rfl
  | succ count ih =>
    apply (ih (iteration+1) _ (by intro it hlo hhi c hc hcol; exact houtput it (by omega) (by omega) c hc hcol)).trans
    exact norm_round_memory_frame guarded ops input row tid iteration s l hprivate
      (by intro c hc hcol; exact houtput iteration (by omega) (by omega) c hc hcol)

theorem norm_rounds_trace_length (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration count : Nat) (s : State α) :
    (normRounds guarded ops input row tid iteration count s).trace.length=s.trace.length+2*normRoundsCount guarded tid iteration count := by
  induction count generalizing iteration s with
  | zero => simp [normRounds,normRoundsCount]
  | succ count ih =>
    change (normRounds guarded ops input row tid (iteration+1) count _).trace.length=_
    rewrite [ih,norm_round_trace_length]
    simp only [normRoundsCount]
    omega

theorem norm_rounds_other (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration count u : Nat) (s : State α) (hu : u ≠ row*1024+tid) :
    OtherThread (row*1024+tid) u s (normRounds guarded ops input row tid iteration count s) := by
  induction count generalizing iteration s with
  | zero => exact ⟨rfl,rfl,rfl⟩
  | succ count ih =>
    exact other_thread_trans (row*1024+tid) u _ _ _ (norm_round_other guarded ops input row tid iteration u s hu) (ih (iteration+1) _)

theorem norm_rounds_fixed_good (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration count : Nat) (s : State α) (ht : tid<1024) (good : ∀ a ∈ s.trace, Good a) :
    ∀ a ∈ (normRounds true ops input row tid iteration count s).trace, Good a := by
  induction count generalizing iteration s with
  | zero => exact good
  | succ count ih => exact ih (iteration+1) _ (norm_round_fixed_good ops input row tid iteration s ht good)

theorem norm_rounds_cost_bound (guarded : Bool) (tid iteration count : Nat) : normRoundsCost guarded tid iteration count≤135*count := by
  induction count generalizing iteration with
  | zero => simp [normRoundsCost]
  | succ count ih =>
    have h := norm_round_cost_bound guarded tid iteration
    have tail := ih (iteration+1)
    simp only [normRoundsCost]
    omega

#print axioms norm_round_past
#print axioms norm_rounds_ready
#print axioms norm_rounds_eq
#print axioms norm_rounds_past
#print axioms norm_rounds_epochs
#print axioms norm_rounds_denominator
#print axioms norm_rounds_index_other
#print axioms norm_rounds_memory_frame
#print axioms norm_rounds_trace_length
#print axioms norm_rounds_other
#print axioms norm_rounds_fixed_good
#print axioms norm_rounds_cost_bound
end LarkNativeSoftmax
