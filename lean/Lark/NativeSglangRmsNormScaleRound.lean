import Lark.NativeSglangRmsNormScaleLoop

/-! Actual outer output-vector rounds and both false loop exits. Two rounds
produce all16 private output halves in source order before the global copy loop.
-/
namespace LarkNativeSglangRmsNorm
open LarkNonlinear
open LarkReduction (setIndex execute_index_of predicate_lt_of predicate_nlt_of)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
attribute [local irreducible] scalePairs

def scaleRoundBegin (t : Nat) (s : State α) : State α :=
  setIndex (advance s t 80) t 17 0 81
def scaleRoundEnd (iteration t : Nat) (s : State α) : State α :=
  advance (setIndex (advance s t 95) t 16 ((iteration+1 : Nat) : Int) 96) t 79
def scaleRoundAfter (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t : Nat) (inverse : α) (s : State α) : State α :=
  scaleRoundEnd iteration t (scalePairs ops input row tid iteration t inverse 0 4 (scaleRoundBegin t s))

theorem scale_round_begin_eq (p : Shape) (ops : Ops α) (iteration t extra : Nat) (s : State α)
    (hi : iteration<2) (hp : s.pc t=79) (h16 : s.indices t 16=some (iteration : Int)) :
    LarkCollective.runLane ops (layout p) (geometry p) (program true) t (extra+2) s=
    LarkCollective.runLane ops (layout p) (geometry p) (program true) t extra (scaleRoundBegin t s) := by
  have pred := predicate_lt_of (geometry p) t s (.ivar 16) (.const 2) (iteration : Int) 2 h16 rfl (by omega)
  have e1 : execute ops (layout p) (geometry p) t (.branch (.lt (.ivar 16) (.const 2)) 97) s=
      some (advance s t 80) := by simp [execute,pred,hp]
  have e2 := execute_index_of ops (layout p) (geometry p) t 17 81 (.const 0) (advance s t 80) 0 rfl (by simp [advance])
  rw [scalar_step p true ops t 79 (extra+1) _ s _ (by decide) hp e1]
  exact scalar_step p true ops t 80 extra _ _ _ (by decide) (by simp [advance]) e2

theorem scale_round_end_eq (p : Shape) (ops : Ops α) (iteration t extra : Nat) (s : State α)
    (hi : iteration<2) (hp : s.pc t=81) (h16 : s.indices t 16=some (iteration : Int))
    (h17 : s.indices t 17=some 4) :
    LarkCollective.runLane ops (layout p) (geometry p) (program true) t (extra+3) s=
    LarkCollective.runLane ops (layout p) (geometry p) (program true) t extra (scaleRoundEnd iteration t s) := by
  let s1 := advance s t 95
  let s2 := setIndex s1 t 16 ((iteration+1 : Nat) : Int) 96
  have pred := predicate_nlt_of (geometry p) t s (.ivar 17) (.const 4) 4 4 h17 rfl (by decide)
  have e1 : execute ops (layout p) (geometry p) t (.branch (.lt (.ivar 17) (.const 4)) 95) s=some s1 := by
    simp [execute,pred,s1]
  have plus := eval_nat_sum (geometry p) t iteration 1 s1 (.ivar 16) (.const 1) h16 rfl (by omega)
  have e2 := execute_index_of ops (layout p) (geometry p) t 16 96 (.add (.ivar 16) (.const 1)) s1 _ plus (by simp [s1,advance])
  have e3 : execute ops (layout p) (geometry p) t (.jump 79) s2=some (scaleRoundEnd iteration t s) := rfl
  rw [scalar_step p true ops t 81 (extra+2) _ s s1 (by decide) hp e1]
  rw [scalar_step p true ops t 95 (extra+1) _ s1 s2 (by decide) (by simp [s1,advance]) e2]
  exact scalar_step p true ops t 96 extra _ s2 _ (by decide) (by simp [s2,setIndex,advance]) e3

theorem scale_rounds_exit_eq (p : Shape) (ops : Ops α) (t extra : Nat) (s : State α)
    (hp : s.pc t=79) (h16 : s.indices t 16=some 2) :
    LarkCollective.runLane ops (layout p) (geometry p) (program true) t (extra+1) s=
    LarkCollective.runLane ops (layout p) (geometry p) (program true) t extra (advance s t 97) := by
  have pred := predicate_nlt_of (geometry p) t s (.ivar 16) (.const 2) 2 2 h16 rfl (by decide)
  have e : execute ops (layout p) (geometry p) t (.branch (.lt (.ivar 16) (.const 2)) 97) s=
      some (advance s t 97) := by simp [execute,pred]
  exact scalar_step p true ops t 79 extra _ s _ (by decide) hp e

structure ScaleRoundReady (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t : Nat) (inverse : α) (s : State α) : Prop where
  pc : s.pc t=79
  rowIndex : s.indices t 0=some (row : Int)
  tidIndex : s.indices t 1=some (tid : Int)
  iterationIndex : s.indices t 16=some (iteration : Int)
  scale : s.regs t 12=some inverse
  inputCached : InputPrefix input row tid 16 t s
  weightCached : WeightPrefix input tid 16 t s
  completed : OutputPrefix ops input row tid (iteration*8) t inverse s

theorem scale_round_begin_ready (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t : Nat) (inverse : α) (s : State α)
    (ready : ScaleRoundReady ops input row tid iteration t inverse s) :
    ScaleReady ops input row tid iteration 0 t inverse (scaleRoundBegin t s) := by
  exact {
    pc := by simp [scaleRoundBegin,setIndex,advance]
    rowIndex := by simpa [scaleRoundBegin,setIndex,advance] using ready.rowIndex
    tidIndex := by simpa [scaleRoundBegin,setIndex,advance] using ready.tidIndex
    iterationIndex := by simpa [scaleRoundBegin,setIndex,advance] using ready.iterationIndex
    pairIndex := by simp [scaleRoundBegin,setIndex,advance]
    scale := ready.scale,inputCached := ready.inputCached,weightCached := ready.weightCached
    completed := by simpa only [Nat.zero_mul,Nat.add_zero] using ready.completed }

theorem scale_round_ready (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t : Nat) (inverse : α) (s : State α)
    (ready : ScaleRoundReady ops input row tid iteration t inverse s) :
    ScaleRoundReady ops input row tid (iteration+1) t inverse
      (scaleRoundAfter ops input row tid iteration t inverse s) := by
  have r4 := scale_pairs_ready ops input row tid iteration t 0 4 inverse (scaleRoundBegin t s)
    (by decide) (scale_round_begin_ready ops input row tid iteration t inverse s ready)
  exact {
    pc := by simp [scaleRoundAfter,scaleRoundEnd,setIndex,advance]
    rowIndex := by simpa [scaleRoundAfter,scaleRoundEnd,setIndex,advance] using r4.rowIndex
    tidIndex := by simpa [scaleRoundAfter,scaleRoundEnd,setIndex,advance] using r4.tidIndex
    iterationIndex := by simp [scaleRoundAfter,scaleRoundEnd,setIndex,advance]
    scale := r4.scale,inputCached := r4.inputCached,weightCached := r4.weightCached
    completed := by
      have he : (iteration+1)*8=iteration*8+(0+4)*2 := by omega
      simpa only [scaleRoundAfter,scaleRoundEnd,setIndex,advance,he] using r4.completed }

theorem scale_round_eq (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t extra : Nat) (inverse : α) (s : State α) (hi : iteration<2)
    (ready : ScaleRoundReady ops input row tid iteration t inverse s) :
    LarkCollective.runLane ops (layout p) (geometry p) (program true) t (extra+61) s=
    LarkCollective.runLane ops (layout p) (geometry p) (program true) t extra
      (scaleRoundAfter ops input row tid iteration t inverse s) := by
  let entry := scaleRoundBegin t s
  let paired := scalePairs ops input row tid iteration t inverse 0 4 entry
  have r0 := scale_round_begin_ready ops input row tid iteration t inverse s ready
  have r4 := scale_pairs_ready ops input row tid iteration t 0 4 inverse entry (by decide) r0
  rw [show extra+61=(extra+59)+2 by omega,scale_round_begin_eq p ops iteration t (extra+59) s hi ready.pc ready.iterationIndex]
  rw [show extra+59=(extra+3)+14*4 by omega,scale_pairs_eq p ops input row tid iteration t 0 4 (extra+3) inverse entry hi (by decide) r0]
  exact scale_round_end_eq p ops iteration t extra paired hi r4.pc r4.iterationIndex r4.pairIndex

theorem scale_round_memory_outside (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t : Nat) (inverse : α) (s : State α) (l : Location) (hl : OutsideOutput t l) :
    (scaleRoundAfter ops input row tid iteration t inverse s).memory l=s.memory l :=
  scale_pairs_memory_outside ops input row tid iteration t 0 4 inverse (scaleRoundBegin t s) l hl

theorem scale_round_epochs (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t : Nat) (inverse : α) (s : State α) :
    (scaleRoundAfter ops input row tid iteration t inverse s).epochs=s.epochs := by
  simp only [scaleRoundAfter,scaleRoundEnd,setIndex,advance,scale_pairs_epochs,scaleRoundBegin]

theorem scale_round_trace_length (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t : Nat) (inverse : α) (s : State α) :
    (scaleRoundAfter ops input row tid iteration t inverse s).trace.length=s.trace.length+24 := by
  simp only [scaleRoundAfter,scaleRoundEnd,setIndex,advance,scale_pairs_trace_length,scaleRoundBegin]

theorem scale_round_good (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t : Nat) (inverse : α) (s : State α) (good : ∀ event∈s.trace,Good event) :
    ∀ event∈(scaleRoundAfter ops input row tid iteration t inverse s).trace,Good event :=
  scale_pairs_good ops input row tid iteration t 0 4 inverse (scaleRoundBegin t s) good

def scaleRounds (ops : Ops α) (input : Nat → Nat → α) (row tid t : Nat) (inverse : α) :
    Nat → Nat → State α → State α
  | _,0,s => s
  | iteration,remaining+1,s => scaleRounds ops input row tid t inverse (iteration+1) remaining
      (scaleRoundAfter ops input row tid iteration t inverse s)

theorem scale_rounds_ready (ops : Ops α) (input : Nat → Nat → α)
    (row tid t iteration remaining : Nat) (inverse : α) (s : State α)
    (ready : ScaleRoundReady ops input row tid iteration t inverse s) :
    ScaleRoundReady ops input row tid (iteration+remaining) t inverse
      (scaleRounds ops input row tid t inverse iteration remaining s) := by
  induction remaining generalizing iteration s with
  | zero => simpa only [scaleRounds,Nat.add_zero] using ready
  | succ remaining ih =>
      have h := ih (iteration+1) _ (scale_round_ready ops input row tid iteration t inverse s ready)
      simpa only [scaleRounds,show iteration+1+remaining=iteration+(remaining+1) by omega] using h

theorem scale_rounds_eq (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid t iteration remaining extra : Nat) (inverse : α) (s : State α)
    (hcount : iteration+remaining≤2) (ready : ScaleRoundReady ops input row tid iteration t inverse s) :
    LarkCollective.runLane ops (layout p) (geometry p) (program true) t (extra+61*remaining) s=
    LarkCollective.runLane ops (layout p) (geometry p) (program true) t extra
      (scaleRounds ops input row tid t inverse iteration remaining s) := by
  induction remaining generalizing iteration s with
  | zero => rfl
  | succ remaining ih =>
      rw [show extra+61*(remaining+1)=(extra+61*remaining)+61 by omega,
        scale_round_eq p ops input row tid iteration t (extra+61*remaining) inverse s (by omega) ready]
      exact ih (iteration+1) _ (by omega) (scale_round_ready ops input row tid iteration t inverse s ready)

theorem scale_rounds_memory_outside (ops : Ops α) (input : Nat → Nat → α)
    (row tid t iteration remaining : Nat) (inverse : α) (s : State α) (l : Location) (hl : OutsideOutput t l) :
    (scaleRounds ops input row tid t inverse iteration remaining s).memory l=s.memory l := by
  induction remaining generalizing iteration s with
  | zero => rfl
  | succ remaining ih => exact (ih (iteration+1) _).trans (scale_round_memory_outside ops input row tid iteration t inverse s l hl)

theorem scale_rounds_epochs (ops : Ops α) (input : Nat → Nat → α)
    (row tid t iteration remaining : Nat) (inverse : α) (s : State α) :
    (scaleRounds ops input row tid t inverse iteration remaining s).epochs=s.epochs := by
  induction remaining generalizing iteration s with
  | zero => rfl
  | succ remaining ih => exact (ih (iteration+1) _).trans (scale_round_epochs ops input row tid iteration t inverse s)

theorem scale_rounds_trace_length (ops : Ops α) (input : Nat → Nat → α)
    (row tid t iteration remaining : Nat) (inverse : α) (s : State α) :
    (scaleRounds ops input row tid t inverse iteration remaining s).trace.length=s.trace.length+24*remaining := by
  induction remaining generalizing iteration s with
  | zero => simp [scaleRounds]
  | succ remaining ih => simp only [scaleRounds,ih,scale_round_trace_length]; omega

theorem scale_rounds_good (ops : Ops α) (input : Nat → Nat → α)
    (row tid t iteration remaining : Nat) (inverse : α) (s : State α) (good : ∀ event∈s.trace,Good event) :
    ∀ event∈(scaleRounds ops input row tid t inverse iteration remaining s).trace,Good event := by
  induction remaining generalizing iteration s with
  | zero => exact good
  | succ remaining ih => exact ih (iteration+1) _ (scale_round_good ops input row tid iteration t inverse s good)

#print axioms scale_round_begin_eq
#print axioms scale_round_end_eq
#print axioms scale_rounds_exit_eq
#print axioms scale_round_begin_ready
#print axioms scale_round_ready
#print axioms scale_round_eq
#print axioms scale_round_memory_outside
#print axioms scale_round_epochs
#print axioms scale_round_trace_length
#print axioms scale_round_good
#print axioms scale_rounds_ready
#print axioms scale_rounds_eq
#print axioms scale_rounds_memory_outside
#print axioms scale_rounds_epochs
#print axioms scale_rounds_trace_length
#print axioms scale_rounds_good
end LarkNativeSglangRmsNorm
