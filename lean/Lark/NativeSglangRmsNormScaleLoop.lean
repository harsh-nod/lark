import Lark.NativeSglangRmsNormScalePair

/-! Induction over the actual four-pair output scaling loop. Earlier private
output halves and both input caches survive each next pair. Successful scalar
execution is separate from the optional classification of an earlier trace.
-/
namespace LarkNativeSglangRmsNorm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def OutputPrefix (ops : Ops α) (input : Nat → Nat → α) (row tid count t : Nat)
    (inverse : α) (s : State α) : Prop :=
  ∀ k,k<count → s.memory (privateCell t 2 k)=some (outputScaled ops input row tid (k/8) (k%8) inverse)

theorem scale_pair_prefix (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration pair t : Nat) (inverse : α) (s : State α) (hc : pair<4)
    (done : OutputPrefix ops input row tid (iteration*8+pair*2) t inverse s) :
    OutputPrefix ops input row tid (iteration*8+pair*2+2) t inverse
      (scalePairAfter ops input row tid iteration pair t inverse s) := by
  intro k hk
  by_cases h0 : k=iteration*8+pair*2
  · subst k
    have hd : (iteration*8+pair*2)/8=iteration := by omega
    have hm : (iteration*8+pair*2)%8=pair*2 := by omega
    simpa only [hd,hm] using (scale_pair_written ops input row tid iteration pair t inverse s).1
  · by_cases h1 : k=iteration*8+pair*2+1
    · subst k
      have hd : (iteration*8+pair*2+1)/8=iteration := by omega
      have hm : (iteration*8+pair*2+1)%8=pair*2+1 := by omega
      simpa only [hd,hm] using (scale_pair_written ops input row tid iteration pair t inverse s).2
    · have ne0 : privateCell t 2 k≠privateCell t 2 (iteration*8+pair*2) := by
        intro he; exact h0 (congrArg Location.offset he)
      have ne1 : privateCell t 2 k≠privateCell t 2 (iteration*8+pair*2+1) := by
        intro he; exact h1 (congrArg Location.offset he)
      rw [scale_pair_memory,if_neg ne1,if_neg ne0]
      exact done k (by omega)

def OutsideOutput (t : Nat) (l : Location) : Prop :=
  l.space≠.local ∨ l.owner≠t ∨ l.buffer≠2

theorem scale_pair_memory_outside (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration pair t : Nat) (inverse : α) (s : State α) (l : Location) (hl : OutsideOutput t l) :
    (scalePairAfter ops input row tid iteration pair t inverse s).memory l=s.memory l := by
  have outside : ∀ slot,l≠privateCell t 2 slot := by
    intro slot he
    rw [he] at hl
    simp [OutsideOutput,privateCell] at hl
  rw [scale_pair_memory,if_neg (outside _),if_neg (outside _)]

theorem scale_pair_caches (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration pair t : Nat) (inverse : α) (s : State α)
    (cached : InputPrefix input row tid 16 t s) (weights : WeightPrefix input tid 16 t s) :
    InputPrefix input row tid 16 t (scalePairAfter ops input row tid iteration pair t inverse s) ∧
    WeightPrefix input tid 16 t (scalePairAfter ops input row tid iteration pair t inverse s) := by
  constructor
  · intro k hk
    rw [scale_pair_memory_outside ops input row tid iteration pair t inverse s _
      (by simp [OutsideOutput,privateCell])]
    exact cached k hk
  · intro k hk
    rw [scale_pair_memory_outside ops input row tid iteration pair t inverse s _
      (by simp [OutsideOutput,privateCell])]
    exact weights k hk

structure ScaleReady (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration pair t : Nat) (inverse : α) (s : State α) : Prop where
  pc : s.pc t=81
  rowIndex : s.indices t 0=some (row : Int)
  tidIndex : s.indices t 1=some (tid : Int)
  iterationIndex : s.indices t 16=some (iteration : Int)
  pairIndex : s.indices t 17=some (pair : Int)
  scale : s.regs t 12=some inverse
  inputCached : InputPrefix input row tid 16 t s
  weightCached : WeightPrefix input tid 16 t s
  completed : OutputPrefix ops input row tid (iteration*8+pair*2) t inverse s

theorem scale_pair_ready (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration pair t : Nat) (inverse : α) (s : State α) (hc : pair<4)
    (ready : ScaleReady ops input row tid iteration pair t inverse s) :
    ScaleReady ops input row tid iteration (pair+1) t inverse
      (scalePairAfter ops input row tid iteration pair t inverse s) := by
  have h := scale_pair_fields ops input row tid iteration pair t inverse s
  have caches := scale_pair_caches ops input row tid iteration pair t inverse s ready.inputCached ready.weightCached
  exact {
    pc := h.1,rowIndex := h.2.1.trans ready.rowIndex,tidIndex := h.2.2.1.trans ready.tidIndex
    iterationIndex := h.2.2.2.1.trans ready.iterationIndex,pairIndex := h.2.2.2.2.1
    scale := h.2.2.2.2.2.1.trans ready.scale,inputCached := caches.1,weightCached := caches.2
    completed := by
      have he : iteration*8+(pair+1)*2=iteration*8+pair*2+2 := by omega
      rw [he]
      exact scale_pair_prefix ops input row tid iteration pair t inverse s hc ready.completed }

def scalePairs (ops : Ops α) (input : Nat → Nat → α) (row tid iteration t : Nat) (inverse : α) :
    Nat → Nat → State α → State α
  | _,0,s => s
  | pair,remaining+1,s => scalePairs ops input row tid iteration t inverse (pair+1) remaining
      (scalePairAfter ops input row tid iteration pair t inverse s)

theorem scale_pairs_ready (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t pair remaining : Nat) (inverse : α) (s : State α)
    (hcount : pair+remaining≤4) (ready : ScaleReady ops input row tid iteration pair t inverse s) :
    ScaleReady ops input row tid iteration (pair+remaining) t inverse
      (scalePairs ops input row tid iteration t inverse pair remaining s) := by
  induction remaining generalizing pair s with
  | zero => simpa only [scalePairs,Nat.add_zero] using ready
  | succ remaining ih =>
      have h := ih (pair+1) (scalePairAfter ops input row tid iteration pair t inverse s) (by omega)
        (scale_pair_ready ops input row tid iteration pair t inverse s (by omega) ready)
      simpa only [scalePairs,show pair+1+remaining=pair+(remaining+1) by omega] using h

theorem scale_pairs_eq (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t pair remaining extra : Nat) (inverse : α) (s : State α)
    (hi : iteration<2) (hcount : pair+remaining≤4)
    (ready : ScaleReady ops input row tid iteration pair t inverse s) :
    LarkCollective.runLane ops (layout p) (geometry p) (program true) t (extra+14*remaining) s=
    LarkCollective.runLane ops (layout p) (geometry p) (program true) t extra
      (scalePairs ops input row tid iteration t inverse pair remaining s) := by
  induction remaining generalizing pair s with
  | zero => rfl
  | succ remaining ih =>
      rw [show extra+14*(remaining+1)=(extra+14*remaining)+14 by omega,
        scale_pair_cycle p ops input row tid iteration pair t (extra+14*remaining) inverse s hi (by omega)
          ready.pc ready.iterationIndex ready.pairIndex ready.scale ready.inputCached ready.weightCached]
      exact ih (pair+1) (scalePairAfter ops input row tid iteration pair t inverse s) (by omega)
        (scale_pair_ready ops input row tid iteration pair t inverse s (by omega) ready)

theorem scale_pairs_memory_outside (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t pair remaining : Nat) (inverse : α) (s : State α) (l : Location) (hl : OutsideOutput t l) :
    (scalePairs ops input row tid iteration t inverse pair remaining s).memory l=s.memory l := by
  induction remaining generalizing pair s with
  | zero => rfl
  | succ remaining ih =>
      exact (ih (pair+1) (scalePairAfter ops input row tid iteration pair t inverse s)).trans
        (scale_pair_memory_outside ops input row tid iteration pair t inverse s l hl)

theorem scale_pairs_epochs (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t pair remaining : Nat) (inverse : α) (s : State α) :
    (scalePairs ops input row tid iteration t inverse pair remaining s).epochs=s.epochs := by
  induction remaining generalizing pair s with
  | zero => rfl
  | succ remaining ih =>
      exact (ih (pair+1) (scalePairAfter ops input row tid iteration pair t inverse s)).trans
        (scale_pair_fields ops input row tid iteration pair t inverse s).2.2.2.2.2.2

theorem scale_pairs_trace_length (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t pair remaining : Nat) (inverse : α) (s : State α) :
    (scalePairs ops input row tid iteration t inverse pair remaining s).trace.length=s.trace.length+6*remaining := by
  induction remaining generalizing pair s with
  | zero => simp [scalePairs]
  | succ remaining ih =>
      simp only [scalePairs,ih,scale_pair_trace,List.length_cons]
      omega

theorem scale_pairs_good (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t pair remaining : Nat) (inverse : α) (s : State α) (good : ∀ event∈s.trace,Good event) :
    ∀ event∈(scalePairs ops input row tid iteration t inverse pair remaining s).trace,Good event := by
  induction remaining generalizing pair s with
  | zero => exact good
  | succ remaining ih => exact ih (pair+1) _ (scale_pair_good ops input row tid iteration pair t inverse s good)

#print axioms scale_pair_prefix
#print axioms scale_pair_memory_outside
#print axioms scale_pair_caches
#print axioms scale_pair_ready
#print axioms scale_pairs_ready
#print axioms scale_pairs_eq
#print axioms scale_pairs_memory_outside
#print axioms scale_pairs_epochs
#print axioms scale_pairs_trace_length
#print axioms scale_pairs_good
end LarkNativeSglangRmsNorm
