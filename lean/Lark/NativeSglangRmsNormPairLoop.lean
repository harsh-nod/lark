import Lark.NativeSglangRmsNormPairStep

/-! Induction over the actual four-pair accumulation loop. -/
namespace LarkNativeSglangRmsNorm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

structure PairReady (p : Shape) (input : Nat → Nat → α)
    (row tid iteration pair t : Nat) (acc : α) (s : State α) : Prop where
  pc : s.pc t = 32
  rowIndex : s.indices t 0 = some (row : Int)
  tidIndex : s.indices t 1 = some (tid : Int)
  iterationIndex : s.indices t 13 = some (iteration : Int)
  pairIndex : s.indices t 14 = some (pair : Int)
  accumulator : s.regs t 0 = some acc
  reads : Reads p input s
  inputCached : InputPrefix input row tid 16 t s
  weightCached : WeightPrefix input tid 16 t s
  good : ∀ a ∈ s.trace, Good a

theorem pair_ready (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration pair t : Nat) (acc : α) (s : State α)
    (ready : PairReady p input row tid iteration pair t acc s) :
    PairReady p input row tid iteration (pair + 1) t
      (ops.add acc (pairSquare ops input row tid iteration pair))
      (pairAfter ops input row tid iteration pair t acc s) := by
  obtain ⟨hp,h0,h1,h13,h14,ha⟩ := pair_fields ops input row tid iteration pair t acc s
  exact {
    pc := hp, rowIndex := h0.trans ready.rowIndex, tidIndex := h1.trans ready.tidIndex
    iterationIndex := h13.trans ready.iterationIndex, pairIndex := h14, accumulator := ha
    reads := ready.reads, inputCached := ready.inputCached, weightCached := ready.weightCached
    good := pair_good ops input row tid iteration pair t acc s ready.good }

def pairs (ops : Ops α) (input : Nat → Nat → α) (row tid iteration t : Nat) :
    Nat → Nat → α → State α → State α
  | _,0,_,s => s
  | pair,remaining + 1,acc,s =>
      pairs ops input row tid iteration t (pair + 1) remaining
        (ops.add acc (pairSquare ops input row tid iteration pair))
        (pairAfter ops input row tid iteration pair t acc s)

theorem pairs_ready (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t pair remaining : Nat) (acc : α) (s : State α)
    (ready : PairReady p input row tid iteration pair t acc s) :
    PairReady p input row tid iteration (pair + remaining) t
      (pairFold ops input row tid iteration pair remaining acc)
      (pairs ops input row tid iteration t pair remaining acc s) := by
  induction remaining generalizing pair acc s with
  | zero => simpa only [pairs,pairFold,Nat.add_zero] using ready
  | succ remaining ih =>
      have next := pair_ready p ops input row tid iteration pair t acc s ready
      have step := ih (pair + 1) (ops.add acc (pairSquare ops input row tid iteration pair))
        (pairAfter ops input row tid iteration pair t acc s) next
      simpa only [pairs,pairFold,
        show pair + 1 + remaining = pair + (remaining + 1) by omega] using step

theorem pairs_eq (p : Shape) (repaired : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t pair remaining extra : Nat) (acc : α) (s : State α)
    (hi : iteration < 2) (hcount : pair + remaining ≤ 4)
    (ready : PairReady p input row tid iteration pair t acc s) :
    LarkCollective.runLane ops (layout p) (geometry p) (program repaired) t (extra + 10 * remaining) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program repaired) t extra
        (pairs ops input row tid iteration t pair remaining acc s) := by
  induction remaining generalizing pair acc s with
  | zero => rfl
  | succ remaining ih =>
      have cycle := pair_cycle p repaired ops input row tid iteration pair t (extra + 10 * remaining)
        acc s hi (by omega) ready.iterationIndex ready.pairIndex ready.accumulator ready.pc ready.inputCached
      rewrite [show extra + 10 * (remaining + 1) = (extra + 10 * remaining) + 10 by omega,cycle]
      exact ih (pair + 1) (ops.add acc (pairSquare ops input row tid iteration pair))
        (pairAfter ops input row tid iteration pair t acc s) (by omega)
        (pair_ready p ops input row tid iteration pair t acc s ready)

theorem pairs_memory (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t pair remaining : Nat) (acc : α) (s : State α) :
    (pairs ops input row tid iteration t pair remaining acc s).memory = s.memory := by
  induction remaining generalizing pair acc s with
  | zero => rfl
  | succ remaining ih =>
      simp only [pairs,ih,pair_memory]

theorem pairs_epochs (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t pair remaining : Nat) (acc : α) (s : State α) :
    (pairs ops input row tid iteration t pair remaining acc s).epochs = s.epochs := by
  induction remaining generalizing pair acc s with
  | zero => rfl
  | succ remaining ih => simp only [pairs,ih,pair_epochs]

theorem pairs_trace_length (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t pair remaining : Nat) (acc : α) (s : State α) :
    (pairs ops input row tid iteration t pair remaining acc s).trace.length =
      s.trace.length + 2 * remaining := by
  induction remaining generalizing pair acc s with
  | zero => simp [pairs]
  | succ remaining ih =>
      simp only [pairs,ih,pair_trace,List.length_cons]
      omega

#print axioms pair_ready
#print axioms pairs_ready
#print axioms pairs_eq
#print axioms pairs_memory
#print axioms pairs_epochs
#print axioms pairs_trace_length
end LarkNativeSglangRmsNorm
