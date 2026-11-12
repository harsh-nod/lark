import Lark.NativeSglangRmsNormPairLoop

/-! Actual counted-round control, including both false exits. Control steps
preserve memory, traces and epochs; the pinned source and machine are unchanged.
-/
namespace LarkNativeSglangRmsNorm
open LarkNonlinear
open LarkReduction (setIndex execute_index_of int32_cast predicate_lt_of predicate_nlt_of)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def beginRound (t : Nat) (s : State α) : State α :=
  setIndex (advance s t 31) t 14 0 32

def endRound (t iteration : Nat) (s : State α) : State α :=
  advance (setIndex (advance s t 42) t 13 ((iteration + 1 : Nat) : Int) 43) t 30

theorem begin_round_eq (p : Shape) (repaired : Bool) (ops : Ops α) (t iteration extra : Nat) (s : State α)
    (hi : iteration < 2) (hp : s.pc t = 30)
    (h4 : s.indices t 13 = some (iteration : Int)) :
    LarkCollective.runLane ops (layout p) (geometry p) (program repaired) t (extra + 2) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program repaired) t extra (beginRound t s) := by
  have pred := predicate_lt_of (geometry p) t s (.ivar 13) (.const 2)
    (iteration : Int) 2 h4 rfl (by omega)
  have e1 : execute ops (layout p) (geometry p) t
      (.branch (.lt (.ivar 13) (.const 2)) 44) s = some (advance s t 31) := by
    simp [execute, pred, hp]
  have e2 := execute_index_of ops (layout p) (geometry p) t 14 32 (.const 0)
    (advance s t 31) 0 rfl (by simp [advance])
  rewrite [scalar_step p repaired ops t 30 _ _ s _ (by cases repaired <;> decide) hp e1]
  rewrite [scalar_step p repaired ops t 31 _ _ _ _ (by cases repaired <;> decide) (by simp [advance]) e2]
  rfl

theorem end_round_eq (p : Shape) (repaired : Bool) (ops : Ops α) (t iteration extra : Nat) (s : State α)
    (hi : iteration < 2) (hp : s.pc t = 32)
    (h4 : s.indices t 13 = some (iteration : Int)) (h5 : s.indices t 14 = some 4) :
    LarkCollective.runLane ops (layout p) (geometry p) (program repaired) t (extra + 3) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program repaired) t extra (endRound t iteration s) := by
  have pred := predicate_nlt_of (geometry p) t s (.ivar 14) (.const 4) 4 4 h5 rfl (by omega)
  let s1 := advance s t 42
  let s2 := setIndex s1 t 13 ((iteration + 1 : Nat) : Int) 43
  have e1 : execute ops (layout p) (geometry p) t
      (.branch (.lt (.ivar 14) (.const 4)) 42) s = some s1 := by
    simp [execute, pred, hp, s1]
  have he : evalIndex (geometry p) t s1 (.add (.ivar 13) (.const 1)) =
      some ((iteration + 1 : Nat) : Int) :=
    eval_nat_sum (geometry p) t iteration 1 s1 (.ivar 13) (.const 1) h4 rfl (by omega)
  have e2 := execute_index_of ops (layout p) (geometry p) t 13 43
    (.add (.ivar 13) (.const 1)) s1 _ he (by simp [s1, advance])
  change execute _ _ _ _ _ s1 = some s2 at e2
  have e3 : execute ops (layout p) (geometry p) t (.jump 30) s2 = some (endRound t iteration s) := rfl
  rewrite [scalar_step p repaired ops t 32 _ _ s s1 (by cases repaired <;> decide) hp e1]
  rewrite [scalar_step p repaired ops t 42 _ _ s1 s2 (by cases repaired <;> decide) (by simp [s1, advance]) e2]
  rewrite [scalar_step p repaired ops t 43 _ _ s2 _ (by cases repaired <;> decide) (by simp [s2, setIndex, advance]) e3]
  rfl

theorem exit_rounds_eq (p : Shape) (repaired : Bool) (ops : Ops α) (t extra : Nat) (s : State α)
    (hp : s.pc t = 30) (h4 : s.indices t 13 = some 2) :
    LarkCollective.runLane ops (layout p) (geometry p) (program repaired) t (extra + 1) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program repaired) t extra (advance s t 44) := by
  have pred := predicate_nlt_of (geometry p) t s (.ivar 13) (.const 2) 2 2 h4 rfl (by omega)
  have e : execute ops (layout p) (geometry p) t
      (.branch (.lt (.ivar 13) (.const 2)) 44) s = some (advance s t 44) := by
    simp [execute, pred, hp]
  exact scalar_step p repaired ops t 30 extra _ s _ (by cases repaired <;> decide) hp e

structure StartReady (p : Shape) (input : Nat → Nat → α)
    (row tid iteration t : Nat) (acc : α) (s : State α) : Prop where
  pc : s.pc t = 30
  rowIndex : s.indices t 0 = some (row : Int)
  tidIndex : s.indices t 1 = some (tid : Int)
  iterationIndex : s.indices t 13 = some (iteration : Int)
  accumulator : s.regs t 0 = some acc
  reads : Reads p input s
  inputCached : InputPrefix input row tid 16 t s
  weightCached : WeightPrefix input tid 16 t s
  good : ∀ a ∈ s.trace, Good a

theorem begin_round_ready (p : Shape) (_ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t : Nat) (acc : α) (s : State α)
    (ready : StartReady p input row tid iteration t acc s) :
    PairReady p input row tid iteration 0 t acc (beginRound t s) := by
  exact {
    pc := by simp [beginRound, setIndex, advance]
    rowIndex := by simpa [beginRound, setIndex, advance] using ready.rowIndex
    tidIndex := by simpa [beginRound, setIndex, advance] using ready.tidIndex
    iterationIndex := by simpa [beginRound, setIndex, advance] using ready.iterationIndex
    pairIndex := by simp [beginRound, setIndex, advance]
    accumulator := ready.accumulator
    reads := ready.reads, inputCached := ready.inputCached, weightCached := ready.weightCached
    good := ready.good }

theorem end_round_ready (p : Shape) (_ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t : Nat) (acc : α) (s : State α)
    (ready : PairReady p input row tid iteration 4 t acc s) :
    StartReady p input row tid (iteration + 1) t acc (endRound t iteration s) := by
  exact {
    pc := by simp [endRound, setIndex, advance]
    rowIndex := by simpa [endRound, setIndex, advance] using ready.rowIndex
    tidIndex := by simpa [endRound, setIndex, advance] using ready.tidIndex
    iterationIndex := by simp [endRound, setIndex, advance]
    accumulator := ready.accumulator
    reads := ready.reads, inputCached := ready.inputCached, weightCached := ready.weightCached
    good := ready.good }

def roundAfter (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t : Nat) (acc : α) (s : State α) : State α :=
  endRound t iteration (pairs ops input row tid iteration t 0 4 acc (beginRound t s))

theorem round_ready (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t : Nat) (acc : α) (s : State α)
    (ready : StartReady p input row tid iteration t acc s) :
    StartReady p input row tid (iteration + 1) t
      (pairFold ops input row tid iteration 0 4 acc)
      (roundAfter ops input row tid iteration t acc s) :=
  end_round_ready p ops input row tid iteration t _ _
    (pairs_ready p ops input row tid iteration t 0 4 acc (beginRound t s)
      (begin_round_ready p ops input row tid iteration t acc s ready))

theorem round_eq (p : Shape) (repaired : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t extra : Nat) (acc : α) (s : State α)
    (_hr : row < p.rows) (_ht : tid < 1024) (hi : iteration < 2)
    (ready : StartReady p input row tid iteration t acc s) :
    LarkCollective.runLane ops (layout p) (geometry p) (program repaired) t (extra + 45) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program repaired) t extra
        (roundAfter ops input row tid iteration t acc s) := by
  have first := begin_round_ready p ops input row tid iteration t acc s ready
  have last := pairs_ready p ops input row tid iteration t 0 4 acc (beginRound t s) first
  rewrite [show extra + 45 = (extra + 43) + 2 by omega,
    begin_round_eq p repaired ops t iteration (extra + 43) s hi ready.pc ready.iterationIndex]
  rewrite [show extra + 43 = (extra + 3) + 10 * 4 by omega,
    pairs_eq p repaired ops input row tid iteration t 0 4 (extra + 3) acc (beginRound t s)
      hi (by decide) first]
  exact end_round_eq p repaired ops t iteration extra _ hi last.pc last.iterationIndex last.pairIndex

theorem round_memory (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t : Nat) (acc : α) (s : State α) :
    (roundAfter ops input row tid iteration t acc s).memory = s.memory :=
  pairs_memory ops input row tid iteration t 0 4 acc (beginRound t s)

theorem round_epochs (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t : Nat) (acc : α) (s : State α) :
    (roundAfter ops input row tid iteration t acc s).epochs = s.epochs :=
  pairs_epochs ops input row tid iteration t 0 4 acc (beginRound t s)

theorem round_trace_length (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t : Nat) (acc : α) (s : State α) :
    (roundAfter ops input row tid iteration t acc s).trace.length = s.trace.length + 8 :=
  pairs_trace_length ops input row tid iteration t 0 4 acc (beginRound t s)

#print axioms begin_round_eq
#print axioms end_round_eq
#print axioms exit_rounds_eq
#print axioms begin_round_ready
#print axioms end_round_ready
#print axioms round_ready
#print axioms round_eq
#print axioms round_memory
#print axioms round_epochs
#print axioms round_trace_length
end LarkNativeSglangRmsNorm
