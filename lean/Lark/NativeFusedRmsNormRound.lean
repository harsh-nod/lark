import Lark.NativeFusedRmsNormLoop

/-! Actual counted-round control, including both false exits. Control steps
preserve memory, traces and epochs; the pinned source and machine are unchanged.
-/
namespace LarkNativeFusedRmsNorm
open LarkNonlinear
open LarkReduction (setIndex execute_index_of int32_cast predicate_lt_of predicate_nlt_of)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def beginRound (t : Nat) (s : State α) : State α :=
  setIndex (advance s t 8) t 5 0 9

def endRound (t iteration : Nat) (s : State α) : State α :=
  advance (setIndex (advance s t 21) t 4 ((iteration + 1 : Nat) : Int) 22) t 7

theorem begin_round_eq (p : Shape) (ops : Ops α) (t iteration extra : Nat) (s : State α)
    (hi : iteration < 2) (hp : s.pc t = 7)
    (h4 : s.indices t 4 = some (iteration : Int)) :
    LarkCollective.runLane ops (layout p) (geometry p) program t (extra + 2) s =
      LarkCollective.runLane ops (layout p) (geometry p) program t extra (beginRound t s) := by
  have pred := predicate_lt_of (geometry p) t s (.ivar 4) (.const 2)
    (iteration : Int) 2 h4 rfl (by omega)
  have e1 : execute ops (layout p) (geometry p) t
      (.branch (.lt (.ivar 4) (.const 2)) 23) s = some (advance s t 8) := by
    simp [execute, pred, hp]
  have e2 := execute_index_of ops (layout p) (geometry p) t 5 9 (.const 0)
    (advance s t 8) 0 rfl (by simp [advance])
  rewrite [scalar_step p ops t 7 _ _ s _ (by decide) hp e1]
  rewrite [scalar_step p ops t 8 _ _ _ _ (by decide) (by simp [advance]) e2]
  rfl

theorem end_round_eq (p : Shape) (ops : Ops α) (t iteration extra : Nat) (s : State α)
    (hi : iteration < 2) (hp : s.pc t = 9)
    (h4 : s.indices t 4 = some (iteration : Int)) (h5 : s.indices t 5 = some 8) :
    LarkCollective.runLane ops (layout p) (geometry p) program t (extra + 3) s =
      LarkCollective.runLane ops (layout p) (geometry p) program t extra (endRound t iteration s) := by
  have pred := predicate_nlt_of (geometry p) t s (.ivar 5) (.const 8) 8 8 h5 rfl (by omega)
  let s1 := advance s t 21
  let s2 := setIndex s1 t 4 ((iteration + 1 : Nat) : Int) 22
  have e1 : execute ops (layout p) (geometry p) t
      (.branch (.lt (.ivar 5) (.const 8)) 21) s = some s1 := by
    simp [execute, pred, hp, s1]
  have he : evalIndex (geometry p) t s1 (.add (.ivar 4) (.const 1)) =
      some ((iteration + 1 : Nat) : Int) :=
    eval_nat_sum (geometry p) t iteration 1 s1 (.ivar 4) (.const 1) h4 rfl (by omega)
  have e2 := execute_index_of ops (layout p) (geometry p) t 4 22
    (.add (.ivar 4) (.const 1)) s1 _ he (by simp [s1, advance])
  change execute _ _ _ _ _ s1 = some s2 at e2
  have e3 : execute ops (layout p) (geometry p) t (.jump 7) s2 = some (endRound t iteration s) := rfl
  rewrite [scalar_step p ops t 9 _ _ s s1 (by decide) hp e1]
  rewrite [scalar_step p ops t 21 _ _ s1 s2 (by decide) (by simp [s1, advance]) e2]
  rewrite [scalar_step p ops t 22 _ _ s2 _ (by decide) (by simp [s2, setIndex, advance]) e3]
  rfl

theorem exit_rounds_eq (p : Shape) (ops : Ops α) (t extra : Nat) (s : State α)
    (hp : s.pc t = 7) (h4 : s.indices t 4 = some 2) :
    LarkCollective.runLane ops (layout p) (geometry p) program t (extra + 1) s =
      LarkCollective.runLane ops (layout p) (geometry p) program t extra (advance s t 23) := by
  have pred := predicate_nlt_of (geometry p) t s (.ivar 4) (.const 2) 2 2 h4 rfl (by omega)
  have e : execute ops (layout p) (geometry p) t
      (.branch (.lt (.ivar 4) (.const 2)) 23) s = some (advance s t 23) := by
    simp [execute, pred, hp]
  exact scalar_step p ops t 7 extra _ s _ (by decide) hp e

structure StartReady (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t : Nat) (acc : α) (s : State α) : Prop where
  pc : s.pc t = 7
  rowIndex : s.indices t 0 = some (row : Int)
  tidIndex : s.indices t 1 = some (tid : Int)
  iterationIndex : s.indices t 4 = some (iteration : Int)
  accumulator : s.regs t 0 = some acc
  pending : Pending input row tid (iteration * 8) s
  completed : Completed ops input row tid t (iteration * 8) s
  good : ∀ a ∈ s.trace, Good a

theorem begin_round_ready (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t : Nat) (acc : α) (s : State α)
    (ready : StartReady ops input row tid iteration t acc s) :
    Ready ops input row tid iteration 0 t acc (beginRound t s) := by
  exact {
    pc := by simp [beginRound, setIndex, advance]
    rowIndex := by simpa [beginRound, setIndex, advance] using ready.rowIndex
    tidIndex := by simpa [beginRound, setIndex, advance] using ready.tidIndex
    iterationIndex := by simpa [beginRound, setIndex, advance] using ready.iterationIndex
    componentIndex := by simp [beginRound, setIndex, advance]
    accumulator := ready.accumulator
    pending := ready.pending
    completed := ready.completed
    good := ready.good }

theorem end_round_ready (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t : Nat) (acc : α) (s : State α)
    (ready : Ready ops input row tid iteration 8 t acc s) :
    StartReady ops input row tid (iteration + 1) t acc (endRound t iteration s) := by
  have hcount : (iteration + 1) * 8 = iteration * 8 + 8 := by omega
  exact {
    pc := by simp [endRound, setIndex, advance]
    rowIndex := by simpa [endRound, setIndex, advance] using ready.rowIndex
    tidIndex := by simpa [endRound, setIndex, advance] using ready.tidIndex
    iterationIndex := by simp [endRound, setIndex, advance]
    accumulator := ready.accumulator
    pending := by simpa only [hcount] using ready.pending
    completed := by simpa only [hcount] using ready.completed
    good := ready.good }

def roundAfter (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t : Nat) (acc : α) (s : State α) : State α :=
  endRound t iteration (components ops input row tid iteration t 0 8 acc (beginRound t s))

theorem round_ready (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t : Nat) (acc : α) (s : State α)
    (ht : tid < 1024) (hi : iteration < 2) (he : t = row * 1024 + tid)
    (ready : StartReady ops input row tid iteration t acc s) :
    StartReady ops input row tid (iteration + 1) t
      (folded ops input row tid iteration 0 8 acc)
      (roundAfter ops input row tid iteration t acc s) :=
  end_round_ready ops input row tid iteration t _ _
    (components_ready p ops input row tid iteration t 0 8 acc (beginRound t s)
      ht hi he (by decide) (begin_round_ready ops input row tid iteration t acc s ready))

theorem round_eq (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t extra : Nat) (acc : α) (s : State α)
    (hr : row < p.rows) (ht : tid < 1024) (hi : iteration < 2) (he : t = row * 1024 + tid)
    (ready : StartReady ops input row tid iteration t acc s) :
    LarkCollective.runLane ops (layout p) (geometry p) program t (extra + 101) s =
      LarkCollective.runLane ops (layout p) (geometry p) program t extra
        (roundAfter ops input row tid iteration t acc s) := by
  have first := begin_round_ready ops input row tid iteration t acc s ready
  have last := components_ready p ops input row tid iteration t 0 8 acc (beginRound t s)
    ht hi he (by decide) first
  rewrite [show extra + 101 = (extra + 99) + 2 by omega,
    begin_round_eq p ops t iteration (extra + 99) s hi ready.pc ready.iterationIndex]
  rewrite [show extra + 99 = (extra + 3) + 12 * 8 by omega,
    components_eq p ops input row tid iteration t 0 8 (extra + 3) acc (beginRound t s)
      hr ht hi he (by decide) first]
  exact end_round_eq p ops t iteration extra _ hi last.pc last.iterationIndex last.componentIndex

theorem round_trace_length (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t : Nat) (acc : α) (s : State α) :
    (roundAfter ops input row tid iteration t acc s).trace.length = s.trace.length + 32 :=
  components_trace_length ops input row tid iteration t 0 8 acc (beginRound t s)

#print axioms begin_round_eq
#print axioms end_round_eq
#print axioms exit_rounds_eq
#print axioms begin_round_ready
#print axioms end_round_ready
#print axioms round_ready
#print axioms round_eq
#print axioms round_trace_length
end LarkNativeFusedRmsNorm
