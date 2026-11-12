import Lark.NativeFlashInferRmsNormOutputLoop

/-! Both counted output-round controls and their false exits. -/
namespace LarkNativeFlashInferRmsNorm
open LarkNonlinear
open LarkReduction (setIndex execute_index_of predicate_lt_of predicate_nlt_of)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def outputBeginRound (t : Nat) (s : State α) : State α :=
  setIndex (advance s t 53) t 9 0 54

def outputEndRound (t iteration : Nat) (s : State α) : State α :=
  advance (setIndex (advance s t 65) t 8 ((iteration + 1 : Nat) : Int) 66) t 52

theorem output_begin_round_eq (p : Shape) (ops : Ops α) (t iteration extra : Nat) (s : State α)
    (hi : iteration < 2) (hp : s.pc t = 52) (h8 : s.indices t 8 = some (iteration : Int)) :
    LarkCollective.runLane ops (layout p) (geometry p) program t (extra + 2) s =
      LarkCollective.runLane ops (layout p) (geometry p) program t extra (outputBeginRound t s) := by
  have pred := predicate_lt_of (geometry p) t s (.ivar 8) (.const 2) (iteration : Int) 2 h8 rfl (by omega)
  have e1 : execute ops (layout p) (geometry p) t (.branch (.lt (.ivar 8) (.const 2)) 67) s =
      some (advance s t 53) := by simp [execute, pred, hp]
  have e2 := execute_index_of ops (layout p) (geometry p) t 9 54 (.const 0)
    (advance s t 53) 0 rfl (by simp [advance])
  rewrite [scalar_step p ops t 52 _ _ s _ (by decide) hp e1]
  rewrite [scalar_step p ops t 53 _ _ _ _ (by decide) (by simp [advance]) e2]
  rfl

theorem output_end_round_eq (p : Shape) (ops : Ops α) (t iteration extra : Nat) (s : State α)
    (hi : iteration < 2) (hp : s.pc t = 54)
    (h8 : s.indices t 8 = some (iteration : Int)) (h9 : s.indices t 9 = some 8) :
    LarkCollective.runLane ops (layout p) (geometry p) program t (extra + 3) s =
      LarkCollective.runLane ops (layout p) (geometry p) program t extra (outputEndRound t iteration s) := by
  have pred := predicate_nlt_of (geometry p) t s (.ivar 9) (.const 8) 8 8 h9 rfl (by omega)
  let s1 := advance s t 65
  let s2 := setIndex s1 t 8 ((iteration + 1 : Nat) : Int) 66
  have e1 : execute ops (layout p) (geometry p) t (.branch (.lt (.ivar 9) (.const 8)) 65) s = some s1 := by
    simp [execute, pred, hp, s1]
  have he := eval_nat_sum (geometry p) t iteration 1 s1 (.ivar 8) (.const 1) h8 rfl (by omega)
  have e2 := execute_index_of ops (layout p) (geometry p) t 8 66 (.add (.ivar 8) (.const 1)) s1 _ he
    (by simp [s1, advance])
  change execute _ _ _ _ _ s1 = some s2 at e2
  have e3 : execute ops (layout p) (geometry p) t (.jump 52) s2 = some (outputEndRound t iteration s) := rfl
  rewrite [scalar_step p ops t 54 _ _ s s1 (by decide) hp e1]
  rewrite [scalar_step p ops t 65 _ _ s1 s2 (by decide) (by simp [s1, advance]) e2]
  rewrite [scalar_step p ops t 66 _ _ s2 _ (by decide) (by simp [s2, setIndex, advance]) e3]
  rfl

theorem output_exit_rounds_eq (p : Shape) (ops : Ops α) (t extra : Nat) (s : State α)
    (hp : s.pc t = 52) (h8 : s.indices t 8 = some 2) :
    LarkCollective.runLane ops (layout p) (geometry p) program t (extra + 1) s =
      LarkCollective.runLane ops (layout p) (geometry p) program t extra (advance s t 67) := by
  have pred := predicate_nlt_of (geometry p) t s (.ivar 8) (.const 2) 2 2 h8 rfl (by omega)
  have e : execute ops (layout p) (geometry p) t (.branch (.lt (.ivar 8) (.const 2)) 67) s =
      some (advance s t 67) := by simp [execute, pred, hp]
  exact scalar_step p ops t 52 extra _ s _ (by decide) hp e

structure OutputStartReady (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t : Nat) (inverse : α) (s : State α) : Prop where
  pc : s.pc t = 52
  rowIndex : s.indices t 0 = some (row : Int)
  tidIndex : s.indices t 1 = some (tid : Int)
  iterationIndex : s.indices t 8 = some (iteration : Int)
  scale : s.regs t 7 = some inverse
  reads : OutputReads ops input row s
  completed : OutputCompleted ops input row tid inverse (iteration * 8) s
  good : ∀ a ∈ s.trace, Good a

theorem output_begin_round_ready (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t : Nat) (inverse : α) (s : State α)
    (ready : OutputStartReady ops input row tid iteration t inverse s) :
    OutputReady ops input row tid iteration 0 t inverse (outputBeginRound t s) := by
  exact {
    pc := by simp [outputBeginRound, setIndex, advance]
    rowIndex := by simpa [outputBeginRound, setIndex, advance] using ready.rowIndex
    tidIndex := by simpa [outputBeginRound, setIndex, advance] using ready.tidIndex
    iterationIndex := by simpa [outputBeginRound, setIndex, advance] using ready.iterationIndex
    componentIndex := by simp [outputBeginRound, setIndex, advance]
    scale := ready.scale
    reads := ready.reads
    completed := by simpa only [Nat.add_zero] using ready.completed
    good := ready.good }

theorem output_end_round_ready (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t : Nat) (inverse : α) (s : State α)
    (ready : OutputReady ops input row tid iteration 8 t inverse s) :
    OutputStartReady ops input row tid (iteration + 1) t inverse (outputEndRound t iteration s) := by
  exact {
    pc := by simp [outputEndRound, setIndex, advance]
    rowIndex := by simpa [outputEndRound, setIndex, advance] using ready.rowIndex
    tidIndex := by simpa [outputEndRound, setIndex, advance] using ready.tidIndex
    iterationIndex := by simp [outputEndRound, setIndex, advance]
    scale := ready.scale
    reads := ready.reads
    completed := by simpa only [show (iteration + 1) * 8 = iteration * 8 + 8 by omega] using ready.completed
    good := ready.good }

def outputRound (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t : Nat) (inverse : α) (s : State α) : State α :=
  outputEndRound t iteration (outputComponents ops input row tid iteration t inverse 0 8 (outputBeginRound t s))

theorem output_round_ready (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t : Nat) (inverse : α) (s : State α)
    (ht : tid < 1024) (hi : iteration < 2) (he : t = row * 1024 + tid)
    (ready : OutputStartReady ops input row tid iteration t inverse s) :
    OutputStartReady ops input row tid (iteration + 1) t inverse (outputRound ops input row tid iteration t inverse s) :=
  output_end_round_ready ops input row tid iteration t inverse _
    (output_components_ready p ops input row tid iteration t 0 8 inverse (outputBeginRound t s)
      ht hi he (by decide) (output_begin_round_ready ops input row tid iteration t inverse s ready))

theorem output_round_eq (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t extra : Nat) (inverse : α) (s : State α)
    (hr : row < p.rows) (ht : tid < 1024) (hi : iteration < 2) (he : t = row * 1024 + tid)
    (ready : OutputStartReady ops input row tid iteration t inverse s) :
    LarkCollective.runLane ops (layout p) (geometry p) program t (extra + 93) s =
      LarkCollective.runLane ops (layout p) (geometry p) program t extra (outputRound ops input row tid iteration t inverse s) := by
  have first := output_begin_round_ready ops input row tid iteration t inverse s ready
  have last := output_components_ready p ops input row tid iteration t 0 8 inverse (outputBeginRound t s) ht hi he (by decide) first
  rewrite [show extra + 93 = (extra + 91) + 2 by omega,
    output_begin_round_eq p ops t iteration (extra + 91) s hi ready.pc ready.iterationIndex]
  rewrite [show extra + 91 = (extra + 3) + 11 * 8 by omega,
    output_components_eq p ops input row tid iteration t 0 8 (extra + 3) inverse (outputBeginRound t s)
      hr ht hi he (by decide) first]
  exact output_end_round_eq p ops t iteration extra _ hi last.pc last.iterationIndex last.componentIndex

theorem output_round_trace_length (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t : Nat) (inverse : α) (s : State α) :
    (outputRound ops input row tid iteration t inverse s).trace.length = s.trace.length + 24 :=
  output_components_trace_length ops input row tid iteration t 0 8 inverse (outputBeginRound t s)

#print axioms output_begin_round_eq
#print axioms output_end_round_eq
#print axioms output_exit_rounds_eq
#print axioms output_begin_round_ready
#print axioms output_end_round_ready
#print axioms output_round_ready
#print axioms output_round_eq
#print axioms output_round_trace_length
end LarkNativeFlashInferRmsNorm
