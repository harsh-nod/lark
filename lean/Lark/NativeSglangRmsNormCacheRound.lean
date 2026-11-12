import Lark.NativeSglangRmsNormCacheLoop

/-! One actual outer input-vector round: entry, eight raw-half copies and exit.
-/
namespace LarkNativeSglangRmsNorm
open LarkNonlinear
open LarkReduction (setIndex execute_index_of)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def inputCacheEntry (t : Nat) (s : State α) : State α := setIndex (advance s t 6) t 5 0 7
def inputCacheExit (iteration t : Nat) (s : State α) : State α :=
  advance (setIndex (advance s t 14) t 4 ((iteration + 1 : Nat) : Int) 15) t 5
def inputCacheRound (input : Nat → Nat → α) (row tid iteration t : Nat) (s : State α) : State α :=
  inputCacheExit iteration t
    (inputCacheComponents input row tid iteration t 0 8 (inputCacheEntry t s))

structure InputRoundReady (p : Shape) (input : Nat → Nat → α)
    (row tid iteration t : Nat) (s : State α) : Prop where
  pc : s.pc t = 5
  rowIndex : s.indices t 0 = some (row : Int)
  tidIndex : s.indices t 1 = some (tid : Int)
  iterationIndex : s.indices t 4 = some (iteration : Int)
  reads : Reads p input s
  cached : InputPrefix input row tid (iteration * 8) t s
  good : ∀ a ∈ s.trace, Good a

theorem input_cache_entry_eq (p : Shape) (repaired : Bool) (ops : Ops α)
    (iteration t extra : Nat) (s : State α) (hi : iteration < 2)
    (hp : s.pc t = 5) (h4 : s.indices t 4 = some (iteration : Int)) :
    LarkCollective.runLane ops (layout p) (geometry p) (program repaired) t (extra + 2) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program repaired) t extra (inputCacheEntry t s) := by
  have pred := LarkReduction.predicate_lt_of (geometry p) t s (.ivar 4) (.const 2)
    (iteration : Int) 2 h4 rfl (by omega)
  have e1 : execute ops (layout p) (geometry p) t (.branch (.lt (.ivar 4) (.const 2)) 16) s =
      some (advance s t 6) := by
    simp only [execute,pred,hp,bind,pure,Option.bind]
    rfl
  have e2 := execute_index_of ops (layout p) (geometry p) t 5 7 (.const 0)
    (advance s t 6) 0 rfl (by simp [advance])
  rewrite [scalar_step p repaired ops t 5 _ _ s _ (by cases repaired <;> decide) hp e1]
  exact scalar_step p repaired ops t 6 extra _ _ _ (by cases repaired <;> decide)
    (by simp [advance]) e2

theorem input_cache_exit_eq (p : Shape) (repaired : Bool) (ops : Ops α)
    (iteration t extra : Nat) (s : State α) (hi : iteration < 2)
    (hp : s.pc t = 7) (h4 : s.indices t 4 = some (iteration : Int))
    (h5 : s.indices t 5 = some 8) :
    LarkCollective.runLane ops (layout p) (geometry p) (program repaired) t (extra + 3) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program repaired) t extra (inputCacheExit iteration t s) := by
  let s1 := advance s t 14
  let s2 := setIndex s1 t 4 ((iteration + 1 : Nat) : Int) 15
  have pred := LarkReduction.predicate_nlt_of (geometry p) t s (.ivar 5) (.const 8)
    8 8 h5 rfl (by decide)
  have e1 : execute ops (layout p) (geometry p) t (.branch (.lt (.ivar 5) (.const 8)) 14) s = some s1 := by
    simp only [execute,pred,bind,pure,Option.bind]
    rfl
  have he := eval_nat_sum (geometry p) t iteration 1 s1 (.ivar 4) (.const 1) h4 rfl (by omega)
  have e2 := execute_index_of ops (layout p) (geometry p) t 4 15
    (.add (.ivar 4) (.const 1)) s1 _ he (by simp [s1,advance])
  have e3 : execute ops (layout p) (geometry p) t (.jump 5) s2 = some (inputCacheExit iteration t s) := rfl
  rewrite [scalar_step p repaired ops t 7 _ _ s s1 (by cases repaired <;> decide) hp e1]
  rewrite [scalar_step p repaired ops t 14 _ _ s1 s2 (by cases repaired <;> decide) (by simp [s1,advance]) e2]
  exact scalar_step p repaired ops t 15 extra _ s2 _ (by cases repaired <;> decide)
    (by simp [s2,setIndex,advance]) e3

theorem input_cache_entry_ready (p : Shape) (input : Nat → Nat → α)
    (row tid iteration t : Nat) (s : State α)
    (ready : InputRoundReady p input row tid iteration t s) :
    InputCacheReady p input row tid iteration 0 t (inputCacheEntry t s) := by
  exact {
    pc := by simp [inputCacheEntry,setIndex,advance]
    rowIndex := by simpa [inputCacheEntry,setIndex,advance] using ready.rowIndex
    tidIndex := by simpa [inputCacheEntry,setIndex,advance] using ready.tidIndex
    iterationIndex := by simpa [inputCacheEntry,setIndex,advance] using ready.iterationIndex
    componentIndex := by simp [inputCacheEntry,setIndex,advance]
    reads := ready.reads
    cached := by simpa only [Nat.add_zero] using ready.cached
    good := ready.good }

theorem input_cache_round_ready (p : Shape) (input : Nat → Nat → α)
    (row tid iteration t : Nat) (s : State α)
    (ready : InputRoundReady p input row tid iteration t s) :
    InputRoundReady p input row tid (iteration + 1) t (inputCacheRound input row tid iteration t s) := by
  have r := input_cache_components_ready p input row tid iteration t 0 8 (inputCacheEntry t s)
    (by decide) (input_cache_entry_ready p input row tid iteration t s ready)
  exact {
    pc := by simp [inputCacheRound,inputCacheExit,setIndex,advance]
    rowIndex := by simpa [inputCacheRound,inputCacheExit,setIndex,advance] using r.rowIndex
    tidIndex := by simpa [inputCacheRound,inputCacheExit,setIndex,advance] using r.tidIndex
    iterationIndex := by simp [inputCacheRound,inputCacheExit,setIndex,advance]
    reads := r.reads
    cached := by simpa only [Nat.zero_add, Nat.add_mul, Nat.one_mul] using r.cached
    good := r.good }

theorem input_cache_round_eq (p : Shape) (repaired : Bool) (ops : Ops α)
    (input : Nat → Nat → α) (row tid iteration t extra : Nat) (s : State α)
    (hr : row < p.rows) (ht : tid < 1024) (hi : iteration < 2)
    (ready : InputRoundReady p input row tid iteration t s) :
    LarkCollective.runLane ops (layout p) (geometry p) (program repaired) t (extra + 61) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program repaired) t extra
        (inputCacheRound input row tid iteration t s) := by
  let entry := inputCacheEntry t s
  let copied := inputCacheComponents input row tid iteration t 0 8 entry
  have r0 := input_cache_entry_ready p input row tid iteration t s ready
  have r8 := input_cache_components_ready p input row tid iteration t 0 8 entry (by decide) r0
  rewrite [show extra + 61 = (extra + 59) + 2 by omega,
    input_cache_entry_eq p repaired ops iteration t (extra + 59) s hi ready.pc ready.iterationIndex]
  rewrite [show extra + 59 = (extra + 3) + 7 * 8 by omega,
    input_cache_components_eq p repaired ops input row tid iteration t 0 8 (extra + 3) entry
      hr ht hi (by decide) r0]
  exact input_cache_exit_eq p repaired ops iteration t extra copied hi r8.pc r8.iterationIndex r8.componentIndex

theorem input_cache_round_epochs (input : Nat → Nat → α)
    (row tid iteration t : Nat) (s : State α) :
    (inputCacheRound input row tid iteration t s).epochs = s.epochs := by
  simp only [inputCacheRound,inputCacheExit,setIndex,advance,input_cache_components_epochs,inputCacheEntry]

theorem input_cache_round_trace_length (input : Nat → Nat → α)
    (row tid iteration t : Nat) (s : State α) :
    (inputCacheRound input row tid iteration t s).trace.length = s.trace.length + 16 := by
  simp only [inputCacheRound,inputCacheExit,setIndex,advance,input_cache_components_trace_length,inputCacheEntry]

#print axioms input_cache_entry_eq
#print axioms input_cache_exit_eq
#print axioms input_cache_entry_ready
#print axioms input_cache_round_ready
#print axioms input_cache_round_eq
#print axioms input_cache_round_epochs
#print axioms input_cache_round_trace_length
end LarkNativeSglangRmsNorm
