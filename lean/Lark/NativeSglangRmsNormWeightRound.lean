import Lark.NativeSglangRmsNormWeightLoop

/-! One actual outer weight-vector round: entry, eight raw-half copies and exit.
-/
namespace LarkNativeSglangRmsNorm
open LarkNonlinear
open LarkReduction (setIndex execute_index_of)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def weightCacheEntry (t : Nat) (s : State α) : State α := setIndex (advance s t 18) t 10 0 19
def weightCacheExit (iteration t : Nat) (s : State α) : State α :=
  advance (setIndex (advance s t 25) t 9 ((iteration + 1 : Nat) : Int) 26) t 17
def weightCacheRound (input : Nat → Nat → α) (row tid iteration t : Nat) (s : State α) : State α :=
  weightCacheExit iteration t
    (weightCacheComponents input row tid iteration t 0 8 (weightCacheEntry t s))

structure WeightRoundReady (p : Shape) (input : Nat → Nat → α)
    (row tid iteration t : Nat) (s : State α) : Prop where
  pc : s.pc t = 17
  rowIndex : s.indices t 0 = some (row : Int)
  tidIndex : s.indices t 1 = some (tid : Int)
  iterationIndex : s.indices t 9 = some (iteration : Int)
  reads : Reads p input s
  inputCached : InputPrefix input row tid 16 t s
  cached : WeightPrefix input tid (iteration * 8) t s
  good : ∀ a ∈ s.trace, Good a

theorem weight_cache_entry_eq (p : Shape) (repaired : Bool) (ops : Ops α)
    (iteration t extra : Nat) (s : State α) (hi : iteration < 2)
    (hp : s.pc t = 17) (h4 : s.indices t 9 = some (iteration : Int)) :
    LarkCollective.runLane ops (layout p) (geometry p) (program repaired) t (extra + 2) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program repaired) t extra (weightCacheEntry t s) := by
  have pred := LarkReduction.predicate_lt_of (geometry p) t s (.ivar 9) (.const 2)
    (iteration : Int) 2 h4 rfl (by omega)
  have e1 : execute ops (layout p) (geometry p) t (.branch (.lt (.ivar 9) (.const 2)) 27) s =
      some (advance s t 18) := by
    simp only [execute,pred,hp,bind,pure,Option.bind]
    rfl
  have e2 := execute_index_of ops (layout p) (geometry p) t 10 19 (.const 0)
    (advance s t 18) 0 rfl (by simp [advance])
  rewrite [scalar_step p repaired ops t 17 _ _ s _ (by cases repaired <;> decide) hp e1]
  exact scalar_step p repaired ops t 18 extra _ _ _ (by cases repaired <;> decide)
    (by simp [advance]) e2

theorem weight_cache_exit_eq (p : Shape) (repaired : Bool) (ops : Ops α)
    (iteration t extra : Nat) (s : State α) (hi : iteration < 2)
    (hp : s.pc t = 19) (h4 : s.indices t 9 = some (iteration : Int))
    (h5 : s.indices t 10 = some 8) :
    LarkCollective.runLane ops (layout p) (geometry p) (program repaired) t (extra + 3) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program repaired) t extra (weightCacheExit iteration t s) := by
  let s1 := advance s t 25
  let s2 := setIndex s1 t 9 ((iteration + 1 : Nat) : Int) 26
  have pred := LarkReduction.predicate_nlt_of (geometry p) t s (.ivar 10) (.const 8)
    8 8 h5 rfl (by decide)
  have e1 : execute ops (layout p) (geometry p) t (.branch (.lt (.ivar 10) (.const 8)) 25) s = some s1 := by
    simp only [execute,pred,bind,pure,Option.bind]
    rfl
  have he := eval_nat_sum (geometry p) t iteration 1 s1 (.ivar 9) (.const 1) h4 rfl (by omega)
  have e2 := execute_index_of ops (layout p) (geometry p) t 9 26
    (.add (.ivar 9) (.const 1)) s1 _ he (by simp [s1,advance])
  have e3 : execute ops (layout p) (geometry p) t (.jump 17) s2 = some (weightCacheExit iteration t s) := rfl
  rewrite [scalar_step p repaired ops t 19 _ _ s s1 (by cases repaired <;> decide) hp e1]
  rewrite [scalar_step p repaired ops t 25 _ _ s1 s2 (by cases repaired <;> decide) (by simp [s1,advance]) e2]
  exact scalar_step p repaired ops t 26 extra _ s2 _ (by cases repaired <;> decide)
    (by simp [s2,setIndex,advance]) e3

theorem weight_cache_entry_ready (p : Shape) (input : Nat → Nat → α)
    (row tid iteration t : Nat) (s : State α)
    (ready : WeightRoundReady p input row tid iteration t s) :
    WeightCacheReady p input row tid iteration 0 t (weightCacheEntry t s) := by
  exact {
    pc := by simp [weightCacheEntry,setIndex,advance]
    rowIndex := by simpa [weightCacheEntry,setIndex,advance] using ready.rowIndex
    tidIndex := by simpa [weightCacheEntry,setIndex,advance] using ready.tidIndex
    iterationIndex := by simpa [weightCacheEntry,setIndex,advance] using ready.iterationIndex
    componentIndex := by simp [weightCacheEntry,setIndex,advance]
    reads := ready.reads
    inputCached := ready.inputCached
    cached := by simpa only [Nat.add_zero] using ready.cached
    good := ready.good }

theorem weight_cache_round_ready (p : Shape) (input : Nat → Nat → α)
    (row tid iteration t : Nat) (s : State α)
    (ready : WeightRoundReady p input row tid iteration t s) :
    WeightRoundReady p input row tid (iteration + 1) t (weightCacheRound input row tid iteration t s) := by
  have r := weight_cache_components_ready p input row tid iteration t 0 8 (weightCacheEntry t s)
    (by decide) (weight_cache_entry_ready p input row tid iteration t s ready)
  exact {
    pc := by simp [weightCacheRound,weightCacheExit,setIndex,advance]
    rowIndex := by simpa [weightCacheRound,weightCacheExit,setIndex,advance] using r.rowIndex
    tidIndex := by simpa [weightCacheRound,weightCacheExit,setIndex,advance] using r.tidIndex
    iterationIndex := by simp [weightCacheRound,weightCacheExit,setIndex,advance]
    reads := r.reads
    inputCached := r.inputCached
    cached := by simpa only [Nat.zero_add, Nat.add_mul, Nat.one_mul] using r.cached
    good := r.good }

theorem weight_cache_round_eq (p : Shape) (repaired : Bool) (ops : Ops α)
    (input : Nat → Nat → α) (row tid iteration t extra : Nat) (s : State α)
    (hr : row < p.rows) (ht : tid < 1024) (hi : iteration < 2)
    (ready : WeightRoundReady p input row tid iteration t s) :
    LarkCollective.runLane ops (layout p) (geometry p) (program repaired) t (extra + 53) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program repaired) t extra
        (weightCacheRound input row tid iteration t s) := by
  let entry := weightCacheEntry t s
  let copied := weightCacheComponents input row tid iteration t 0 8 entry
  have r0 := weight_cache_entry_ready p input row tid iteration t s ready
  have r8 := weight_cache_components_ready p input row tid iteration t 0 8 entry (by decide) r0
  rewrite [show extra + 53 = (extra + 51) + 2 by omega,
    weight_cache_entry_eq p repaired ops iteration t (extra + 51) s hi ready.pc ready.iterationIndex]
  rewrite [show extra + 51 = (extra + 3) + 6 * 8 by omega,
    weight_cache_components_eq p repaired ops input row tid iteration t 0 8 (extra + 3) entry
      hr ht hi (by decide) r0]
  exact weight_cache_exit_eq p repaired ops iteration t extra copied hi r8.pc r8.iterationIndex r8.componentIndex

theorem weight_cache_round_epochs (input : Nat → Nat → α)
    (row tid iteration t : Nat) (s : State α) :
    (weightCacheRound input row tid iteration t s).epochs = s.epochs := by
  simp only [weightCacheRound,weightCacheExit,setIndex,advance,weight_cache_components_epochs,weightCacheEntry]

theorem weight_cache_round_trace_length (input : Nat → Nat → α)
    (row tid iteration t : Nat) (s : State α) :
    (weightCacheRound input row tid iteration t s).trace.length = s.trace.length + 16 := by
  simp only [weightCacheRound,weightCacheExit,setIndex,advance,weight_cache_components_trace_length,weightCacheEntry]

#print axioms weight_cache_entry_eq
#print axioms weight_cache_exit_eq
#print axioms weight_cache_entry_ready
#print axioms weight_cache_round_ready
#print axioms weight_cache_round_eq
#print axioms weight_cache_round_epochs
#print axioms weight_cache_round_trace_length
end LarkNativeSglangRmsNorm
