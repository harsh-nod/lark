import Lark.NativeSglangRmsNormWeightRound

/-! Scalar prefix equation through all raw input/weight caches, before PC27.
No continuation to the first collective instruction is asserted here. -/
namespace LarkNativeSglangRmsNorm
open LarkNonlinear
open LarkReduction (setIndex execute_index_of)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def weightPreloads (input : Nat → Nat → α) (t : Nat) (s : State α) : State α :=
  let row := t / 1024
  let tid := t % 1024
  let s := setIndex s t 9 0 17
  let s := weightCacheRound input row tid 0 t s
  advance (weightCacheRound input row tid 1 t s) t 27

def preloads (input : Nat → Nat → α) (t : Nat) (s : State α) : State α :=
  weightPreloads input t (inputPreloads input t s)

theorem initial_input_preloads_indices (p : Shape) (input : Nat → Nat → α)
    (outside : Location → Option α) (t : Nat) :
    (inputPreloads input t (initial p input outside)).indices t 0 = some ((t / 1024 : Nat) : Int) ∧
    (inputPreloads input t (initial p input outside)).indices t 1 = some ((t % 1024 : Nat) : Int) := by
  have r0 := initial_input_round_ready p input outside t
  have r1 := input_cache_round_ready p input (t / 1024) (t % 1024) 0 t _ r0
  have r2 := input_cache_round_ready p input (t / 1024) (t % 1024) 1 t _ r1
  exact ⟨r2.rowIndex,r2.tidIndex⟩

theorem initial_weight_round_ready (p : Shape) (input : Nat → Nat → α)
    (outside : Location → Option α) (t : Nat) :
    WeightRoundReady p input (t / 1024) (t % 1024) 0 t
      (setIndex (inputPreloads input t (initial p input outside)) t 9 0 17) := by
  obtain ⟨h0,h1⟩ := initial_input_preloads_indices p input outside t
  exact {
    pc := by simp [setIndex,advance]
    rowIndex := by simpa [setIndex,advance] using h0
    tidIndex := by simpa [setIndex,advance] using h1
    iterationIndex := by simp [setIndex,advance]
    reads := initial_input_preloads_reads p input outside t
    inputCached := initial_input_preloads_values p input outside t
    cached := by intro k hk; omega
    good := initial_input_preloads_good p input outside t }

theorem initial_preloads_eq (p : Shape) (repaired : Bool) (ops : Ops α)
    (input : Nat → Nat → α) (outside : Location → Option α)
    (t extra : Nat) (ht : t < p.rows * 1024) :
    LarkCollective.runLane ops (layout p) (geometry p) (program repaired) t
      (extra + 236) (initial p input outside) =
    LarkCollective.runLane ops (layout p) (geometry p) (program repaired) t extra
      (preloads input t (initial p input outside)) := by
  let row := t / 1024
  let tid := t % 1024
  let si := inputPreloads input t (initial p input outside)
  let s0 := setIndex si t 9 0 17
  let s1 := weightCacheRound input row tid 0 t s0
  let s2 := weightCacheRound input row tid 1 t s1
  have hr : row < p.rows := by omega
  have htid : tid < 1024 := Nat.mod_lt _ (by decide)
  have r0 := initial_weight_round_ready p input outside t
  have r1 := weight_cache_round_ready p input row tid 0 t s0 r0
  have r2 := weight_cache_round_ready p input row tid 1 t s1 r1
  have e0 := execute_index_of ops (layout p) (geometry p) t 9 17 (.const 0) si 0 rfl
    (by simp [si,input_preloads_pc])
  have pred := LarkReduction.predicate_nlt_of (geometry p) t s2 (.ivar 9) (.const 2)
    2 2 r2.iterationIndex rfl (by decide)
  have he : execute ops (layout p) (geometry p) t (.branch (.lt (.ivar 9) (.const 2)) 27) s2 =
      some (advance s2 t 27) := by
    simp only [execute,pred,bind,pure,Option.bind]
    rfl
  rewrite [show extra + 236 = (extra + 108) + 128 by omega,
    initial_input_preloads_eq p repaired ops input outside t (extra + 108) ht]
  rewrite [show extra + 108 = (extra + 107) + 1 by omega,
    scalar_step p repaired ops t 16 (extra + 107) _ si s0 (by cases repaired <;> decide)
      (input_preloads_pc input t _) e0]
  rewrite [show extra + 107 = (extra + 54) + 53 by omega,
    weight_cache_round_eq p repaired ops input row tid 0 t (extra + 54) s0 hr htid (by decide) r0]
  rewrite [show extra + 54 = (extra + 1) + 53 by omega,
    weight_cache_round_eq p repaired ops input row tid 1 t (extra + 1) s1 hr htid (by decide) r1]
  exact scalar_step p repaired ops t 17 extra _ s2 _ (by cases repaired <;> decide) r2.pc he

theorem initial_preloads_values (p : Shape) (input : Nat → Nat → α)
    (outside : Location → Option α) (t : Nat) :
    InputPrefix input (t / 1024) (t % 1024) 16 t (preloads input t (initial p input outside)) ∧
    WeightPrefix input (t % 1024) 16 t (preloads input t (initial p input outside)) := by
  have r0 := initial_weight_round_ready p input outside t
  have r1 := weight_cache_round_ready p input (t / 1024) (t % 1024) 0 t _ r0
  have r2 := weight_cache_round_ready p input (t / 1024) (t % 1024) 1 t _ r1
  exact ⟨r2.inputCached,r2.cached⟩

theorem initial_preloads_reads (p : Shape) (input : Nat → Nat → α)
    (outside : Location → Option α) (t : Nat) :
    Reads p input (preloads input t (initial p input outside)) := by
  have r0 := initial_weight_round_ready p input outside t
  have r1 := weight_cache_round_ready p input (t / 1024) (t % 1024) 0 t _ r0
  have r2 := weight_cache_round_ready p input (t / 1024) (t % 1024) 1 t _ r1
  exact r2.reads

theorem initial_preloads_good (p : Shape) (input : Nat → Nat → α)
    (outside : Location → Option α) (t : Nat) :
    ∀ a ∈ (preloads input t (initial p input outside)).trace, Good a := by
  have r0 := initial_weight_round_ready p input outside t
  have r1 := weight_cache_round_ready p input (t / 1024) (t % 1024) 0 t _ r0
  have r2 := weight_cache_round_ready p input (t / 1024) (t % 1024) 1 t _ r1
  exact r2.good

theorem initial_preloads_indices (p : Shape) (input : Nat → Nat → α)
    (outside : Location → Option α) (t : Nat) :
    (preloads input t (initial p input outside)).indices t 0 = some ((t / 1024 : Nat) : Int) ∧
    (preloads input t (initial p input outside)).indices t 1 = some ((t % 1024 : Nat) : Int) := by
  have r0 := initial_weight_round_ready p input outside t
  have r1 := weight_cache_round_ready p input (t / 1024) (t % 1024) 0 t _ r0
  have r2 := weight_cache_round_ready p input (t / 1024) (t % 1024) 1 t _ r1
  exact ⟨r2.rowIndex,r2.tidIndex⟩

theorem initial_preloads_race_free (p : Shape) (input : Nat → Nat → α)
    (outside : Location → Option α) (t : Nat) :
    raceFree (geometry p) (preloads input t (initial p input outside)).trace = true :=
  race_free p _ (initial_preloads_good p input outside t)

theorem preloads_pc (input : Nat → Nat → α) (t : Nat) (s : State α) :
    (preloads input t s).pc t = 27 := by simp [preloads,weightPreloads,advance]

theorem preloads_epochs (input : Nat → Nat → α) (t : Nat) (s : State α) :
    (preloads input t s).epochs = s.epochs := by
  simp only [preloads,weightPreloads,advance,weight_cache_round_epochs,setIndex,input_preloads_epochs]

theorem preloads_trace_length (input : Nat → Nat → α) (t : Nat) (s : State α) :
    (preloads input t s).trace.length = s.trace.length + 64 := by
  simp only [preloads,weightPreloads,advance,weight_cache_round_trace_length,setIndex,input_preloads_trace_length]

#print axioms initial_input_preloads_indices
#print axioms initial_weight_round_ready
#print axioms initial_preloads_eq
#print axioms initial_preloads_values
#print axioms initial_preloads_reads
#print axioms initial_preloads_good
#print axioms initial_preloads_indices
#print axioms initial_preloads_race_free
#print axioms preloads_pc
#print axioms preloads_epochs
#print axioms preloads_trace_length
end LarkNativeSglangRmsNorm
