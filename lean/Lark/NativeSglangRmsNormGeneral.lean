import Lark.NativeSglangRmsNormPrefix

/-! The same native scalar prefix from carried machine state. This intermediate
module requires a classified prior trace; trace transport removes that premise
for execution-only conclusions in a separate module. -/
namespace LarkNativeSglangRmsNorm
open LarkNonlinear
open LarkReduction (setIndex)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem general_input_round_ready (p : Shape) (input : Nat → Nat → α) (t : Nat) (s : State α)
    (reads : Reads p input s) (good : ∀ a ∈ s.trace, Good a) :
    InputRoundReady p input (t / 1024) (t % 1024) 0 t (initialized t s) := by
  obtain ⟨hp,h0,h1,_,_,h4⟩ := initialized_fields t s
  exact { pc := hp, rowIndex := h0, tidIndex := h1, iterationIndex := h4
          reads := reads, cached := by intro k hk; omega
          good := good }

structure InputPrepared (p : Shape) (input : Nat → Nat → α) (t : Nat) (s : State α) : Prop where
  pc : s.pc t = 16
  rowIndex : s.indices t 0 = some ((t / 1024 : Nat) : Int)
  tidIndex : s.indices t 1 = some ((t % 1024 : Nat) : Int)
  reads : Reads p input s
  cached : InputPrefix input (t / 1024) (t % 1024) 16 t s
  good : ∀ a ∈ s.trace, Good a

theorem general_input_prepared (p : Shape) (input : Nat → Nat → α) (t : Nat) (s : State α)
    (reads : Reads p input s) (good : ∀ a ∈ s.trace, Good a) :
    InputPrepared p input t (inputPreloads input t s) := by
  have r0 := general_input_round_ready p input t s reads good
  have r1 := input_cache_round_ready p input (t / 1024) (t % 1024) 0 t _ r0
  have r2 := input_cache_round_ready p input (t / 1024) (t % 1024) 1 t _ r1
  exact ⟨input_preloads_pc input t s,r2.rowIndex,r2.tidIndex,r2.reads,r2.cached,r2.good⟩

theorem general_input_eq (p : Shape) (repaired : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (t extra : Nat) (s : State α) (ht : t < p.rows * 1024) (hp : s.pc t = 0)
    (reads : Reads p input s) (good : ∀ a ∈ s.trace, Good a) :
    LarkCollective.runLane ops (layout p) (geometry p) (program repaired) t (extra + 128) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program repaired) t extra (inputPreloads input t s) := by
  let row := t / 1024
  let tid := t % 1024
  let s0 := initialized t s
  let s1 := inputCacheRound input row tid 0 t s0
  let s2 := inputCacheRound input row tid 1 t s1
  have hr : row < p.rows := by omega
  have htid : tid < 1024 := Nat.mod_lt _ (by decide)
  have r0 := general_input_round_ready p input t s reads good
  have r1 := input_cache_round_ready p input row tid 0 t s0 r0
  have r2 := input_cache_round_ready p input row tid 1 t s1 r1
  have pred := LarkReduction.predicate_nlt_of (geometry p) t s2 (.ivar 4) (.const 2)
    2 2 r2.iterationIndex rfl (by decide)
  have he : execute ops (layout p) (geometry p) t (.branch (.lt (.ivar 4) (.const 2)) 16) s2 =
      some (advance s2 t 16) := by
    simp only [execute,pred,bind,pure,Option.bind]
    rfl
  rewrite [show extra + 128 = (extra + 123) + 5 by omega,
    initialized_eq p repaired ops t (extra + 123) s ht hp]
  rewrite [show extra + 123 = (extra + 62) + 61 by omega,
    input_cache_round_eq p repaired ops input row tid 0 t (extra + 62) s0 hr htid (by decide) r0]
  rewrite [show extra + 62 = (extra + 1) + 61 by omega,
    input_cache_round_eq p repaired ops input row tid 1 t (extra + 1) s1 hr htid (by decide) r1]
  exact scalar_step p repaired ops t 5 extra _ s2 _ (by cases repaired <;> decide) r2.pc he

theorem general_weight_round_ready (p : Shape) (input : Nat → Nat → α) (t : Nat) (s : State α)
    (reads : Reads p input s) (good : ∀ a ∈ s.trace, Good a) :
    WeightRoundReady p input (t / 1024) (t % 1024) 0 t
      (setIndex (inputPreloads input t s) t 9 0 17) := by
  have r := general_input_prepared p input t s reads good
  exact {
    pc := by simp [setIndex,advance]
    rowIndex := by simpa [setIndex,advance] using r.rowIndex
    tidIndex := by simpa [setIndex,advance] using r.tidIndex
    iterationIndex := by simp [setIndex,advance]
    reads := r.reads, inputCached := r.cached
    cached := by intro k hk; omega
    good := r.good }

structure PreloadsPrepared (p : Shape) (input : Nat → Nat → α) (t : Nat) (s : State α) : Prop where
  pc : s.pc t = 27
  rowIndex : s.indices t 0 = some ((t / 1024 : Nat) : Int)
  tidIndex : s.indices t 1 = some ((t % 1024 : Nat) : Int)
  reads : Reads p input s
  inputs : InputPrefix input (t / 1024) (t % 1024) 16 t s
  weights : WeightPrefix input (t % 1024) 16 t s
  good : ∀ a ∈ s.trace, Good a

theorem general_preloads_prepared (p : Shape) (input : Nat → Nat → α) (t : Nat) (s : State α)
    (reads : Reads p input s) (good : ∀ a ∈ s.trace, Good a) :
    PreloadsPrepared p input t (preloads input t s) := by
  have r0 := general_weight_round_ready p input t s reads good
  have r1 := weight_cache_round_ready p input (t / 1024) (t % 1024) 0 t _ r0
  have r2 := weight_cache_round_ready p input (t / 1024) (t % 1024) 1 t _ r1
  exact ⟨preloads_pc input t s,r2.rowIndex,r2.tidIndex,r2.reads,r2.inputCached,r2.cached,r2.good⟩

theorem general_preloads_eq (p : Shape) (repaired : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (t extra : Nat) (s : State α) (ht : t < p.rows * 1024) (hp : s.pc t = 0)
    (reads : Reads p input s) (good : ∀ a ∈ s.trace, Good a) :
    LarkCollective.runLane ops (layout p) (geometry p) (program repaired) t (extra + 236) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program repaired) t extra (preloads input t s) := by
  let row := t / 1024
  let tid := t % 1024
  let si := inputPreloads input t s
  let s0 := setIndex si t 9 0 17
  let s1 := weightCacheRound input row tid 0 t s0
  let s2 := weightCacheRound input row tid 1 t s1
  have hr : row < p.rows := by omega
  have htid : tid < 1024 := Nat.mod_lt _ (by decide)
  have r0 := general_weight_round_ready p input t s reads good
  have r1 := weight_cache_round_ready p input row tid 0 t s0 r0
  have r2 := weight_cache_round_ready p input row tid 1 t s1 r1
  have e0 := LarkReduction.execute_index_of ops (layout p) (geometry p) t 9 17 (.const 0) si 0 rfl
    (by simp [si,input_preloads_pc])
  have pred := LarkReduction.predicate_nlt_of (geometry p) t s2 (.ivar 9) (.const 2)
    2 2 r2.iterationIndex rfl (by decide)
  have he : execute ops (layout p) (geometry p) t (.branch (.lt (.ivar 9) (.const 2)) 27) s2 =
      some (advance s2 t 27) := by
    simp only [execute,pred,bind,pure,Option.bind]
    rfl
  rewrite [show extra + 236 = (extra + 108) + 128 by omega,
    general_input_eq p repaired ops input t (extra + 108) s ht hp reads good]
  rewrite [show extra + 108 = (extra + 107) + 1 by omega,
    scalar_step p repaired ops t 16 (extra + 107) _ si s0 (by cases repaired <;> decide)
      (input_preloads_pc input t _) e0]
  rewrite [show extra + 107 = (extra + 54) + 53 by omega,
    weight_cache_round_eq p repaired ops input row tid 0 t (extra + 54) s0 hr htid (by decide) r0]
  rewrite [show extra + 54 = (extra + 1) + 53 by omega,
    weight_cache_round_eq p repaired ops input row tid 1 t (extra + 1) s1 hr htid (by decide) r1]
  exact scalar_step p repaired ops t 17 extra _ s2 _ (by cases repaired <;> decide) r2.pc he

theorem general_sum_ready (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t : Nat) (s : State α) (reads : Reads p input s) (good : ∀ a ∈ s.trace, Good a) :
    StartReady p input (t / 1024) (t % 1024) 0 t (ops.literal 0 1)
      (sumStarted ops t (preloads input t s)) := by
  have r := general_preloads_prepared p input t s reads good
  exact {
    pc := by simp [sumStarted,LarkReduction.setReg,setIndex,advance]
    rowIndex := by simpa [sumStarted,LarkReduction.setReg,setIndex,advance] using r.rowIndex
    tidIndex := by simpa [sumStarted,LarkReduction.setReg,setIndex,advance] using r.tidIndex
    iterationIndex := by simp [sumStarted,LarkReduction.setReg,setIndex,advance]
    accumulator := by simp [sumStarted,LarkReduction.setReg,setIndex,advance]
    reads := r.reads, inputCached := r.inputs, weightCached := r.weights, good := r.good }

theorem general_prefix_eq (p : Shape) (repaired : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (t extra : Nat) (s : State α) (ht : t < p.rows * 1024) (hp : s.pc t = 0)
    (reads : Reads p input s) (good : ∀ a ∈ s.trace, Good a) :
    LarkCollective.runLane ops (layout p) (geometry p) (program repaired) t (extra + 330) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program repaired) t extra (prefixState ops input t s) := by
  let row := t / 1024
  let tid := t % 1024
  let zero := ops.literal 0 1
  let s0 := sumStarted ops t (preloads input t s)
  let acc1 := pairFold ops input row tid 0 0 4 zero
  let s1 := roundAfter ops input row tid 0 t zero s0
  let s2 := roundAfter ops input row tid 1 t acc1 s1
  have hr : row < p.rows := by omega
  have htid : tid < 1024 := Nat.mod_lt _ (by decide)
  have r0 := general_sum_ready p ops input t s reads good
  have r1 := round_ready p ops input row tid 0 t zero s0 r0
  have r2 := round_ready p ops input row tid 1 t acc1 s1 r1
  rewrite [show extra + 330 = (extra + 94) + 236 by omega,
    general_preloads_eq p repaired ops input t (extra + 94) s ht hp reads good]
  rewrite [show extra + 94 = (extra + 91) + 3 by omega,
    sum_started_eq p repaired ops t (extra + 91) _ (preloads_pc input t _)]
  rewrite [show extra + 91 = (extra + 46) + 45 by omega,
    round_eq p repaired ops input row tid 0 t (extra + 46) zero s0 hr htid (by decide) r0]
  rewrite [show extra + 46 = (extra + 1) + 45 by omega,
    round_eq p repaired ops input row tid 1 t (extra + 1) acc1 s1 hr htid (by decide) r1]
  exact exit_rounds_eq p repaired ops t extra s2 r2.pc r2.iterationIndex

structure GeneralPrefixReady (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t : Nat) (s : State α) : Prop where
  pc : s.pc t = 44
  accumulator : s.regs t 0 = some (threadSum ops input (t / 1024) (t % 1024))
  reads : Reads p input s
  inputs : InputPrefix input (t / 1024) (t % 1024) 16 t s
  weights : WeightPrefix input (t % 1024) 16 t s
  good : ∀ a ∈ s.trace, Good a

theorem general_prefix_ready (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t : Nat) (s : State α) (reads : Reads p input s) (good : ∀ a ∈ s.trace, Good a) :
    GeneralPrefixReady p ops input t (prefixState ops input t s) := by
  have r0 := general_sum_ready p ops input t s reads good
  have r1 := round_ready p ops input (t / 1024) (t % 1024) 0 t _ _ r0
  have r2 := round_ready p ops input (t / 1024) (t % 1024) 1 t _ _ r1
  exact ⟨prefix_pc ops input t s,r2.accumulator,r2.reads,r2.inputCached,r2.weightCached,r2.good⟩

theorem general_prefix_run (p : Shape) (repaired : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (t : Nat) (s : State α) (ht : t < p.rows * 1024) (hp : s.pc t = 0)
    (reads : Reads p input s) (good : ∀ a ∈ s.trace, Good a) :
    LarkCollective.runLane ops (layout p) (geometry p) (program repaired) t fuel.lane s =
      some (prefixState ops input t s) := by
  have parked : LarkCollective.parked (program repaired) (prefixState ops input t s) t = some .shuffle := by
    simp only [LarkCollective.parked,prefix_pc]
    cases repaired <;> rfl
  change LarkCollective.runLane ops (layout p) (geometry p) (program repaired) t (182 + 330) s = _
  rewrite [general_prefix_eq p repaired ops input t 182 s ht hp reads good]
  simp only [LarkCollective.runLane,parked]

#print axioms general_input_round_ready
#print axioms general_input_prepared
#print axioms general_input_eq
#print axioms general_weight_round_ready
#print axioms general_preloads_prepared
#print axioms general_preloads_eq
#print axioms general_sum_ready
#print axioms general_prefix_eq
#print axioms general_prefix_ready
#print axioms general_prefix_run
end LarkNativeSglangRmsNorm
