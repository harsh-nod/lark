import Lark.NativeSglangRmsNormPairRound

/-! Successful native scalar preparation, from the initializer to first shuffle.
All raw half caches and the source's pair grouping remain explicit. -/
namespace LarkNativeSglangRmsNorm
open LarkNonlinear
open LarkReduction (setIndex setReg execute_index_of execute_pure_of)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def sumStarted (ops : Ops α) (t : Nat) (s : State α) : State α :=
  let s := setReg s t 0 (ops.literal 0 1) 28
  let s := setReg s t 1 (ops.literal 0 1) 29
  setIndex s t 13 0 30

def prefixState (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) : State α :=
  let row := t / 1024
  let tid := t % 1024
  let zero := ops.literal 0 1
  let s := sumStarted ops t (preloads input t s)
  let s := roundAfter ops input row tid 0 t zero s
  advance (roundAfter ops input row tid 1 t (pairFold ops input row tid 0 0 4 zero) s) t 44

theorem sum_started_eq (p : Shape) (repaired : Bool) (ops : Ops α)
    (t extra : Nat) (s : State α) (hp : s.pc t = 27) :
    LarkCollective.runLane ops (layout p) (geometry p) (program repaired) t (extra + 3) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program repaired) t extra (sumStarted ops t s) := by
  let s1 := setReg s t 0 (ops.literal 0 1) 28
  let s2 := setReg s1 t 1 (ops.literal 0 1) 29
  have e1 := execute_pure_of ops (layout p) (geometry p) t 0 28 (.lit 0 1) s (ops.literal 0 1)
    (by simp [evalExpr]) (by omega)
  have e2 := execute_pure_of ops (layout p) (geometry p) t 1 29 (.lit 0 1) s1 (ops.literal 0 1)
    (by simp [evalExpr]) (by simp [s1,setReg,advance])
  have e3 := execute_index_of ops (layout p) (geometry p) t 13 30 (.const 0) s2 0 rfl
    (by simp [s2,setReg,advance])
  rewrite [scalar_step p repaired ops t 27 _ _ s s1 (by cases repaired <;> decide) hp e1]
  rewrite [scalar_step p repaired ops t 28 _ _ s1 s2 (by cases repaired <;> decide) (by simp [s1,setReg,advance]) e2]
  exact scalar_step p repaired ops t 29 extra _ s2 _ (by cases repaired <;> decide)
    (by simp [s2,setReg,advance]) e3

theorem initial_sum_started_ready (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (t : Nat) :
    StartReady p input (t / 1024) (t % 1024) 0 t (ops.literal 0 1)
      (sumStarted ops t (preloads input t (initial p input outside))) := by
  obtain ⟨h0,h1⟩ := initial_preloads_indices p input outside t
  obtain ⟨inputs,weights⟩ := initial_preloads_values p input outside t
  exact {
    pc := by simp [sumStarted,setReg,setIndex,advance]
    rowIndex := by simpa [sumStarted,setReg,setIndex,advance] using h0
    tidIndex := by simpa [sumStarted,setReg,setIndex,advance] using h1
    iterationIndex := by simp [sumStarted,setReg,setIndex,advance]
    accumulator := by simp [sumStarted,setReg,setIndex,advance]
    reads := initial_preloads_reads p input outside t
    inputCached := inputs, weightCached := weights
    good := initial_preloads_good p input outside t }

theorem initial_prefix_eq (p : Shape) (repaired : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (t extra : Nat) (ht : t < p.rows * 1024) :
    LarkCollective.runLane ops (layout p) (geometry p) (program repaired) t
      (extra + 330) (initial p input outside) =
    LarkCollective.runLane ops (layout p) (geometry p) (program repaired) t extra
      (prefixState ops input t (initial p input outside)) := by
  let row := t / 1024
  let tid := t % 1024
  let zero := ops.literal 0 1
  let s0 := sumStarted ops t (preloads input t (initial p input outside))
  let acc1 := pairFold ops input row tid 0 0 4 zero
  let s1 := roundAfter ops input row tid 0 t zero s0
  let s2 := roundAfter ops input row tid 1 t acc1 s1
  have hr : row < p.rows := by omega
  have htid : tid < 1024 := Nat.mod_lt _ (by decide)
  have r0 := initial_sum_started_ready p ops input outside t
  have r1 := round_ready p ops input row tid 0 t zero s0 r0
  have r2 := round_ready p ops input row tid 1 t acc1 s1 r1
  rewrite [show extra + 330 = (extra + 94) + 236 by omega,
    initial_preloads_eq p repaired ops input outside t (extra + 94) ht]
  rewrite [show extra + 94 = (extra + 91) + 3 by omega,
    sum_started_eq p repaired ops t (extra + 91) _ (preloads_pc input t _)]
  rewrite [show extra + 91 = (extra + 46) + 45 by omega,
    round_eq p repaired ops input row tid 0 t (extra + 46) zero s0 hr htid (by decide) r0]
  rewrite [show extra + 46 = (extra + 1) + 45 by omega,
    round_eq p repaired ops input row tid 1 t (extra + 1) acc1 s1 hr htid (by decide) r1]
  exact exit_rounds_eq p repaired ops t extra s2 r2.pc r2.iterationIndex

theorem prefix_pc (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) :
    (prefixState ops input t s).pc t = 44 := by simp [prefixState,advance]

theorem initial_prefix_run (p : Shape) (repaired : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (t : Nat) (ht : t < p.rows * 1024) :
    LarkCollective.runLane ops (layout p) (geometry p) (program repaired) t fuel.lane
      (initial p input outside) = some (prefixState ops input t (initial p input outside)) := by
  have parked : LarkCollective.parked (program repaired) (prefixState ops input t (initial p input outside)) t =
      some .shuffle := by
    simp only [LarkCollective.parked,prefix_pc]
    cases repaired <;> rfl
  change LarkCollective.runLane ops (layout p) (geometry p) (program repaired) t (182 + 330) _ = _
  rewrite [initial_prefix_eq p repaired ops input outside t 182 ht]
  simp only [LarkCollective.runLane,parked]

theorem initial_prefix_values (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (t : Nat) :
    (prefixState ops input t (initial p input outside)).regs t 0 =
      some (threadSum ops input (t / 1024) (t % 1024)) ∧
    InputPrefix input (t / 1024) (t % 1024) 16 t (prefixState ops input t (initial p input outside)) ∧
    WeightPrefix input (t % 1024) 16 t (prefixState ops input t (initial p input outside)) := by
  have r0 := initial_sum_started_ready p ops input outside t
  have r1 := round_ready p ops input (t / 1024) (t % 1024) 0 t _ _ r0
  have r2 := round_ready p ops input (t / 1024) (t % 1024) 1 t _ _ r1
  exact ⟨r2.accumulator,r2.inputCached,r2.weightCached⟩

theorem initial_prefix_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (t : Nat) :
    Reads p input (prefixState ops input t (initial p input outside)) := by
  have r0 := initial_sum_started_ready p ops input outside t
  have r1 := round_ready p ops input (t / 1024) (t % 1024) 0 t _ _ r0
  have r2 := round_ready p ops input (t / 1024) (t % 1024) 1 t _ _ r1
  exact r2.reads

theorem initial_prefix_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (t : Nat) :
    ∀ a ∈ (prefixState ops input t (initial p input outside)).trace, Good a := by
  have r0 := initial_sum_started_ready p ops input outside t
  have r1 := round_ready p ops input (t / 1024) (t % 1024) 0 t _ _ r0
  have r2 := round_ready p ops input (t / 1024) (t % 1024) 1 t _ _ r1
  exact r2.good

theorem initial_prefix_race_free (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (t : Nat) :
    raceFree (geometry p) (prefixState ops input t (initial p input outside)).trace = true :=
  race_free p _ (initial_prefix_good p ops input outside t)

theorem prefix_epochs (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) :
    (prefixState ops input t s).epochs = s.epochs := by
  simp only [prefixState,advance,round_epochs,sumStarted,setReg,setIndex,preloads_epochs]

theorem prefix_trace_length (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) :
    (prefixState ops input t s).trace.length = s.trace.length + 80 := by
  simp only [prefixState,advance,round_trace_length,sumStarted,setReg,setIndex,preloads_trace_length]

#print axioms sum_started_eq
#print axioms initial_sum_started_ready
#print axioms initial_prefix_eq
#print axioms prefix_pc
#print axioms initial_prefix_run
#print axioms initial_prefix_values
#print axioms initial_prefix_reads
#print axioms initial_prefix_good
#print axioms initial_prefix_race_free
#print axioms prefix_epochs
#print axioms prefix_trace_length
end LarkNativeSglangRmsNorm
