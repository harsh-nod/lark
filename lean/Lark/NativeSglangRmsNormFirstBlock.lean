import Lark.NativeSglangRmsNormBlockData

/-! Actual first-phase block traces. The repair classifies every recorded
access; the original conflict survives the remaining fifteen waves. Barrier
resumption itself records no access. Whole-kernel completion is still pending.
-/
namespace LarkNativeSglangRmsNorm
open LarkNonlinear LarkCollective
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
attribute [local irreducible] prefixFold reductionSnapshot partialFold firstBlockFold

theorem carried_fixed_wave_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row w : Nat) (s : State α) (reads : Reads p input s)
    (epochs : ∀ t∈cohortThreads row w 64,(s.epochs t).block=0) (good : ∀ event∈s.trace,Good event) :
    ∀ event∈(wavePartial p true ops input row w s).trace,Good event := by
  apply fixed_partial_fold_good ops _ _ _ _
  · intro t ht
    rw [(wave_last_snapshot_preserves p ops input row w s).2.2.1]
    exact epochs t ht
  · rw [(wave_last_snapshot_preserves p ops input row w s).2.2.2]
    exact prefix_fold_good p ops input _ s reads good

theorem fixed_first_block_fold_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ws : List Nat) (s : State α) (bounds : ∀ w∈ws,w<16) (reads : Reads p input s)
    (epochs : ∀ t∈blockThreads (geometry p) row,(s.epochs t).block=0) (good : ∀ event∈s.trace,Good event) :
    ∀ event∈(firstBlockFold p true ops input row ws s).trace,Good event := by
  induction ws generalizing s with
  | nil => simpa only [firstBlockFold,List.foldl_nil] using good
  | cons w ws ih =>
      rw [first_block_fold_cons]
      apply ih (wavePartial p true ops input row w s)
      · intro v hv; exact bounds v (by simp [hv])
      · exact wave_partial_reads p true ops input row w s reads
      · intro t ht
        rw [(wave_partial_indices_epochs p true ops input row w s).2]
        exact epochs t ht
      · exact carried_fixed_wave_good p ops input row w s reads
          (fun t ht => epochs t (cohort_in_block p row w t (bounds w (by simp)) ht)) good

theorem initial_fixed_first_block_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row : Nat) :
    ∀ event∈(firstBlockFold p true ops input row (List.range 16) (initial p input outside)).trace,Good event :=
  fixed_first_block_fold_good p ops input row (List.range 16) _ (fun w hw => List.mem_range.mp hw)
    (initial_reads p input outside) (by intro t ht; rfl) (by intro event he; cases he)

theorem initial_resumed_first_block_race_free (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row : Nat) :
    raceFree (geometry p) (resumedFirstBlock p ops input row (initial p input outside)).trace=true :=
  race_free p _ (initial_fixed_first_block_good p ops input outside row)

theorem first_block_fold_trace_length (p : Shape) (repaired : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ws : List Nat) (s : State α) (bounds : ∀ w∈ws,w<16) :
    (firstBlockFold p repaired ops input row ws s).trace.length=
      s.trace.length+ws.length*(if repaired then 5122 else 5184) := by
  induction ws generalizing s with
  | nil => simp only [firstBlockFold,List.foldl_nil,List.length_nil,Nat.zero_mul,Nat.add_zero]
  | cons w ws ih =>
      have hwlen : (wavePartial p repaired ops input row w s).trace.length=
          s.trace.length+(if repaired then 5122 else 5184) := by
        cases repaired with
        | false => exact original_wave_partial_trace_length p ops input row w s
        | true => exact fixed_wave_partial_trace_length p ops input row w s (bounds w (by simp))
      rw [first_block_fold_cons,ih _ (fun v hv => bounds v (by simp [hv])),hwlen]
      simp only [List.length_cons,Nat.succ_mul]
      omega

theorem initial_original_first_block_trace_length (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row : Nat) :
    (firstBlockFold p false ops input row (List.range 16) (initial p input outside)).trace.length=82944 := by
  simpa only [initial,LarkNonlinear.initial,List.length_nil,List.length_range,Nat.zero_add,↓reduceIte] using
    first_block_fold_trace_length p false ops input row (List.range 16) (initial p input outside)
      (fun w hw => List.mem_range.mp hw)

theorem initial_fixed_first_block_trace_length (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row : Nat) :
    (firstBlockFold p true ops input row (List.range 16) (initial p input outside)).trace.length=81952 := by
  simpa only [initial,LarkNonlinear.initial,List.length_nil,List.length_range,Nat.zero_add,↓reduceIte] using
    first_block_fold_trace_length p true ops input row (List.range 16) (initial p input outside)
      (fun w hw => List.mem_range.mp hw)

theorem wave_partial_carries_trace (p : Shape) (repaired : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row w : Nat) (s : State α) (reads : Reads p input s) (event : Access) (he : event∈s.trace) :
    event∈(wavePartial p repaired ops input row w s).trace := by
  obtain ⟨events,ht,hl,hg⟩ := wave_partial_trace_tail p repaired ops input row w s reads
  rw [ht]
  simp [he]

theorem first_block_fold_carries_trace (p : Shape) (repaired : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ws : List Nat) (s : State α) (reads : Reads p input s) (event : Access) (he : event∈s.trace) :
    event∈(firstBlockFold p repaired ops input row ws s).trace := by
  induction ws generalizing s with
  | nil => simpa only [firstBlockFold,List.foldl_nil] using he
  | cons w ws ih =>
      rw [first_block_fold_cons]
      exact ih _ (wave_partial_reads p repaired ops input row w s reads)
        (wave_partial_carries_trace p repaired ops input row w s reads event he)

theorem initial_original_first_block_racy (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row : Nat) :
    raceFree (geometry p) (firstBlockFold p false ops input row (List.range 16) (initial p input outside)).trace=false := by
  have hs : List.range 16=0::((List.range 15).map (fun n => n+1)) := by decide
  rw [hs,first_block_fold_cons]
  apply conflicting_trace_members (geometry p) _ (originalWaveAccess row 0 0) (originalWaveAccess row 0 1)
  · exact first_block_fold_carries_trace p false ops input row _ _
      (wave_partial_reads p false ops input row 0 _ (initial_reads p input outside)) _
      (original_wave_access_member p ops input outside row 0 0 (by decide))
  · exact first_block_fold_carries_trace p false ops input row _ _
      (wave_partial_reads p false ops input row 0 _ (initial_reads p input outside)) _
      (original_wave_access_member p ops input outside row 0 1 (by decide))
  · exact original_wave_pair_conflict p row 0 (by decide)

theorem initial_native_first_block_waves (p : Shape) (repaired : Bool) (ops : Ops α)
    (input : Nat → Nat → α) (outside : Location → Option α) (row : Nat) (hr : row<p.rows) :
    (List.range 16).foldlM
      (fun s w => LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel (program repaired)
        (warpThreads (geometry p) row w) fuel.warp s) (initial p input outside)=
      some (firstBlockFold p repaired ops input row (List.range 16) (initial p input outside)) :=
  first_block_waves_run p repaired ops input row (List.range 16) _ hr List.nodup_range
    (fun w hw => List.mem_range.mp hw) (by intro w hw t ht; rfl) (initial_reads p input outside)

#print axioms carried_fixed_wave_good
#print axioms fixed_first_block_fold_good
#print axioms initial_fixed_first_block_good
#print axioms initial_resumed_first_block_race_free
#print axioms first_block_fold_trace_length
#print axioms initial_original_first_block_trace_length
#print axioms initial_fixed_first_block_trace_length
#print axioms wave_partial_carries_trace
#print axioms first_block_fold_carries_trace
#print axioms initial_original_first_block_racy
#print axioms initial_native_first_block_waves
end LarkNativeSglangRmsNorm
