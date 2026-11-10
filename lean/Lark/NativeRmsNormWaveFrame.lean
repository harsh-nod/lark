import Lark.NativeRmsNormFirstWave

/-! Native-wave frame properties needed to compose all sixteen physical waves.
Only the current wave's shared partial cell is written in this phase.
-/
namespace LarkNativeRmsNorm
open LarkNonlinear
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem first_last_memory_other (ops : Ops α) (t lane warp valid : Nat) (a b : α) (s : State α)
    (l : Location) (hl : l ≠ partialCell t warp) :
    (firstLastAfter ops t lane warp valid a b s).memory l = s.memory l := by
  unfold firstLastAfter partialAfter
  split <;> simp only [partialWritten, advance, record, if_neg hl]
  all_goals exact congrFun (guarded_preserves ops t 33 lane 32 valid a b s).2.1 l

theorem last_cohort_memory (p : Shape) (ops : Ops α) (row warp valid : Nat) (a b : Nat → α)
    (s : State α) (hw : warp < 16) :
    (firstLastFold ops warp valid (LarkPartitionCollective.nativeLane (geometry p)) a b
      (cohortThreads row warp 64) s).memory =
      (firstLastAfter ops (cohortBase row warp) 0 warp valid (a (cohortBase row warp)) (b (cohortBase row warp)) s).memory := by
  let tail := (List.range 63).map (fun lane => cohortBase row warp + (lane + 1))
  have hn : ∀ t ∈ tail, LarkPartitionCollective.nativeLane (geometry p) t ≠ 0 := by
    intro t ht
    obtain ⟨lane, hl, rfl⟩ := List.mem_map.mp ht
    have hl := List.mem_range.mp hl
    rewrite [(cohort_coords p row warp (lane + 1) hw (by omega)).2]
    omega
  have hc : LarkPartitionCollective.nativeLane (geometry p) (cohortBase row warp) = 0 := by
    simpa only [Nat.add_zero] using (cohort_coords p row warp 0 hw (by decide)).2
  unfold firstLastFold
  rewrite [cohort_cons, List.foldl_cons, hc]
  exact first_last_fold_memory_nonzero ops warp valid (LarkPartitionCollective.nativeLane (geometry p)) a b tail _ hn

theorem last_wave_memory_other (p : Shape) (ops : Ops α) (row warp valid : Nat) (values : Nat → α)
    (s : State α) (hw : warp < 16) (l : Location) (hl : l ≠ partialCell (cohortBase row warp) warp) :
    (lastWave p ops row warp valid values s).memory l = s.memory l := by
  have hm := last_cohort_memory p ops row warp valid
    (fun t => values (LarkPartitionCollective.nativeLane (geometry p) t))
    (fun t => values (downPeer 64 32 (LarkPartitionCollective.nativeLane (geometry p) t)))
    (LarkCollective.shuffleUpdates 1 (cohortSnapshot p row warp 64 32 values) s) hw
  exact (congrFun hm l).trans (first_last_memory_other ops (cohortBase row warp) 0 warp valid _ _ _ l hl)

theorem last_wave_other (p : Shape) (ops : Ops α) (row warp valid t : Nat) (values : Nat → α)
    (s : State α) (ht : t ∉ cohortThreads row warp 64) :
    (lastWave p ops row warp valid values s).pc t = s.pc t ∧
    (lastWave p ops row warp valid values s).regs t = s.regs t := by
  have h := first_last_fold_other ops warp valid (LarkPartitionCollective.nativeLane (geometry p))
    (fun t => values (LarkPartitionCollective.nativeLane (geometry p) t))
    (fun t => values (downPeer 64 32 (LarkPartitionCollective.nativeLane (geometry p) t)))
    (cohortThreads row warp 64) t (LarkCollective.shuffleUpdates 1 (cohortSnapshot p row warp 64 32 values) s) ht
  have hs := cohort_shuffled_other p row warp 64 32 t values s ht
  exact ⟨h.1.trans hs.1, h.2.trans hs.2⟩

theorem wave_tail_memory_other (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp n remaining : Nat) (s : State α) (hw : warp < 16) (l : Location)
    (hl : l ≠ partialCell (cohortBase row warp) warp) :
    (waveTail p ops input row warp n remaining s).memory l = s.memory l := by
  induction remaining generalizing n s with
  | zero => exact last_wave_memory_other p ops row warp _ _ s hw l hl
  | succ remaining ih =>
      have h := ih (n + 1) (cohortStep p ops row warp 64 (18 + 3 * n) (2 ^ n)
        (1024 - warp * 64) (waveValues ops input row warp n) s)
      have h1 := (cohort_step_preserves p ops row warp 64 (18 + 3 * n) (2 ^ n)
        (1024 - warp * 64) (waveValues ops input row warp n) s).2.1
      exact h.trans (congrFun h1 l)

theorem wave_tail_other (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp n remaining t : Nat) (s : State α) (ht : t ∉ cohortThreads row warp 64) :
    (waveTail p ops input row warp n remaining s).pc t = s.pc t ∧
    (waveTail p ops input row warp n remaining s).regs t = s.regs t := by
  induction remaining generalizing n s with
  | zero => exact last_wave_other p ops row warp _ t _ s ht
  | succ remaining ih =>
      have h := ih (n + 1) (cohortStep p ops row warp 64 (18 + 3 * n) (2 ^ n)
        (1024 - warp * 64) (waveValues ops input row warp n) s)
      have h1 := cohort_step_other p ops row warp 64 (18 + 3 * n) (2 ^ n)
        (1024 - warp * 64) t (waveValues ops input row warp n) s ht
      exact ⟨h.1.trans h1.1, h.2.trans h1.2⟩

theorem first_wave_other (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp t : Nat) (s : State α) (ht : t ∉ cohortThreads row warp 64) :
    (firstWave p ops input row warp s).pc t = s.pc t ∧
    (firstWave p ops input row warp s).regs t = s.regs t := by
  have h := wave_tail_other p ops input row warp 0 5 t (prefixFold ops input (cohortThreads row warp 64) s) ht
  have h1 := prefix_fold_other ops input (cohortThreads row warp 64) t s ht
  exact ⟨h.1.trans h1.1, h.2.trans h1.2.2⟩

theorem first_wave_memory_other (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp : Nat) (s : State α) (hw : warp < 16) (l : Location)
    (hl : l ≠ partialCell (cohortBase row warp) warp) :
    (firstWave p ops input row warp s).memory l = s.memory l := by
  have h := wave_tail_memory_other p ops input row warp 0 5
    (prefixFold ops input (cohortThreads row warp 64) s) hw l hl
  exact h.trans (congrFun (prefix_fold_preserves ops input (cohortThreads row warp 64) s).1 l)

theorem first_wave_indices_other (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp t : Nat) (s : State α) (ht : t ∉ cohortThreads row warp 64) :
    (firstWave p ops input row warp s).indices t = s.indices t := by
  have h := (wave_tail_preserves p ops input row warp 0 5 (prefixFold ops input (cohortThreads row warp 64) s)).1
  exact (congrFun h t).trans (prefix_fold_other ops input (cohortThreads row warp 64) t s ht).2.1

theorem first_wave_epochs (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp : Nat) (s : State α) : (firstWave p ops input row warp s).epochs = s.epochs :=
  (wave_tail_preserves p ops input row warp 0 5 (prefixFold ops input (cohortThreads row warp 64) s)).2.trans
    (prefix_fold_preserves ops input (cohortThreads row warp 64) s).2

theorem first_wave_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp : Nat) (s : State α) (reads : Reads p input s) : Reads p input (firstWave p ops input row warp s) :=
  wave_tail_reads p ops input row warp 0 5 _ (reads_of_memory p input s _ reads
    (prefix_fold_preserves ops input (cohortThreads row warp 64) s).1)

theorem first_wave_partial (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp : Nat) (s : State α) (hw : warp < 16) :
    (firstWave p ops input row warp s).memory (partialCell (cohortBase row warp) warp) =
      some (warpSum ops input row warp) :=
  wave_tail_partial p ops input row warp 0 5 _ (by decide) hw

theorem first_wave_pc (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp : Nat) (s : State α) (hw : warp < 16) :
    ∀ lane, lane < 64 → (firstWave p ops input row warp s).pc (cohortBase row warp + lane) = 38 :=
  wave_tail_pc p ops input row warp 0 5 _ (by decide) hw (first_prefix_ready p ops input row warp s hw)

theorem first_wave_indices (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp t : Nat) (s : State α) (ht : t ∈ cohortThreads row warp 64) :
    NativeIndices t (firstWave p ops input row warp s) := by
  have hi := (prefix_fold_member ops input (cohortThreads row warp 64) s (cohort_nodup row warp 64) t ht).2.2
  have hp := (wave_tail_preserves p ops input row warp 0 5 (prefixFold ops input (cohortThreads row warp 64) s)).1
  change NativeIndices t (waveTail p ops input row warp 0 5 (prefixFold ops input (cohortThreads row warp 64) s))
  simpa only [NativeIndices, hp] using hi

theorem first_wave_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp : Nat) (s : State α) (hw : warp < 16)
    (he : ∀ lane, lane < 64 → (s.epochs (cohortBase row warp + lane)).block = 0)
    (good : ∀ access ∈ s.trace, LarkReductionFootprint.Good (traversal p) 0 access) :
    ∀ access ∈ (firstWave p ops input row warp s).trace, LarkReductionFootprint.Good (traversal p) 0 access := by
  have hp := (prefix_fold_preserves ops input (cohortThreads row warp 64) s).2
  apply wave_tail_good p ops input row warp 0 5 _ hw
  · intro lane hl
    exact (congrArg (fun epochs => (epochs (cohortBase row warp + lane)).block) hp).trans (he lane hl)
  · exact prefix_fold_good p ops input _ s good

#print axioms first_wave_other
#print axioms first_wave_memory_other
end LarkNativeRmsNorm
