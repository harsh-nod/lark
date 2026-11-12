import Lark.NativeSglangRmsNormCompleteBlock

/-! Frames needed for sequential whole-grid composition: other blocks retain
their control state and epochs, inputs/weights stay read-only, and earlier
blocks' output locations remain intact.
-/
namespace LarkNativeSglangRmsNorm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
attribute [local irreducible] prefixFold reductionSnapshot partialFold firstBlockFold secondFold regAddFold inverseFold secondSnapshot skipFold inactiveWaves scalePairs scaleRounds outputCopies outputFold

theorem resume_pc_other (ts : List Nat) (s : State α) (t : Nat) (ht : t∉ts) :
    (resume ts .block s).pc t=s.pc t := by
  have hc : ts.contains t=false := by simp [List.contains_iff_mem,ht]
  simp only [resume,hc,Bool.false_eq_true,↓reduceIte]

theorem resume_epoch_other (ts : List Nat) (s : State α) (t : Nat) (ht : t∉ts) :
    (resume ts .block s).epochs t=s.epochs t := by
  have hc : ts.contains t=false := by simp [List.contains_iff_mem,ht]
  simp only [resume,hc,Bool.false_eq_true,↓reduceIte]

theorem first_block_pc_other (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row t : Nat) (s : State α) (ht : t∉blockThreads (geometry p) row) :
    (firstBlockFold p true ops input row (List.range 16) s).pc t=s.pc t :=
  (first_block_fold_other p true ops input row (List.range 16) t s (by
    intro w hw hm
    exact ht (cohort_in_block p row w t (List.mem_range.mp hw) hm))).1

theorem second_block_pc_other (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row t : Nat) (s : State α) (ht : t∉blockThreads (geometry p) row) :
    (secondBlock p ops input row s).pc t=s.pc t := by
  have h0 := wave_second_other p ops input row t s (by
    intro hm; exact ht (cohort_in_block p row 0 t (by decide) hm))
  have h1 := inactive_waves_other row remainingWaves t (waveSecond p ops input row s) (by
    intro w hw hm
    exact ht (cohort_in_block p row w t ((remaining_waves_bounds w).mp hw).2 hm))
  exact h1.trans h0.1

theorem complete_block_pc_other (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row t : Nat) (s : State α) (ht : t∉blockThreads (geometry p) row) :
    (completeBlock p ops input row s).pc t=s.pc t := by
  have h0 := first_block_pc_other p ops input row t s ht
  have h1 := resume_pc_other (blockThreads (geometry p) row)
    (firstBlockFold p true ops input row (List.range 16) s) t ht
  have h2 := second_block_pc_other p ops input row t (resumedFirstBlock p ops input row s) ht
  have h3 := resume_pc_other (blockThreads (geometry p) row)
    (secondBlock p ops input row (resumedFirstBlock p ops input row s)) t ht
  have h4 := (output_fold_other ops input (blockThreads (geometry p) row) t
    (resumedSecondBlock p ops input row (resumedFirstBlock p ops input row s)) ht).1
  exact h4.trans (h3.trans (h2.trans (h1.trans h0)))

theorem complete_block_epoch_other (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row t : Nat) (s : State α) (ht : t∉blockThreads (geometry p) row) :
    (completeBlock p ops input row s).epochs t=s.epochs t := by
  have h0 := congrFun (first_block_fold_epochs p true ops input row (List.range 16) s) t
  have h1 := resume_epoch_other (blockThreads (geometry p) row)
    (firstBlockFold p true ops input row (List.range 16) s) t ht
  have h2 := congrFun (second_block_indices_epochs p ops input row (resumedFirstBlock p ops input row s)).2 t
  have h3 := resume_epoch_other (blockThreads (geometry p) row)
    (secondBlock p ops input row (resumedFirstBlock p ops input row s)) t ht
  have h4 := congrFun (output_block_epochs p ops input row
    (resumedSecondBlock p ops input row (resumedFirstBlock p ops input row s))) t
  exact h4.trans (h3.trans (h2.trans (h1.trans h0)))

theorem output_fold_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (ts : List Nat) (s : State α) (reads : Reads p input s) : Reads p input (outputFold ops input ts s) := by
  induction ts generalizing s with
  | nil => rw [outputFold]; exact reads
  | cons t ts ih =>
      rw [output_fold_cons]
      exact ih (laneOutput ops input t s)
        (output_lane_reads p ops input (t/1024) (t%1024) t (laneInverse ops input t) s reads)

theorem complete_block_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) (reads : Reads p input s) : Reads p input (completeBlock p ops input row s) :=
  output_fold_reads p ops input (blockThreads (geometry p) row) _ (resumed_twice_reads p ops input row s reads)

theorem first_wave_global_output (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row w offset : Nat) (s : State α) :
    (wavePartial p true ops input row w s).memory (globalCell 0 offset)=s.memory (globalCell 0 offset) := by
  apply wave_partial_memory
  · intro t _
    exact Or.inl (by simp [globalCell])
  · intro t _ he
    have hs := congrArg Location.space he
    cases hs

theorem first_block_global_output (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row offset : Nat) (ws : List Nat) (s : State α) :
    (firstBlockFold p true ops input row ws s).memory (globalCell 0 offset)=s.memory (globalCell 0 offset) := by
  induction ws generalizing s with
  | nil => rw [firstBlockFold]; rfl
  | cons w ws ih =>
      rw [first_block_fold_cons]
      exact (ih (wavePartial p true ops input row w s)).trans (first_wave_global_output p ops input row w offset s)

theorem resumed_twice_global_output (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row offset : Nat) (s : State α) :
    (resumedSecondBlock p ops input row (resumedFirstBlock p ops input row s)).memory (globalCell 0 offset)=
      s.memory (globalCell 0 offset) :=
  (second_block_outside_shared p ops input row (resumedFirstBlock p ops input row s)
    (globalCell 0 offset) (by simp [globalCell])).trans (first_block_global_output p ops input row offset (List.range 16) s)

theorem complete_block_previous_output (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row offset : Nat) (s : State α) (outside : writer offset∉blockThreads (geometry p) row) :
    (completeBlock p ops input row s).memory (globalCell 0 offset)=s.memory (globalCell 0 offset) :=
  (output_fold_previous_output ops input (blockThreads (geometry p) row) offset _ outside).trans
    (resumed_twice_global_output p ops input row offset s)

theorem other_row_thread (p : Shape) (row other tid : Nat) (ht : tid<1024) (hne : other≠row) :
    other*1024+tid∉blockThreads (geometry p) row := by
  intro hm
  obtain ⟨peer,hp,he⟩ := (block_member p row _).mp hm
  omega

#print axioms resume_pc_other
#print axioms resume_epoch_other
#print axioms first_block_pc_other
#print axioms second_block_pc_other
#print axioms complete_block_pc_other
#print axioms complete_block_epoch_other
#print axioms output_fold_reads
#print axioms complete_block_reads
#print axioms first_wave_global_output
#print axioms first_block_global_output
#print axioms resumed_twice_global_output
#print axioms complete_block_previous_output
#print axioms other_row_thread
end LarkNativeSglangRmsNorm
