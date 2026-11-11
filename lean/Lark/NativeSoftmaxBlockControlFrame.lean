import Lark.NativeSoftmaxWholeBlock

/-! Whole-block control and epoch frames for grid composition. A block changes
only its own threads' PCs and synchronization epochs, including all four actual
barrier resumes. No entry or race-freedom assumption is needed for these frames. -/
namespace LarkNativeSoftmax
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem foreign_cohort_absent (row warp t : Nat) (hw : warp<16) (hne : t/1024 ≠ row) :
    t ∉ cohortThreads row warp 64 := by
  intro ht
  exact hne (exp_cohort_row row warp hw t ht)

theorem foreign_block_contains_false (p : Shape) (row t : Nat) (hne : t/1024 ≠ row) :
    (blockThreads (geometry p) row).contains t=false := by
  cases hc : (blockThreads (geometry p) row).contains t with
  | false => rfl
  | true =>
    obtain ⟨tid,ht,he⟩ := (block_mem p row t).mp (List.contains_iff_mem.mp hc)
    subst t
    exact False.elim (hne (row_thread_coords row tid ht).1)

theorem resume_foreign_pc (p : Shape) (row t : Nat) (cut : Cut) (s : State α) (hne : t/1024 ≠ row) :
    (resume (blockThreads (geometry p) row) cut s).pc t=s.pc t := by
  simp only [resume,foreign_block_contains_false p row t hne,Bool.false_eq_true,↓reduceIte]

theorem resume_foreign_epoch (p : Shape) (row t : Nat) (cut : Cut) (s : State α) (hne : t/1024 ≠ row) :
    (resume (blockThreads (geometry p) row) cut s).epochs t=s.epochs t := by
  simp only [resume,foreign_block_contains_false p row t hne,Bool.false_eq_true,↓reduceIte]

theorem first_block_foreign_pc (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row t : Nat) (s : State α) (hne : t/1024 ≠ row) : (firstBlock p ops input row s).pc t=s.pc t :=
  (wave_fold_other p ops input row (List.range 16) t s (by
    intro w hw; exact foreign_cohort_absent row w t (List.mem_range.mp hw) hne)).1

theorem mid_foreign_pc (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row t : Nat) (s : State α) (hne : t/1024 ≠ row) : (midState p ops input row s).pc t=s.pc t :=
  (resume_foreign_pc p row t .block _ hne).trans (first_block_foreign_pc p ops input row t s hne)

theorem after_maximum_foreign_pc (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row t : Nat) (s : State α) (hne : t/1024 ≠ row) : (afterMaximum p ops input row s).pc t=s.pc t :=
  (resume_foreign_pc p row t .block _ hne).trans
    (serial_waves_other ops (blockPartial ops input row) row (List.range 16) t s (by
      intro w hw; exact foreign_cohort_absent row w t (List.mem_range.mp hw) hne))

theorem maximum_foreign_pc (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row t : Nat) (s : State α) (hne : t/1024 ≠ row) : (maximumState p ops input row s).pc t=s.pc t :=
  (after_maximum_foreign_pc p ops input row t _ hne).trans (mid_foreign_pc p ops input row t s hne)

theorem after_exp_foreign_pc (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row t : Nat) (s : State α) (hne : t/1024 ≠ row) : (afterExp p ops input row s).pc t=s.pc t :=
  (resume_foreign_pc p row t .block _ hne).trans
    (exp_wave_fold_other p ops input row (List.range 16) t s (fun _ hw => List.mem_range.mp hw) (by
      intro w hw; exact foreign_cohort_absent row w t (List.mem_range.mp hw) hne)).1

theorem after_sum_foreign_pc (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row t : Nat) (s : State α) (hne : t/1024 ≠ row) : (afterSum p ops input row s).pc t=s.pc t :=
  (resume_foreign_pc p row t .block _ hne).trans
    (sum_serial_waves_other ops (expBlockPartial ops input row) row (List.range 16) t s (by
      intro w hw; exact foreign_cohort_absent row w t (List.mem_range.mp hw) hne))

theorem sum_state_foreign_pc (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row t : Nat) (s : State α) (hne : t/1024 ≠ row) : (sumState p ops input row s).pc t=s.pc t :=
  (after_sum_foreign_pc p ops input row t _ hne).trans
    ((after_exp_foreign_pc p ops input row t _ hne).trans (maximum_foreign_pc p ops input row t s hne))

theorem norm_block_foreign_pc (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row t : Nat) (s : State α) (hne : t/1024 ≠ row) : (normBlock guarded ops input row s).pc t=s.pc t :=
  (norm_wave_fold_other guarded ops input row (List.range 16) t s (fun _ hw => List.mem_range.mp hw) (by
    intro w hw; exact foreign_cohort_absent row w t (List.mem_range.mp hw) hne)).1

theorem whole_block_foreign_pc (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row t : Nat) (s : State α) (hne : t/1024 ≠ row) : (wholeBlock p guarded ops input row s).pc t=s.pc t :=
  (norm_block_foreign_pc guarded ops input row t _ hne).trans (sum_state_foreign_pc p ops input row t s hne)

theorem mid_foreign_epoch (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row t : Nat) (s : State α) (hne : t/1024 ≠ row) : (midState p ops input row s).epochs t=s.epochs t :=
  (resume_foreign_epoch p row t .block _ hne).trans (congrFun (first_block_epochs p ops input row s) t)

theorem after_maximum_foreign_epoch (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row t : Nat) (s : State α) (hne : t/1024 ≠ row) : (afterMaximum p ops input row s).epochs t=s.epochs t :=
  (resume_foreign_epoch p row t .block _ hne).trans (congrFun (serial_block_epochs ops input row s) t)

theorem maximum_foreign_epoch (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row t : Nat) (s : State α) (hne : t/1024 ≠ row) : (maximumState p ops input row s).epochs t=s.epochs t :=
  (after_maximum_foreign_epoch p ops input row t _ hne).trans (mid_foreign_epoch p ops input row t s hne)

theorem after_exp_foreign_epoch (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row t : Nat) (s : State α) (hne : t/1024 ≠ row) : (afterExp p ops input row s).epochs t=s.epochs t :=
  (resume_foreign_epoch p row t .block _ hne).trans (congrFun (exp_block_epochs p ops input row s) t)

theorem after_sum_foreign_epoch (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row t : Nat) (s : State α) (hne : t/1024 ≠ row) : (afterSum p ops input row s).epochs t=s.epochs t :=
  (resume_foreign_epoch p row t .block _ hne).trans (congrFun (sum_serial_block_epochs ops input row s) t)

theorem sum_state_foreign_epoch (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row t : Nat) (s : State α) (hne : t/1024 ≠ row) : (sumState p ops input row s).epochs t=s.epochs t :=
  (after_sum_foreign_epoch p ops input row t _ hne).trans
    ((after_exp_foreign_epoch p ops input row t _ hne).trans (maximum_foreign_epoch p ops input row t s hne))

theorem whole_block_foreign_epoch (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row t : Nat) (s : State α) (hne : t/1024 ≠ row) : (wholeBlock p guarded ops input row s).epochs t=s.epochs t :=
  (congrFun (norm_block_epochs guarded ops input row _) t).trans (sum_state_foreign_epoch p ops input row t s hne)

#print axioms foreign_cohort_absent
#print axioms foreign_block_contains_false
#print axioms resume_foreign_pc
#print axioms resume_foreign_epoch
#print axioms first_block_foreign_pc
#print axioms mid_foreign_pc
#print axioms after_maximum_foreign_pc
#print axioms maximum_foreign_pc
#print axioms after_exp_foreign_pc
#print axioms after_sum_foreign_pc
#print axioms sum_state_foreign_pc
#print axioms norm_block_foreign_pc
#print axioms whole_block_foreign_pc
#print axioms mid_foreign_epoch
#print axioms after_maximum_foreign_epoch
#print axioms maximum_foreign_epoch
#print axioms after_exp_foreign_epoch
#print axioms after_sum_foreign_epoch
#print axioms sum_state_foreign_epoch
#print axioms whole_block_foreign_epoch
end LarkNativeSoftmax
