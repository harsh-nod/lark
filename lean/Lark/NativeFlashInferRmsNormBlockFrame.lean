import Lark.NativeFlashInferRmsNormBlock

/-! Complete block control/epoch frames for sequential grid composition. -/
namespace LarkNativeFlashInferRmsNorm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem cohort_subset_block (p : Shape) (row warp t : Nat) (hw : warp < 16)
    (ht : t ∈ cohortThreads row warp 64) : t ∈ blockThreads (geometry p) row := by
  obtain ⟨lane,hl,rfl⟩ := (cohort_mem row warp 64 t).mp ht
  exact (block_mem p row _).mpr ⟨warp * 64 + lane,by omega,by simp only [cohortBase,Nat.add_assoc]⟩

theorem resume_pc_other (ts : List Nat) (s : State α) (t : Nat) (ht : t ∉ ts) :
    (resume ts .block s).pc t = s.pc t := by
  have hc : ts.contains t = false := by simp [List.contains_iff_mem,ht]
  simp only [resume,hc,Bool.false_eq_true,↓reduceIte]

theorem resume_epoch_other (ts : List Nat) (s : State α) (t : Nat) (ht : t ∉ ts) :
    (resume ts .block s).epochs t = s.epochs t := by
  have hc : ts.contains t = false := by simp [List.contains_iff_mem,ht]
  simp only [resume,hc,Bool.false_eq_true,↓reduceIte]

theorem first_block_pc_other (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row t : Nat) (s : State α) (ht : t ∉ blockThreads (geometry p) row) :
    (firstBlock p ops input row s).pc t = s.pc t :=
  (wave_fold_other p ops input row (List.range 16) t s (by
    intro w hw hm
    exact ht (cohort_subset_block p row w t (List.mem_range.mp hw) hm))).1

theorem scale_block_pc_other (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row t : Nat) (s : State α) (ht : t ∉ blockThreads (geometry p) row) :
    (scaleBlock p ops input row s).pc t = s.pc t := by
  have h0 := scale_wave_other p ops input row t s (by
    intro hm; exact ht (cohort_subset_block p row 0 t (by decide) hm))
  have h1 := skip_waves_other row (List.range' 1 15) (scaleWave p ops input row s) t (by
    intro w hw hm
    have hb := List.mem_range'.mp hw
    exact ht (cohort_subset_block p row w t (by omega) hm))
  exact h1.trans h0.1

theorem native_block_pc_other (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row t : Nat) (s : State α) (ht : t ∉ blockThreads (geometry p) row) :
    (nativeBlock p ops input row s).pc t = s.pc t := by
  have h0 := first_block_pc_other p ops input row t s ht
  have h1 := resume_pc_other (blockThreads (geometry p) row) (firstBlock p ops input row s) t ht
  have h2 := scale_block_pc_other p ops input row t (midState p ops input row s) ht
  have h3 := resume_pc_other (blockThreads (geometry p) row)
    (scaleBlock p ops input row (midState p ops input row s)) t ht
  have h4 := (output_fold_other ops input row (blockThreads (geometry p) row) t
    (outState p ops input row (midState p ops input row s)) ht).1
  exact h4.trans (h3.trans (h2.trans (h1.trans h0)))

theorem native_block_epoch_other (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row t : Nat) (s : State α) (ht : t ∉ blockThreads (geometry p) row) :
    (nativeBlock p ops input row s).epochs t = s.epochs t := by
  have h0 := congrFun (first_block_epochs p ops input row s) t
  have h1 := resume_epoch_other (blockThreads (geometry p) row) (firstBlock p ops input row s) t ht
  have h2 := congrFun (scale_block_preserves p ops input row (midState p ops input row s)).2 t
  have h3 := resume_epoch_other (blockThreads (geometry p) row)
    (scaleBlock p ops input row (midState p ops input row s)) t ht
  have h4 := congrFun (output_block_epochs p ops input row (outState p ops input row (midState p ops input row s))) t
  exact h4.trans (h3.trans (h2.trans (h1.trans h0)))

theorem other_row_thread (p : Shape) (row other tid : Nat) (ht : tid < 1024) (hne : other ≠ row) :
    other * 1024 + tid ∉ blockThreads (geometry p) row := by
  intro hm
  obtain ⟨peer,hp,he⟩ := (block_mem p row _).mp hm
  omega

#print axioms cohort_subset_block
#print axioms resume_pc_other
#print axioms resume_epoch_other
#print axioms first_block_pc_other
#print axioms scale_block_pc_other
#print axioms native_block_pc_other
#print axioms native_block_epoch_other
#print axioms other_row_thread
end LarkNativeFlashInferRmsNorm
