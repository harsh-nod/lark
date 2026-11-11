import Lark.NativeSoftmaxBlockControlFrame

/-! Whole-block input and other-row output frames. A repaired completed block
preserves the data and controls required to execute any pending distinct row,
and its actual classified trace supplies that row's Good entry condition. -/
namespace LarkNativeSoftmax
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem norm_scalar_fold_input_memory (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ts : List Nat) (offset : Nat) (s : State α) (hb : ∀ t ∈ ts, t/1024=row) :
    (normScalarFold guarded ops input row ts s).memory (globalCell 1 offset)=s.memory (globalCell 1 offset) := by
  apply norm_scalar_fold_memory_frame guarded ops input row ts s _ hb
  · intro t ht
    exact Or.inl (by change Space.global ≠ Space.local; decide)
  · intro t ht it hi c hc hcol he
    have hb := congrArg Location.buffer he
    simp [globalCell] at hb

theorem norm_wave_input_memory (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row warp offset : Nat) (s : State α) (hw : warp<16) :
    (normWave guarded ops input row warp s).memory (globalCell 1 offset)=s.memory (globalCell 1 offset) :=
  norm_scalar_fold_input_memory guarded ops input row _ offset s (exp_cohort_row row warp hw)

theorem norm_wave_fold_input_memory (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ws : List Nat) (offset : Nat) (s : State α) (hb : ∀ w ∈ ws, w<16) :
    (normWaveFold guarded ops input row ws s).memory (globalCell 1 offset)=s.memory (globalCell 1 offset) := by
  induction ws generalizing s with
  | nil => rfl
  | cons w ws ih =>
    exact (ih _ (by intro u hu; exact hb u (by simp [hu]))).trans (norm_wave_input_memory guarded ops input row w offset s (hb w (by simp)))

theorem norm_block_reads (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) (reads : Reads p input s) : Reads p input (normBlock guarded ops input row s) := by
  intro offset ho
  exact (norm_wave_fold_input_memory guarded ops input row (List.range 16) offset s (fun _ hw => List.mem_range.mp hw)).trans (reads offset ho)

theorem whole_block_reads (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) (entry : BlockEntry p input row s) : Reads p input (wholeBlock p guarded ops input row s) :=
  norm_block_reads p guarded ops input row _ (sum_ready p ops input row s entry).reads

theorem exp_block_output_foreign (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row offset : Nat) (s : State α) (ho : (writer offset)/1024 ≠ row) :
    (expBlock p ops input row s).memory (globalCell 0 offset)=s.memory (globalCell 0 offset) := by
  apply exp_wave_fold_output_other p ops input row (List.range 16) offset s (fun _ hw => List.mem_range.mp hw)
  intro w hw hm
  exact ho (exp_cohort_row row w (List.mem_range.mp hw) (writer offset) hm)

theorem norm_block_output_foreign (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row offset : Nat) (s : State α) (ho : (writer offset)/1024 ≠ row) :
    (normBlock guarded ops input row s).memory (globalCell 0 offset)=s.memory (globalCell 0 offset) := by
  apply norm_wave_fold_output_other guarded ops input row (List.range 16) offset s (fun _ hw => List.mem_range.mp hw)
  intro w hw hm
  exact ho (exp_cohort_row row w (List.mem_range.mp hw) (writer offset) hm)

theorem sum_state_output_foreign (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row offset : Nat) (s : State α) (ho : (writer offset)/1024 ≠ row) :
    (sumState p ops input row s).memory (globalCell 0 offset)=s.memory (globalCell 0 offset) :=
  (after_sum_output_frame p ops input row offset _).trans
    ((exp_block_output_foreign p ops input row offset _ ho).trans
      (maximum_memory_frame p ops input row s _ (Or.inl rfl)))

theorem whole_block_output_foreign (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row offset : Nat) (s : State α) (ho : (writer offset)/1024 ≠ row) :
    (wholeBlock p guarded ops input row s).memory (globalCell 0 offset)=s.memory (globalCell 0 offset) :=
  (norm_block_output_foreign guarded ops input row offset _ ho).trans (sum_state_output_foreign p ops input row offset s ho)

theorem address_writer_row (row col : Nat) (hc : col<50257) : (writer (address row col))/1024=row := by
  obtain ⟨tid,it,c,ht,hi,hcb,_,he⟩ := column_cover col hc
  rewrite [←he,address_writer row tid it c ht (by simpa only [he] using hc)]
  exact (row_thread_coords row tid ht).1

theorem whole_block_other_row_output (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row other col : Nat) (s : State α) (hne : other ≠ row) (hc : col<50257) :
    (wholeBlock p guarded ops input row s).memory (globalCell 0 (address other col))=s.memory (globalCell 0 (address other col)) :=
  whole_block_output_foreign p guarded ops input row _ s (by rewrite [address_writer_row other col hc]; exact hne)

theorem whole_block_fixed_entry_other (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row other : Nat) (s : State α) (hne : other ≠ row)
    (entry : BlockEntry p input row s) (next : BlockEntry p input other s) :
    BlockEntry p input other (wholeBlock p true ops input row s) := by
  exact {
    valid := next.valid
    pc := by
      intro tid ht
      exact (whole_block_foreign_pc p true ops input row (other*1024+tid) s (by
        rewrite [(row_thread_coords other tid ht).1]; exact hne)).trans (next.pc tid ht)
    reads := whole_block_reads p true ops input row s entry
    epoch := by
      intro tid ht
      exact (congrArg Epoch.block (whole_block_foreign_epoch p true ops input row (other*1024+tid) s (by
        rewrite [(row_thread_coords other tid ht).1]; exact hne))).trans (next.epoch tid ht)
    good := whole_block_fixed_good p ops input row s entry }

#print axioms norm_scalar_fold_input_memory
#print axioms norm_wave_input_memory
#print axioms norm_wave_fold_input_memory
#print axioms norm_block_reads
#print axioms whole_block_reads
#print axioms exp_block_output_foreign
#print axioms norm_block_output_foreign
#print axioms sum_state_output_foreign
#print axioms whole_block_output_foreign
#print axioms address_writer_row
#print axioms whole_block_other_row_output
#print axioms whole_block_fixed_entry_other
end LarkNativeSoftmax
