import Lark.NativeSoftmaxBlockMemoryFrame

/-! Actual repaired block fold for a grid. Pending rows retain their complete
source entry, completed rows retain their halt PCs and normalization outputs,
and the actual accumulated trace remains classified Good. -/
namespace LarkNativeSoftmax
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def GridRowsEntry (p : Shape) (input : Nat → Nat → α) (rows : List Nat) (s : State α) : Prop :=
  ∀ row ∈ rows, BlockEntry p input row s

def fixedBlockFold (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (rows : List Nat) (s : State α) : State α :=
  rows.foldl (fun s row => wholeBlock p true ops input row s) s

theorem grid_rows_entry_tail (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (rows : List Nat) (s : State α) (hn : row ∉ rows) (entry : GridRowsEntry p input (row::rows) s) :
    GridRowsEntry p input rows (wholeBlock p true ops input row s) := by
  intro other ho
  exact whole_block_fixed_entry_other p ops input row other s (by intro he; subst other; exact hn ho)
    (entry row (by simp)) (entry other (by simp [ho]))

theorem fixed_block_fold_run (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (rows : List Nat) (s : State α) (hn : rows.Nodup) (entry : GridRowsEntry p input rows s) :
    rows.foldlM (fun s row => LarkPartitionCollective.runBlock ops (layout p) (geometry p) fuel (program true) row fuel.block s) s=
      some (fixedBlockFold p ops input rows s) := by
  induction rows generalizing s with
  | nil => rfl
  | cons row rows ih =>
    obtain ⟨hnot,htail⟩ := List.nodup_cons.mp hn
    rewrite [List.foldlM_cons,whole_block_run p true ops input row s (entry row (by simp))]
    simp only [bind,Option.some_bind]
    exact ih _ htail (grid_rows_entry_tail p ops input row rows s hnot entry)

theorem fixed_block_fold_pc_other (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (rows : List Nat) (t : Nat) (s : State α) (ht : t/1024 ∉ rows) :
    (fixedBlockFold p ops input rows s).pc t=s.pc t := by
  induction rows generalizing s with
  | nil => rfl
  | cons row rows ih =>
    have hne : t/1024 ≠ row := by intro he; exact ht (List.mem_cons.mpr (Or.inl he))
    exact (ih _ (by intro hm; exact ht (by simp [hm]))).trans (whole_block_foreign_pc p true ops input row t s hne)

theorem fixed_block_fold_member_pc (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (rows : List Nat) (s : State α) (hn : rows.Nodup) (row tid : Nat) (hr : row ∈ rows) (ht : tid<1024) :
    (fixedBlockFold p ops input rows s).pc (row*1024+tid)=normPc true 115 := by
  induction rows generalizing s with
  | nil => simp at hr
  | cons other rows ih =>
    obtain ⟨hnot,htail⟩ := List.nodup_cons.mp hn
    rcases List.mem_cons.mp hr with he | hm
    · subst row
      exact (fixed_block_fold_pc_other p ops input rows (other*1024+tid) (wholeBlock p true ops input other s)
        (by simpa only [(row_thread_coords other tid ht).1] using hnot)).trans (whole_block_pc p true ops input other tid s ht)
    · exact ih _ htail hm

theorem fixed_block_fold_epoch_other (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (rows : List Nat) (t : Nat) (s : State α) (ht : t/1024 ∉ rows) :
    (fixedBlockFold p ops input rows s).epochs t=s.epochs t := by
  induction rows generalizing s with
  | nil => rfl
  | cons row rows ih =>
    have hne : t/1024 ≠ row := by intro he; exact ht (List.mem_cons.mpr (Or.inl he))
    exact (ih _ (by intro hm; exact ht (by simp [hm]))).trans (whole_block_foreign_epoch p true ops input row t s hne)

theorem whole_block_entry_epoch (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid : Nat) (s : State α) (entry : BlockEntry p input row s) (ht : tid<1024) :
    ((wholeBlock p guarded ops input row s).epochs (row*1024+tid)).block=4 :=
  (congrArg (fun epochs => (epochs (row*1024+tid)).block) (whole_block_normalization_epochs p guarded ops input row s)).trans
    ((sum_ready p ops input row s entry).epoch tid ht)

theorem fixed_block_fold_member_epoch (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (rows : List Nat) (s : State α) (hn : rows.Nodup) (entry : GridRowsEntry p input rows s)
    (row tid : Nat) (hr : row ∈ rows) (ht : tid<1024) :
    ((fixedBlockFold p ops input rows s).epochs (row*1024+tid)).block=4 := by
  induction rows generalizing s with
  | nil => simp at hr
  | cons other rows ih =>
    obtain ⟨hnot,htail⟩ := List.nodup_cons.mp hn
    rcases List.mem_cons.mp hr with he | hm
    · subst row
      exact (congrArg Epoch.block (fixed_block_fold_epoch_other p ops input rows (other*1024+tid) (wholeBlock p true ops input other s)
        (by simpa only [(row_thread_coords other tid ht).1] using hnot))).trans
          (whole_block_entry_epoch p true ops input other tid s (entry other (by simp)) ht)
    · exact ih _ htail (grid_rows_entry_tail p ops input other rows s hnot entry) hm

theorem fixed_block_fold_output_other (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (rows : List Nat) (row col : Nat) (s : State α) (hr : row ∉ rows) (hc : col<50257) :
    (fixedBlockFold p ops input rows s).memory (globalCell 0 (address row col))=s.memory (globalCell 0 (address row col)) := by
  induction rows generalizing s with
  | nil => rfl
  | cons other rows ih =>
    have hne : row ≠ other := by intro he; subst row; simp at hr
    exact (ih _ (by intro hm; exact hr (by simp [hm]))).trans (whole_block_other_row_output p true ops input other row col s hne hc)

theorem fixed_block_fold_output_member (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (rows : List Nat) (s : State α) (hn : rows.Nodup) (row col : Nat) (hr : row ∈ rows) (hc : col<50257) :
    (fixedBlockFold p ops input rows s).memory (globalCell 0 (address row col))=some (normOutputValue ops input row col) := by
  induction rows generalizing s with
  | nil => simp at hr
  | cons other rows ih =>
    obtain ⟨hnot,htail⟩ := List.nodup_cons.mp hn
    rcases List.mem_cons.mp hr with he | hm
    · subst row
      exact (fixed_block_fold_output_other p ops input rows other col (wholeBlock p true ops input other s) hnot hc).trans
        (whole_block_outputs p true ops input other s col hc)
    · exact ih _ htail hm

theorem fixed_block_fold_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (rows : List Nat) (s : State α) (hn : rows.Nodup) (entry : GridRowsEntry p input rows s) (good : ∀ a ∈ s.trace, Good a) :
    ∀ a ∈ (fixedBlockFold p ops input rows s).trace, Good a := by
  induction rows generalizing s with
  | nil => exact good
  | cons row rows ih =>
    obtain ⟨hnot,htail⟩ := List.nodup_cons.mp hn
    exact ih _ htail (grid_rows_entry_tail p ops input row rows s hnot entry) (whole_block_fixed_good p ops input row s (entry row (by simp)))

theorem fixed_block_fold_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (rows : List Nat) (s : State α) (hn : rows.Nodup) (entry : GridRowsEntry p input rows s) (reads : Reads p input s) :
    Reads p input (fixedBlockFold p ops input rows s) := by
  induction rows generalizing s with
  | nil => exact reads
  | cons row rows ih =>
    obtain ⟨hnot,htail⟩ := List.nodup_cons.mp hn
    exact ih _ htail (grid_rows_entry_tail p ops input row rows s hnot entry) (whole_block_reads p true ops input row s (entry row (by simp)))

theorem fixed_block_fold_trace_length (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (rows : List Nat) (s : State α) : (fixedBlockFold p ops input rows s).trace.length=s.trace.length+475752*rows.length := by
  induction rows generalizing s with
  | nil => simp [fixedBlockFold]
  | cons row rows ih =>
    change (fixedBlockFold p ops input rows (wholeBlock p true ops input row s)).trace.length=_
    have hh : (wholeBlock p true ops input row s).trace.length=s.trace.length+475752 := whole_block_trace_length p true ops input row s
    rewrite [ih,hh]
    simp only [List.length_cons]
    omega

#print axioms grid_rows_entry_tail
#print axioms fixed_block_fold_run
#print axioms fixed_block_fold_pc_other
#print axioms fixed_block_fold_member_pc
#print axioms fixed_block_fold_epoch_other
#print axioms whole_block_entry_epoch
#print axioms fixed_block_fold_member_epoch
#print axioms fixed_block_fold_output_other
#print axioms fixed_block_fold_output_member
#print axioms fixed_block_fold_good
#print axioms fixed_block_fold_reads
#print axioms fixed_block_fold_trace_length
end LarkNativeSoftmax
