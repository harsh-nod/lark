import Lark.NativeFusedRmsNormBlockMemory

/-! Source-ordered complete native row blocks with both in-place result slices.
Later rows preserve completed results and the original operands of pending rows.
-/
namespace LarkNativeFusedRmsNorm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def nativeRows (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (rows : List Nat) (s : State α) : State α := rows.foldl (fun s row => nativeBlock p ops input row s) s

def RowValues (ops : Ops α) (input : Nat → Nat → α) (row : Nat) (s : State α) : Prop :=
  ∀ col, col < 16384 →
    s.memory (globalCell 0 (address row col)) = some (outputResult ops input row col) ∧
    s.memory (globalCell 1 (address row col)) = some (residualResult ops input row col)

theorem native_block_row_values (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) (entry : BlockEntry p input row s) : RowValues ops input row (nativeBlock p ops input row s) :=
  fun col hc => ⟨native_block_value p ops input row col s hc,native_block_residual p ops input row col s entry hc⟩

theorem native_rows_pc_other (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (rows : List Nat) (s : State α) (t : Nat) (ht : ∀ row ∈ rows, t ∉ blockThreads (geometry p) row) :
    (nativeRows p ops input rows s).pc t = s.pc t := by
  induction rows generalizing s with
  | nil => rfl
  | cons row rows ih =>
      exact (ih (nativeBlock p ops input row s) (by intro r hr; exact ht r (by simp [hr]))).trans
        (native_block_pc_other p ops input row t s (ht row (by simp)))

theorem native_rows_pc (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (rows : List Nat) (s : State α) (hn : rows.Nodup) (row tid : Nat) (hr : row ∈ rows) (ht : tid < 1024) :
    (nativeRows p ops input rows s).pc (row * 1024 + tid) = 71 := by
  induction rows generalizing s with
  | nil => simp at hr
  | cons r rows ih =>
      rcases List.nodup_cons.mp hn with ⟨hnot,hnodup⟩
      rcases List.mem_cons.mp hr with he | hm
      · subst row
        exact (native_rows_pc_other p ops input rows (nativeBlock p ops input r s) (r * 1024 + tid)
          (by intro u hu; exact other_row_thread p u r tid ht (by intro he; subst u; exact hnot hu))).trans
          (native_block_pc p ops input r tid s ht)
      · exact ih _ hnodup hm

theorem native_rows_memory_other (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (rows : List Nat) (s : State α) (row col buffer : Nat) (hc : col < 16384) (hr : row ∉ rows) :
    (nativeRows p ops input rows s).memory (globalCell buffer (address row col)) = s.memory (globalCell buffer (address row col)) := by
  induction rows generalizing s with
  | nil => rfl
  | cons r rows ih =>
      have he : row ≠ r := by intro he; subst row; simp at hr
      have hn : row ∉ rows := by intro hm; exact hr (by simp [hm])
      exact (ih (nativeBlock p ops input r s) hn).trans (native_block_value_other p ops input r row col buffer s he hc)

theorem native_rows_entry_tail (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (rows : List Nat) (s : State α) (hn : row ∉ rows)
    (entry : ∀ r ∈ row :: rows, BlockEntry p input r s) :
    ∀ r ∈ rows, BlockEntry p input r (nativeBlock p ops input row s) := by
  intro r hr
  exact native_block_entry_other p ops input row r s (by intro he; subst r; exact hn hr)
    (entry row (by simp)) (entry r (by simp [hr]))

theorem native_rows_values (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (rows : List Nat) (s : State α) (hn : rows.Nodup) (entry : ∀ r ∈ rows, BlockEntry p input r s)
    (row : Nat) (hr : row ∈ rows) : RowValues ops input row (nativeRows p ops input rows s) := by
  induction rows generalizing s with
  | nil => simp at hr
  | cons r rows ih =>
      rcases List.nodup_cons.mp hn with ⟨hnot,hnodup⟩
      rcases List.mem_cons.mp hr with he | hm
      · subst row
        have head := native_block_row_values p ops input r s (entry r (by simp))
        intro col hc
        exact ⟨(native_rows_memory_other p ops input rows (nativeBlock p ops input r s) r col 0 hc hnot).trans (head col hc).1,
          (native_rows_memory_other p ops input rows (nativeBlock p ops input r s) r col 1 hc hnot).trans (head col hc).2⟩
      · exact ih _ hnodup (native_rows_entry_tail p ops input r rows s hnot entry) hm

theorem native_rows_exec (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (rows : List Nat) (s : State α) (hn : rows.Nodup) (entry : ∀ row ∈ rows, BlockEntry p input row s)
    (good : ∀ a ∈ s.trace, Good a) :
    rows.foldlM (fun s row => LarkPartitionCollective.runBlock ops (layout p) (geometry p) fuel program row fuel.block s) s =
      some (nativeRows p ops input rows s) ∧ (∀ a ∈ (nativeRows p ops input rows s).trace, Good a) := by
  induction rows generalizing s with
  | nil => exact ⟨rfl,good⟩
  | cons row rows ih =>
      rcases List.nodup_cons.mp hn with ⟨hnot,hnodup⟩
      have head := entry row (by simp)
      have h := ih (nativeBlock p ops input row s) hnodup (native_rows_entry_tail p ops input row rows s hnot entry)
        (native_block_good p ops input row s head)
      refine ⟨?_,h.2⟩
      rewrite [List.foldlM_cons,native_block_run p ops input row s head]
      simp only [bind,Option.some_bind]
      exact h.1

#print axioms native_block_row_values
#print axioms native_rows_pc_other
#print axioms native_rows_pc
#print axioms native_rows_memory_other
#print axioms native_rows_entry_tail
#print axioms native_rows_values
#print axioms native_rows_exec
end LarkNativeFusedRmsNorm
