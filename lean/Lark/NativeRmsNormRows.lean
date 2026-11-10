import Lark.NativeRmsNormBlockMemory

/-! Source-ordered composition of complete native row blocks. -/
namespace LarkNativeRmsNorm
open LarkNonlinear
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def nativeRows (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (rows : List Nat) (s : State α) : State α := rows.foldl (fun s row => nativeBlock p ops input row s) s

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
    (nativeRows p ops input rows s).pc (row * 1024 + tid) = 70 := by
  induction rows generalizing s with
  | nil => simp at hr
  | cons r rows ih =>
      rcases List.nodup_cons.mp hn with ⟨hnot, hnodup⟩
      rcases List.mem_cons.mp hr with he | hm
      · subst row
        exact (native_rows_pc_other p ops input rows (nativeBlock p ops input r s) (r * 1024 + tid)
          (by intro u hu; exact other_row_thread p u r tid ht (by intro he; subst u; exact hnot hu))).trans
          (native_block_pc p ops input r tid s ht)
      · exact ih (nativeBlock p ops input r s) hnodup hm

theorem native_rows_memory_other (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (rows : List Nat) (s : State α) (row col : Nat) (hc : col < 16384) (hr : row ∉ rows) :
    (nativeRows p ops input rows s).memory (globalCell 0 (row * 16384 + col)) =
      s.memory (globalCell 0 (row * 16384 + col)) := by
  induction rows generalizing s with
  | nil => rfl
  | cons r rows ih =>
      have he : row ≠ r := by intro he; subst row; simp at hr
      have hn : row ∉ rows := by intro hm; exact hr (by simp [hm])
      exact (ih (nativeBlock p ops input r s) hn).trans (native_block_value_other p ops input r row col s he hc)

theorem native_rows_value (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (rows : List Nat) (s : State α) (hn : rows.Nodup) (row col : Nat) (hr : row ∈ rows) (hc : col < 16384) :
    (nativeRows p ops input rows s).memory (globalCell 0 (row * 16384 + col)) = some (result ops input row col) := by
  induction rows generalizing s with
  | nil => simp at hr
  | cons r rows ih =>
      rcases List.nodup_cons.mp hn with ⟨hnot, hnodup⟩
      rcases List.mem_cons.mp hr with he | hm
      · subst row
        exact (native_rows_memory_other p ops input rows (nativeBlock p ops input r s) r col hc hnot).trans
          (native_block_value p ops input r col s hc)
      · exact ih (nativeBlock p ops input r s) hnodup hm

theorem native_rows_exec (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (rows : List Nat) (s : State α) (hn : rows.Nodup) (hb : ∀ row ∈ rows, row < p.rows)
    (entry : ∀ row ∈ rows, BlockEntry p input row s)
    (good : ∀ a ∈ s.trace, LarkReductionFootprint.Good (traversal p) 0 a) :
    rows.foldlM (fun s row => LarkPartitionCollective.runBlock ops (layout p) (geometry p) fuel program row fuel.block s) s =
      some (nativeRows p ops input rows s) ∧
    (∀ a ∈ (nativeRows p ops input rows s).trace, LarkReductionFootprint.Good (traversal p) 0 a) := by
  induction rows generalizing s with
  | nil => exact ⟨rfl, good⟩
  | cons row rows ih =>
      rcases List.nodup_cons.mp hn with ⟨hnot, hnodup⟩
      have head := entry row (by simp)
      have htail : ∀ r ∈ rows, BlockEntry p input r (nativeBlock p ops input row s) := by
        intro r hr
        exact native_block_entry_other p ops input row r s (by intro he; subst r; exact hnot hr) head (entry r (by simp [hr]))
      have h := ih (nativeBlock p ops input row s) hnodup (by intro r hr; exact hb r (by simp [hr])) htail
        (native_block_good p ops input row s head)
      refine ⟨?_, h.2⟩
      rewrite [List.foldlM_cons, native_block_run p ops input row s (hb row (by simp)) head]
      simp only [bind, Option.some_bind]
      exact h.1

#print axioms native_rows_exec
#print axioms native_rows_pc
#print axioms native_rows_value
end LarkNativeRmsNorm
