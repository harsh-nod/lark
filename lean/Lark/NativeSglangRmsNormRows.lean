import Lark.NativeSglangRmsNormCompleteBlockFrame

/-! Source-ordered native row composition. A completed block preserves the
original operands, control and epochs of every pending row, and all outputs
already written by earlier rows. Execution and trace safety remain separate.
-/
namespace LarkNativeSglangRmsNorm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
attribute [local irreducible] prefixFold reductionSnapshot partialFold firstBlockFold secondFold regAddFold inverseFold secondSnapshot skipFold inactiveWaves scalePairs scaleRounds outputCopies outputFold

def sourceResult (ops : Ops α) (input : Nat → Nat → α) (row col : Nat) : α :=
  ops.toHalf (ops.mul (ops.mul (ops.fromHalf (input 1 (address row col)))
    (blockInverseValue ops input row (col/8%1024/32))) (ops.fromHalf (input 2 col)))

theorem source_result_column (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component : Nat) (ht : tid<1024) (hc : component<8) :
    sourceResult ops input row (column tid iteration component)=
      outputScaled ops input row tid iteration component (blockInverseValue ops input row (tid/32)) := by
  have htid : column tid iteration component/8%1024=tid := by unfold column; omega
  simp only [sourceResult,outputScaled,scaleProduct,pairLoaded,scaleWeight,htid]

theorem column_coordinates (col : Nat) :
    column (col/8%1024) (col/8192) (col%8)=col := by unfold column; omega

def RowValues (ops : Ops α) (input : Nat → Nat → α) (row : Nat) (s : State α) : Prop :=
  ∀ col,col<16384 → s.memory (globalCell 0 (address row col))=some (sourceResult ops input row col)

structure BlockEntry (p : Shape) (input : Nat → Nat → α) (row : Nat) (s : State α) : Prop where
  valid : row<p.rows
  reads : Reads p input s
  pc : ∀ t∈blockThreads (geometry p) row,s.pc t=0
  epoch : ∀ t∈blockThreads (geometry p) row,(s.epochs t).block=0

theorem initial_block_entry (p : Shape) (input : Nat → Nat → α) (outside : Location → Option α)
    (row : Nat) (hr : row<p.rows) : BlockEntry p input row (initial p input outside) :=
  ⟨hr,initial_reads p input outside,by intro t ht; rfl,by intro t ht; rfl⟩

theorem block_entry_other (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row other : Nat) (s : State α) (hne : other≠row) (entry : BlockEntry p input other s) :
    BlockEntry p input other (completeBlock p ops input row s) := by
  have outside : ∀ t∈blockThreads (geometry p) other,t∉blockThreads (geometry p) row := by
    intro t ht
    obtain ⟨tid,htid,rfl⟩ := (block_member p other t).mp ht
    exact other_row_thread p row other tid htid hne
  exact {
    valid := entry.valid,reads := complete_block_reads p ops input row s entry.reads
    pc := fun t ht => (complete_block_pc_other p ops input row t s (outside t ht)).trans (entry.pc t ht)
    epoch := by
      intro t ht
      rw [complete_block_epoch_other p ops input row t s (outside t ht)]
      exact entry.epoch t ht }

theorem complete_block_row_values (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) (reads : Reads p input s) : RowValues ops input row (completeBlock p ops input row s) := by
  intro col hc
  have ht : col/8%1024<1024 := Nat.mod_lt _ (by decide)
  have hi : col/8192<2 := by omega
  have hcomp : col%8<8 := Nat.mod_lt _ (by decide)
  have value := complete_block_value p ops input row (col/8%1024) (col/8192) (col%8) s reads ht hi hcomp
  rw [← source_result_column ops input row (col/8%1024) (col/8192) (col%8) ht hcomp] at value
  simpa only [column_coordinates] using value

def nativeRows (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (rows : List Nat) (s : State α) : State α :=
  rows.foldl (fun s row => completeBlock p ops input row s) s

theorem native_rows_cons (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (rows : List Nat) (s : State α) :
    nativeRows p ops input (row::rows) s=nativeRows p ops input rows (completeBlock p ops input row s) := rfl

theorem native_rows_pc_other (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (rows : List Nat) (s : State α) (t : Nat) (outside : ∀ row∈rows,t∉blockThreads (geometry p) row) :
    (nativeRows p ops input rows s).pc t=s.pc t := by
  induction rows generalizing s with
  | nil => rfl
  | cons row rows ih =>
      exact (ih (completeBlock p ops input row s) (fun r hr => outside r (by simp [hr]))).trans
        (complete_block_pc_other p ops input row t s (outside row (by simp)))

theorem native_rows_pc (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (rows : List Nat) (s : State α) (hn : rows.Nodup) (row tid : Nat) (hr : row∈rows) (ht : tid<1024) :
    (nativeRows p ops input rows s).pc (row*1024+tid)=109 := by
  induction rows generalizing s with
  | nil => simp at hr
  | cons r rows ih =>
      obtain ⟨hnot,hnodup⟩ := List.nodup_cons.mp hn
      rcases List.mem_cons.mp hr with he | hm
      · subst row
        exact (native_rows_pc_other p ops input rows (completeBlock p ops input r s) (r*1024+tid)
          (by intro u hu; exact other_row_thread p u r tid ht (by intro he; subst u; exact hnot hu))).trans
          (complete_block_pc p ops input r s _ ((block_member p r _).mpr ⟨tid,ht,rfl⟩))
      · exact ih (completeBlock p ops input r s) hnodup hm

theorem native_rows_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (rows : List Nat) (s : State α) (reads : Reads p input s) : Reads p input (nativeRows p ops input rows s) := by
  induction rows generalizing s with
  | nil => exact reads
  | cons row rows ih => exact ih (completeBlock p ops input row s) (complete_block_reads p ops input row s reads)

theorem native_rows_memory_other (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (rows : List Nat) (s : State α) (row col : Nat) (hc : col<16384) (outside : row∉rows) :
    (nativeRows p ops input rows s).memory (globalCell 0 (address row col))=s.memory (globalCell 0 (address row col)) := by
  induction rows generalizing s with
  | nil => rfl
  | cons r rows ih =>
      have hne : row≠r := by intro he; subst row; simp at outside
      have hn : row∉rows := by intro hm; exact outside (by simp [hm])
      have owner : writer (address row col)=row*1024+(col/8%1024) := by unfold writer address; omega
      have disjoint : writer (address row col)∉blockThreads (geometry p) r := by
        rw [owner]
        exact other_row_thread p r row (col/8%1024) (Nat.mod_lt _ (by decide)) hne
      exact (ih (completeBlock p ops input r s) hn).trans (complete_block_previous_output p ops input r _ s disjoint)

theorem native_rows_entry_tail (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (rows : List Nat) (s : State α) (hn : row∉rows)
    (entry : ∀ r∈row::rows,BlockEntry p input r s) :
    ∀ r∈rows,BlockEntry p input r (completeBlock p ops input row s) := by
  intro r hr
  exact block_entry_other p ops input row r s (by intro he; subst r; exact hn hr) (entry r (by simp [hr]))

theorem native_rows_values (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (rows : List Nat) (s : State α) (hn : rows.Nodup) (entry : ∀ r∈rows,BlockEntry p input r s)
    (row : Nat) (hr : row∈rows) : RowValues ops input row (nativeRows p ops input rows s) := by
  induction rows generalizing s with
  | nil => simp at hr
  | cons r rows ih =>
      obtain ⟨hnot,hnodup⟩ := List.nodup_cons.mp hn
      rcases List.mem_cons.mp hr with he | hm
      · subst row
        have head := complete_block_row_values p ops input r s (entry r (by simp)).reads
        intro col hc
        exact (native_rows_memory_other p ops input rows (completeBlock p ops input r s) r col hc hnot).trans (head col hc)
      · exact ih (completeBlock p ops input r s) hnodup (native_rows_entry_tail p ops input r rows s hnot entry) hm

theorem native_rows_exec (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (rows : List Nat) (s : State α) (hn : rows.Nodup) (entry : ∀ row∈rows,BlockEntry p input row s)
    (good : ∀ event∈s.trace,Good event) :
    rows.foldlM (fun u row => LarkPartitionCollective.runBlock ops (layout p) (geometry p) fuel (program true)
      row fuel.block u) s=some (nativeRows p ops input rows s) ∧
      (∀ event∈(nativeRows p ops input rows s).trace,Good event) := by
  induction rows generalizing s with
  | nil => exact ⟨rfl,good⟩
  | cons row rows ih =>
      obtain ⟨hnot,hnodup⟩ := List.nodup_cons.mp hn
      have head := entry row (by simp)
      have h := ih (completeBlock p ops input row s) hnodup (native_rows_entry_tail p ops input row rows s hnot entry)
        (complete_block_good p ops input row s head.reads head.epoch good)
      refine ⟨?_,h.2⟩
      rw [List.foldlM_cons,complete_block_run p ops input row s head.valid head.pc head.reads]
      exact h.1

#print axioms source_result_column
#print axioms column_coordinates
#print axioms initial_block_entry
#print axioms block_entry_other
#print axioms complete_block_row_values
#print axioms native_rows_cons
#print axioms native_rows_pc_other
#print axioms native_rows_pc
#print axioms native_rows_reads
#print axioms native_rows_memory_other
#print axioms native_rows_entry_tail
#print axioms native_rows_values
#print axioms native_rows_exec
end LarkNativeSglangRmsNorm
