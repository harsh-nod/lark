import Lark.NativeFlashInferRmsNormBlockFrame

/-! Row ownership: a complete block changes only its output row and its own
shared memory. Read-only input/weight cells and other rows are never reseeded.
-/
namespace LarkNativeFlashInferRmsNorm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def RowWrites (row : Nat) (l : Location) : Prop :=
  (l.space = .global ∧ l.owner = 0 ∧ l.buffer = 0 ∧ l.offset / 16384 = row) ∨
  (l.space = .shared ∧ l.owner = row)

theorem writer_row (offset : Nat) : writer offset / 1024 = offset / 16384 := by
  have h := Nat.mod_lt (offset % 16384 / 8) (by decide : 0 < 1024)
  unfold writer
  omega

theorem partial_writes_row (row t : Nat) (l : Location) (hr : t / 1024 = row) (ho : PartialWrites t l) : RowWrites row l := by
  rcases ho with ⟨_,rfl⟩
  exact Or.inr ⟨rfl,hr⟩

theorem output_writes_row (row tid : Nat) (l : Location) (ht : tid < 1024) (ho : OutputWrites row tid l) : RowWrites row l := by
  obtain ⟨j,hj,rfl⟩ := ho
  have hb := slot_bound tid j ht hj
  refine Or.inl ⟨rfl,rfl,rfl,?_⟩
  change (row * 16384 + slot tid j) / 16384 = row
  omega

theorem first_wave_row_frame (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp : Nat) (s : State α) (hw : warp < 16) (l : Location) (hl : ¬ RowWrites row l) :
    (firstWave p ops input row warp s).memory l = s.memory l := by
  apply first_wave_partial_memory_frame p ops input row warp s l
  intro t ht ho
  obtain ⟨lane,hlane,rfl⟩ := (cohort_mem row warp 64 t).mp ht
  exact hl (partial_writes_row row _ l (cohort_arithmetic row warp lane hw hlane).1 ho)

theorem wave_fold_row_frame (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ws : List Nat) (s : State α) (hw : ∀ w ∈ ws, w < 16) (l : Location) (hl : ¬ RowWrites row l) :
    (waveFold p ops input row ws s).memory l = s.memory l := by
  induction ws generalizing s with
  | nil => rfl
  | cons w ws ih =>
      exact (ih (firstWave p ops input row w s) (by intro u hu; exact hw u (by simp [hu]))).trans
        (first_wave_row_frame p ops input row w s (hw w (by simp)) l hl)

theorem resume_memory (ts : List Nat) (s : State α) : (resume ts .block s).memory = s.memory := rfl

theorem native_block_memory_frame (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) (l : Location) (hl : ¬ RowWrites row l) :
    (nativeBlock p ops input row s).memory l = s.memory l := by
  have h0 := wave_fold_row_frame p ops input row (List.range 16) s (fun w hw => List.mem_range.mp hw) l hl
  have hn : l ≠ partialSlot row 0 := by intro he; subst l; exact hl (Or.inr ⟨rfl,rfl⟩)
  have h01 := congrFun (resume_memory (blockThreads (geometry p) row) (firstBlock p ops input row s)) l
  have h1 := scale_block_memory_frame p ops input row (midState p ops input row s) l hn
  have h12 := congrFun (resume_memory (blockThreads (geometry p) row) (scaleBlock p ops input row (midState p ops input row s))) l
  have h2 := output_block_memory_frame p ops input row (outState p ops input row (midState p ops input row s)) l
    (by intro tid ht ho; exact hl (output_writes_row row tid l ht ho))
  exact h2.trans (h12.trans (h1.trans (h01.trans h0)))

theorem row_global_other (row other col buffer : Nat) (hc : col < 16384) (hne : other ≠ row) :
    ¬ RowWrites row (globalCell buffer (address other col)) := by
  intro h
  rcases h with h | h
  · have hx := h.2.2.2
    change (other * 16384 + col) / 16384 = row at hx
    have he : (other * 16384 + col) / 16384 = other := by omega
    exact hne (he.symm.trans hx)
  · cases h.1

theorem native_block_value_other (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row other col buffer : Nat) (s : State α) (hne : other ≠ row) (hc : col < 16384) :
    (nativeBlock p ops input row s).memory (globalCell buffer (address other col)) = s.memory (globalCell buffer (address other col)) :=
  native_block_memory_frame p ops input row s _ (row_global_other row other col buffer hc hne)

theorem block_entry_from_frames (p : Shape) (input : Nat → Nat → α) (row : Nat)
    (s next : State α) (entry : BlockEntry p input row s)
    (pc : ∀ tid, tid < 1024 → next.pc (row * 1024 + tid) = s.pc (row * 1024 + tid))
    (memory : ∀ buffer col, col < 16384 → next.memory (globalCell buffer (address row col)) = s.memory (globalCell buffer (address row col)))
    (weight : ∀ col, col < 16384 → next.memory (globalCell 2 col) = s.memory (globalCell 2 col))
    (epoch : ∀ tid, tid < 1024 → next.epochs (row * 1024 + tid) = s.epochs (row * 1024 + tid))
    (good : ∀ a ∈ next.trace, Good a) : BlockEntry p input row next := by
  exact {
    valid := entry.valid
    pc := fun tid ht => (pc tid ht).trans (entry.pc tid ht)
    inputs := by
      intro tid ht j hj
      exact (memory 1 (slot tid j) (slot_bound tid j ht hj)).trans (entry.inputs tid ht j hj)
    weights := fun col hc => (weight col hc).trans (entry.weights col hc)
    epoch := fun tid ht => (congrArg Epoch.block (epoch tid ht)).trans (entry.epoch tid ht)
    good := good }

theorem native_block_entry_other (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row other : Nat) (s : State α) (hne : other ≠ row)
    (entry : BlockEntry p input row s) (otherEntry : BlockEntry p input other s) :
    BlockEntry p input other (nativeBlock p ops input row s) :=
  block_entry_from_frames p input other s (nativeBlock p ops input row s) otherEntry
    (fun tid ht => native_block_pc_other p ops input row (other * 1024 + tid) s (other_row_thread p row other tid ht hne))
    (fun buffer col hc => native_block_value_other p ops input row other col buffer s hne hc)
    (fun col hc => native_block_memory_frame p ops input row s _ (by simp [RowWrites,globalCell]))
    (fun tid ht => native_block_epoch_other p ops input row (other * 1024 + tid) s (other_row_thread p row other tid ht hne))
    (native_block_good p ops input row s entry)

#print axioms writer_row
#print axioms partial_writes_row
#print axioms output_writes_row
#print axioms first_wave_row_frame
#print axioms wave_fold_row_frame
#print axioms resume_memory
#print axioms native_block_memory_frame
#print axioms row_global_other
#print axioms native_block_value_other
#print axioms block_entry_from_frames
#print axioms native_block_entry_other
end LarkNativeFlashInferRmsNorm
