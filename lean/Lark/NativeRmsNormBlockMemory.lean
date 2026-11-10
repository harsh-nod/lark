import Lark.NativeRmsNormBlockFrame

/-! A completed row preserves every other row's output values. -/
namespace LarkNativeRmsNorm
open LarkNonlinear
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem first_block_global_frame (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) (l : Location) (hl : l.space = .global) :
    (firstBlock p ops input row s).memory l = s.memory l := by
  apply wave_fold_memory_other p ops input row (List.range 16) s (fun w hw => List.mem_range.mp hw) l
  intro w hw he
  have hs := congrArg Location.space he
  simp only [hl, partialCell] at hs
  cases hs

theorem early_block_global_frame (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) (l : Location) (hl : l.space = .global) :
    (outState p ops input row (midState p ops input row s)).memory l = s.memory l := by
  have h0 := first_block_global_frame p ops input row s l hl
  have h1 := congrFun (resume_memory (blockThreads (geometry p) row) (firstBlock p ops input row s)) l
  have h2 := scale_block_memory_other p ops input row (midState p ops input row s) l (by
    intro he
    have hs := congrArg Location.space he
    simp only [hl, scaleSlot] at hs
    cases hs)
  have h3 := congrFun (resume_memory (blockThreads (geometry p) row)
    (scaleBlock p ops input row (midState p ops input row s))) l
  exact h3.trans (h2.trans (h1.trans h0))

theorem column_writer (p : Shape) (row col : Nat) (hc : col < 16384) :
    LarkVectorStride.writer (traversal p) (row * 16384 + col) = row * 1024 + col / 8 % 1024 := by
  have hv : col / 8 < 2048 := by omega
  have hcomp : col % 8 < 8 := Nat.mod_lt _ (by decide)
  have he : scalarAddress row (col / 8) (col % 8) = row * 16384 + col := by
    unfold scalarAddress
    have h := Nat.div_add_mod col 8
    omega
  exact (congrArg (LarkVectorStride.writer (traversal p)) he).symm.trans
    (output_writer p row (col / 8) (col % 8) hv hcomp)

theorem native_block_value_other (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row other col : Nat) (s : State α) (hne : other ≠ row) (hc : col < 16384) :
    (nativeBlock p ops input row s).memory (globalCell 0 (other * 16384 + col)) =
      s.memory (globalCell 0 (other * 16384 + col)) := by
  have hw := column_writer p other col hc
  have ht : col / 8 % 1024 < 1024 := Nat.mod_lt _ (by decide)
  have hf := output_fold_memory_frame p ops input row (blockThreads (geometry p) row)
    (outState p ops input row (midState p ops input row s)) (block_owner p row)
    (globalCell 0 (other * 16384 + col)) (by
      intro t hm howner
      obtain ⟨tid, htid, rfl⟩ := (block_mem p row t).mp hm
      have he : other * 1024 + col / 8 % 1024 = row * 1024 + tid := hw.symm.trans howner.2.2.2
      omega)
  exact hf.trans (early_block_global_frame p ops input row s (globalCell 0 (other * 16384 + col)) rfl)

#print axioms native_block_value_other
end LarkNativeRmsNorm
