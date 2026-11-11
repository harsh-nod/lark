import LarkReal.NativeAttentionOnline

/-! Canonical dense SDPA for the complete actual native attention launch.
Half conversions are identities only in this explicitly idealized real model. -/
namespace LarkReal.NativeAttention
open LarkNativeAttention LarkNonlinear
set_option maxRecDepth 1000
set_option maxHeartbeats 2000000

theorem tile_entries_range (input : Nat → Nat → ℝ) (t qi key : Nat) :
    tileEntries input t qi key = (List.range' (key * 32) 32).map (denseEntry input t qi) := by
  simp only [tileEntries, List.range'_eq_map_range, List.map_map, Function.comp_def]

theorem processed_entries_dense (input : Nat → Nat → ℝ) (t qi n : Nat) :
    processedEntries input t qi n = (List.range (n * 32)).map (denseEntry input t qi) := by
  induction n with
  | zero => simp [processedEntries]
  | succ n ih =>
      rw [processed_entries_succ, ih, tile_entries_range, ← List.map_append]
      have h := List.range'_append (s := 0) (m := n * 32) (n := 32) (step := 1)
      have he : List.range (n * 32) ++ List.range' (n * 32) 32 = List.range ((n + 1) * 32) := by
        simpa [List.range'_eq_map_range, Nat.add_mul] using h
      exact congrArg (fun xs => xs.map (denseEntry input t qi)) he

theorem online_dense_reference (input : Nat → Nat → ℝ) (t qi col : Nat) :
    (onlineValues ops input 4 t qi).stored col = OnlineSoftmax.reference (denseEntries input t qi) col := by
  have hv := OnlineSoftmax.valid_reference (processedEntries input t qi 4) (toAccumulator (onlineValues ops input 4 t qi))
    (online_real_valid input t qi 3) col
  have entries : processedEntries input t qi 4 = denseEntries input t qi := by
    exact processed_entries_dense input t qi 4
  exact hv.trans (congrArg (fun xs => OnlineSoftmax.reference xs col) entries)

noncomputable def denseValue (input : Nat → Nat → ℝ) (offset : Nat) : ℝ :=
  OnlineSoftmax.reference (denseEntries input (writer offset) (offset / 8192 % 4)) (offset % 256)
noncomputable def denseSpec (p : Shape) (input : Nat → Nat → ℝ) : List ℝ :=
  (List.range (p.groups * 32768)).map (denseValue input)

theorem source_spec_dense (p : Shape) : sourceSpec p ops = denseSpec p := by
  funext input
  unfold sourceSpec denseSpec
  apply congrArg (fun f : Nat → ℝ => (List.range (p.groups * 32768)).map f)
  funext offset
  exact online_dense_reference input (writer offset) (offset / 8192 % 4) (offset % 256)

/-- All allowed group counts and all inputs/outside memory: the actual source
launch halts, its complete trace is race free and every output equals dense
real-valued SDPA with 128 keys, 256 components and the source's 1/16 scale. -/
theorem correct (p : Shape) : Correct ops (layout p) (geometry p) fuel program (denseSpec p) := by
  rw [← source_spec_dense p]
  exact source_order_correct p ops

#print axioms processed_entries_dense
#print axioms online_dense_reference
#print axioms source_spec_dense
#print axioms correct
end LarkReal.NativeAttention
