import Lark.NativeSoftmaxNormBlock

/-! Exact whole-block normalization access counts, derived from all actual
lane and native-wave folds. These counts retain the original extra clamp reads. -/
namespace LarkNativeSoftmax
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def normLaneAccesses (guarded : Bool) (tid : Nat) : Nat :=
  if guarded then (if tid<81 then 201 else 197) else (if tid<81 then 213 else 211)

def normWaveAccesses (guarded : Bool) (warp : Nat) : Nat :=
  if guarded then (if warp=0 then 12864 else if warp=1 then 12676 else 12608)
  else (if warp=0 then 13632 else if warp=1 then 13538 else 13504)

theorem norm_wave_accesses_table (guarded : Bool) (warp : Nat) (hw : warp<16) :
    ((List.range 64).map (fun lane => normLaneAccesses guarded (warp*64+lane))).sum=normWaveAccesses guarded warp := by
  have table : ∀ w : Fin 16,
      ((List.range 64).map (fun lane => normLaneAccesses guarded (w.val*64+lane))).sum=normWaveAccesses guarded w.val := by
    cases guarded <;> decide
  exact table ⟨warp,hw⟩

theorem norm_wave_accesses (guarded : Bool) (row warp : Nat) (hw : warp<16) :
    normScalarAccesses guarded (cohortThreads row warp 64)=normWaveAccesses guarded warp := by
  unfold normScalarAccesses cohortThreads
  rewrite [List.map_map]
  change ((List.range 64).map (fun lane => normLaneAccesses guarded ((cohortBase row warp+lane)%1024))).sum=_
  have he : (List.range 64).map (fun lane => normLaneAccesses guarded ((cohortBase row warp+lane)%1024))=
      (List.range 64).map (fun lane => normLaneAccesses guarded (warp*64+lane)) := by
    apply List.map_congr_left
    intro lane hl
    rewrite [(cohort_arithmetic row warp lane hw (List.mem_range.mp hl)).2.1]
    rfl
  rewrite [he]
  exact norm_wave_accesses_table guarded warp hw

theorem norm_block_accesses (guarded : Bool) (row : Nat) :
    normWaveFoldAccesses guarded row (List.range 16)=(if guarded then 202052 else 216226) := by
  unfold normWaveFoldAccesses
  have he : (List.range 16).map (fun w => normScalarAccesses guarded (cohortThreads row w 64))=
      (List.range 16).map (normWaveAccesses guarded) := by
    apply List.map_congr_left
    intro w hw
    exact norm_wave_accesses guarded row w (List.mem_range.mp hw)
  rewrite [he]
  cases guarded <;> decide

theorem norm_block_trace_length (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) :
    (normBlock guarded ops input row s).trace.length=s.trace.length+(if guarded then 202052 else 216226) := by
  have h := norm_wave_fold_trace_length guarded ops input row (List.range 16) s
  rewrite [norm_block_accesses] at h
  exact h

#print axioms norm_wave_accesses_table
#print axioms norm_wave_accesses
#print axioms norm_block_accesses
#print axioms norm_block_trace_length
end LarkNativeSoftmax
