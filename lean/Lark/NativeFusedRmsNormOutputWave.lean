import Lark.NativeFusedRmsNormOutputFold

/-! Actual physical-wave64 output execution, including all sequential lane
visits and convergence at the source halt.
-/
namespace LarkNativeFusedRmsNorm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem cohort_halt (row warp width : Nat) (s : State α) (hpos : 0 < width)
    (hp : ∀ lane, lane < width → s.pc (cohortBase row warp + lane) = 71) :
    LarkPartitionCollective.nextCohort program (cohortThreads row warp width) s = none ∧
    LarkCollective.converged program (cohortThreads row warp width) s = some .halt := by
  have hp0 : s.pc (cohortBase row warp) = 71 := by simpa only [Nat.add_zero] using hp 0 hpos
  have hf : (cohortThreads row warp width).filter (LarkPartitionCollective.isShuffle program s) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro t ht
    obtain ⟨lane,hl,rfl⟩ := (cohort_mem row warp width t).mp ht
    simp only [LarkPartitionCollective.isShuffle, hp lane hl, final_halt]
    decide
  have ha : (cohortThreads row warp width).all (fun t => s.pc t == s.pc (cohortBase row warp)) = true := by
    apply List.all_eq_true.mpr
    intro t ht
    obtain ⟨lane,hl,rfl⟩ := (cohort_mem row warp width t).mp ht
    simp [hp lane hl,hp0]
  constructor
  · simp only [LarkPartitionCollective.nextCohort,hf,List.head?_nil,bind,Option.bind]
  · unfold LarkCollective.converged
    rewrite [cohort_head row warp width hpos]
    simp only [bind,pure,Option.bind,ha,↓reduceIte]
    unfold LarkCollective.parked
    rewrite [hp0,final_halt]
    rfl

theorem warp_at_halt (p : Shape) (ops : Ops α) (row warp width extra : Nat)
    (s next : State α) (hpos : 0 < width)
    (hf : (cohortThreads row warp width).foldlM
      (fun u t => LarkCollective.runLane ops (layout p) (geometry p) program t fuel.lane u) s = some next)
    (hp : ∀ lane, lane < width → next.pc (cohortBase row warp + lane) = 71) :
    LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel program
      (cohortThreads row warp width) (extra + 1) s = some next := by
  rcases cohort_halt row warp width next hpos hp with ⟨hc,hconverged⟩
  rewrite [LarkPartitionCollective.runWarp,hf]
  simp only [bind,pure,Option.some_bind,hc,hconverged,reduceCtorEq,↓reduceIte]

def outputWave (ops : Ops α) (input : Nat → Nat → α) (row warp : Nat) (s : State α) : State α :=
  outputFold ops input row (cohortThreads row warp 64) s

theorem output_wave_run (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp : Nat) (s : State α) (hw : warp < 16)
    (entry : OutputFoldEntry p ops input row (cohortThreads row warp 64) s) :
    LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel program
      (warpThreads (geometry p) row warp) fuel.warp s = some (outputWave ops input row warp s) := by
  rewrite [cohort_native_threads p row warp hw,show fuel.warp = 7 + 1 by decide]
  apply warp_at_halt p ops row warp 64 7 s (outputWave ops input row warp s) (by decide)
  · apply output_fold_run p ops input row _ s (cohort_nodup row warp 64) ?_ entry
    intro t ht
    obtain ⟨lane,hl,rfl⟩ := (cohort_mem row warp 64 t).mp ht
    exact (cohort_arithmetic row warp lane hw hl).1
  · intro lane hl
    exact output_fold_pc ops input row _ s (cohort_nodup row warp 64) _ ((cohort_mem row warp 64 _).mpr ⟨lane,hl,rfl⟩)

theorem output_wave_trace_length (ops : Ops α) (input : Nat → Nat → α) (row warp : Nat) (s : State α) :
    (outputWave ops input row warp s).trace.length = s.trace.length + 3136 := by
  simpa only [cohortThreads,List.length_map,List.length_range] using
    output_fold_trace_length ops input row (cohortThreads row warp 64) s

#print axioms cohort_halt
#print axioms warp_at_halt
#print axioms output_wave_run
#print axioms output_wave_trace_length
end LarkNativeFusedRmsNorm
