import Lark.NativeSoftmaxMaxFirstWave

/-! Exact access count of the actual first wave: 3,584 input reads and two
shared partial writes. Snapshot transport has no memory access or fence. -/
namespace LarkNativeSoftmax
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem partial_trace_length (t lane warp : Nat) (value : α) (s : State α) :
    (partialAfter t lane warp value s).trace.length = s.trace.length + if lane = 0 then 1 else 0 := by
  by_cases hz : lane = 0 <;>
    simp [partialAfter,hz,partialWritten,written,advance,record]

theorem first_last_trace_length (ops : Ops α) (t : Nat) (a b : α) (s : State α) :
    (firstLastAfter ops t a b s).trace.length = s.trace.length + if t%1024%32 = 0 then 1 else 0 :=
  partial_trace_length t _ _ _ _

def partialCount (ts : List Nat) : Nat := ts.countP (fun t => t%1024%32 == 0)

theorem last_fold_trace_length (ops : Ops α) (a b : Nat → α) (ts : List Nat) (s : State α) :
    (lastFold ops a b ts s).trace.length = s.trace.length + partialCount ts := by
  induction ts generalizing s with
  | nil => simp [lastFold,partialCount]
  | cons t ts ih =>
    change (lastFold ops a b ts (firstLastAfter ops t (a t) (b t) s)).trace.length = _
    rewrite [ih,first_last_trace_length]
    simp only [partialCount,List.countP_cons,beq_iff_eq]
    omega

theorem cohort_partial_count (row warp : Nat) (hw : warp < 16) :
    partialCount (cohortThreads row warp 64) = 2 := by
  unfold partialCount cohortThreads
  rewrite [List.countP_map]
  have he : (List.range 64).countP (fun lane => (cohortBase row warp+lane)%1024%32 == 0) =
      (List.range 64).countP (fun lane => lane%32 == 0) := by
    apply List.countP_congr
    intro lane hl
    have hl := List.mem_range.mp hl
    have coords := (cohort_arithmetic row warp lane hw hl).2.1
    rewrite [coords]
    simp only [beq_iff_eq]
    omega
  change (List.range 64).countP (fun lane => (cohortBase row warp+lane)%1024%32 == 0) = 2
  rewrite [he]
  decide

theorem last_wave_trace_length (p : Shape) (ops : Ops α) (row warp : Nat)
    (values : Nat → α) (s : State α) :
    (lastWave p ops row warp values s).trace.length = s.trace.length + partialCount (cohortThreads row warp 64) :=
  last_fold_trace_length ops (waveLeft p values) (waveRight p values) (cohortThreads row warp 64)
    (LarkCollective.shuffleUpdates 2 (downSnapshot p row warp 64 1 values) s)

theorem first_wave_trace_length (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp : Nat) (s : State α) (hw : warp < 16) :
    (firstWave p ops input row warp s).trace.length = s.trace.length + 3586 := by
  have last := last_wave_trace_length p ops row warp (waveValues ops input row warp 4)
    (firstStages p ops input row warp 0 4 (maxPrefixFold ops input (cohortThreads row warp 64) s))
  change (firstWave p ops input row warp s).trace.length = _ at last
  exact last.trans (by
    rewrite [(first_stages_preserves p ops input row warp 0 4 _).2.2.2,
      native_prefix_trace_length,cohort_partial_count row warp hw]
    omega)

#print axioms partial_trace_length
#print axioms first_last_trace_length
#print axioms last_fold_trace_length
#print axioms cohort_partial_count
#print axioms last_wave_trace_length
#print axioms first_wave_trace_length
end LarkNativeSoftmax
