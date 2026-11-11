import Lark.NativeSoftmaxExpBarrier

/-! Exact trace counts for the scalar exp plus native sum phase. Logical32
snapshot shuffles and register adds contribute no access record or fence. -/
namespace LarkNativeSoftmax
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem sum_partial_trace_length (t lane warp : Nat) (value : α) (s : State α) :
    (sumPartialAfter t lane warp value s).trace.length=s.trace.length+if lane=0 then 1 else 0 := by
  by_cases hz : lane=0 <;> simp [sumPartialAfter,hz,sumPartialWritten,written,advance,record]

theorem sum_last_trace_length (ops : Ops α) (t : Nat) (a b : α) (s : State α) :
    (sumLastAfter ops t a b s).trace.length=s.trace.length+if t%1024%32=0 then 1 else 0 :=
  sum_partial_trace_length t _ _ _ _

theorem sum_last_fold_trace_length (ops : Ops α) (a b : Nat → α) (ts : List Nat) (s : State α) :
    (sumLastFold ops a b ts s).trace.length=s.trace.length+partialCount ts := by
  induction ts generalizing s with
  | nil => simp [sumLastFold,partialCount]
  | cons t ts ih =>
    change (sumLastFold ops a b ts (sumLastAfter ops t (a t) (b t) s)).trace.length=_
    rewrite [ih,sum_last_trace_length]
    simp only [partialCount,List.countP_cons,beq_iff_eq]
    omega

theorem sum_last_wave_trace_length (p : Shape) (ops : Ops α) (row warp : Nat)
    (values : Nat → α) (s : State α) :
    (sumLastWave p ops row warp values s).trace.length=s.trace.length+partialCount (cohortThreads row warp 64) :=
  sum_last_fold_trace_length ops (sumWaveLeft p values) (sumWaveRight p values) (cohortThreads row warp 64)
    (LarkCollective.shuffleUpdates 9 (sumXorSnapshot p row warp 64 1 values) s)

def expLaneAccesses (tid : Nat) : Nat := if tid<81 then 213 else 211

theorem exp_scalar_fold_trace_length (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ts : List Nat) (s : State α) :
    (expScalarFold ops input row ts s).trace.length=s.trace.length+(ts.map (fun t => expLaneAccesses (t%1024))).sum := by
  induction ts generalizing s with
  | nil => simp [expScalarFold]
  | cons t ts ih =>
    change (expScalarFold ops input row ts (expLaneStep ops input row t s)).trace.length=_
    rewrite [ih]
    have h := exp_prefix_trace_exact ops input row (t%1024) s (Nat.mod_lt _ (by decide))
    change (expLaneStep ops input row t s).trace.length=s.trace.length+expLaneAccesses (t%1024) at h
    rewrite [h,List.map_cons,List.sum_cons]
    omega

def expScalarWaveAccesses (warp : Nat) : Nat := if warp=0 then 13632 else if warp=1 then 13538 else 13504

theorem exp_scalar_wave_accesses (warp : Nat) (hw : warp<16) :
    ((List.range 64).map (fun lane => expLaneAccesses (warp*64+lane))).sum=expScalarWaveAccesses warp := by
  have table : ∀ w : Fin 16,
      ((List.range 64).map (fun lane => expLaneAccesses (w.val*64+lane))).sum=expScalarWaveAccesses w.val := by decide
  exact table ⟨warp,hw⟩

theorem exp_scalar_wave_trace_length (ops : Ops α) (input : Nat → Nat → α)
    (row warp : Nat) (s : State α) (hw : warp<16) :
    (expScalarWave ops input row warp s).trace.length=s.trace.length+expScalarWaveAccesses warp := by
  have h := exp_scalar_fold_trace_length ops input row (cohortThreads row warp 64) s
  change (expScalarWave ops input row warp s).trace.length=_ at h
  apply h.trans
  apply congrArg (s.trace.length+·)
  unfold cohortThreads
  rewrite [List.map_map]
  change ((List.range 64).map (fun lane => expLaneAccesses ((cohortBase row warp+lane)%1024))).sum=_
  have he : (List.range 64).map (fun lane => expLaneAccesses ((cohortBase row warp+lane)%1024))=
      (List.range 64).map (fun lane => expLaneAccesses (warp*64+lane)) := by
    apply List.map_congr_left
    intro lane hl
    rewrite [(cohort_arithmetic row warp lane hw (List.mem_range.mp hl)).2.1]
    rfl
  rewrite [he]
  exact exp_scalar_wave_accesses warp hw

def expWaveAccesses (warp : Nat) : Nat := expScalarWaveAccesses warp+2

theorem exp_wave_trace_length (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp : Nat) (s : State α) (hw : warp<16) :
    (expWave p ops input row warp s).trace.length=s.trace.length+expWaveAccesses warp := by
  have h := sum_last_wave_trace_length p ops row warp (sumWaveValues ops input row warp 4)
    (sumStages p ops input row warp 0 4 (expScalarWave ops input row warp s))
  change (expWave p ops input row warp s).trace.length=_ at h
  exact h.trans (by
    rewrite [(sum_stages_preserves p ops input row warp 0 4 _).2.2.2,
      exp_scalar_wave_trace_length ops input row warp s hw,cohort_partial_count row warp hw]
    rfl)

theorem exp_wave_fold_trace_length (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ws : List Nat) (s : State α) (hb : ∀ w ∈ ws, w<16) :
    (expWaveFold p ops input row ws s).trace.length=s.trace.length+(ws.map expWaveAccesses).sum := by
  induction ws generalizing s with
  | nil => simp [expWaveFold]
  | cons w ws ih =>
    change (expWaveFold p ops input row ws (expWave p ops input row w s)).trace.length=_
    rewrite [ih _ (by intro u hu; exact hb u (by simp [hu])),exp_wave_trace_length p ops input row w s (hb w (by simp)),List.map_cons,List.sum_cons]
    omega

theorem exp_block_trace_length (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) : (expBlock p ops input row s).trace.length=s.trace.length+216258 := by
  have h := exp_wave_fold_trace_length p ops input row (List.range 16) s (fun _w hw => List.mem_range.mp hw)
  have count : ((List.range 16).map expWaveAccesses).sum=216258 := by decide
  simpa only [count] using h

theorem after_exp_trace_length (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) : (afterExp p ops input row s).trace.length=s.trace.length+216258 :=
  exp_block_trace_length p ops input row s

theorem exp_count_total_of_start (before after : State α) (n k : Nat)
    (hbefore : before.trace.length=n) (hafter : after.trace.length=before.trace.length+k) :
    after.trace.length=n+k := by
  rewrite [hbefore] at hafter
  exact hafter

theorem exp_trace_length_of_nil (before after : State α) (n : Nat)
    (hbefore : before.trace=[]) (hafter : after.trace.length=before.trace.length+n) : after.trace.length=n := by
  simpa only [hbefore,List.length_nil,Nat.zero_add] using hafter

theorem exp_counts_after_sized_start (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) (hstart : s.trace.length=57409) :
    (afterExp p ops input row s).trace.length=273667 :=
  exp_count_total_of_start s (afterExp p ops input row s) 57409 216258 hstart
    (after_exp_trace_length p ops input row s)

theorem initial_after_exp_trace_length (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row : Nat) :
    (afterExp p ops input row (maximumState p ops input row (initial (layout p) input outside))).trace.length=273667 :=
  exp_counts_after_sized_start p ops input row (maximumState p ops input row (initial (layout p) input outside))
    (exp_trace_length_of_nil (initial (layout p) input outside)
      (maximumState p ops input row (initial (layout p) input outside)) 57409 rfl
      (maximum_trace_length p ops input row (initial (layout p) input outside)))

#print axioms sum_partial_trace_length
#print axioms sum_last_trace_length
#print axioms sum_last_fold_trace_length
#print axioms sum_last_wave_trace_length
#print axioms exp_scalar_fold_trace_length
#print axioms exp_scalar_wave_accesses
#print axioms exp_scalar_wave_trace_length
#print axioms exp_wave_trace_length
#print axioms exp_wave_fold_trace_length
#print axioms exp_block_trace_length
#print axioms after_exp_trace_length
#print axioms exp_count_total_of_start
#print axioms exp_trace_length_of_nil
#print axioms exp_counts_after_sized_start
#print axioms initial_after_exp_trace_length
end LarkNativeSoftmax
