import Lark.NativeSoftmaxExpWave
namespace LarkNativeSoftmax
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem sum_xor_step_other (p : Shape) (ops : Ops α) (row warp active pc distance t : Nat)
    (values : Nat → α) (s : State α) (ht : t ∉ cohortThreads row warp active) :
    (sumXorStep p ops row warp active pc distance values s).pc t = s.pc t ∧
    (sumXorStep p ops row warp active pc distance values s).regs t = s.regs t := by
  have h := sum_combine_fold_other ops (pc + 1)
    (fun u => values (LarkPartitionCollective.nativeLane (geometry p) u))
    (fun u => values (sumXorPeer32 (LarkPartitionCollective.nativeLane (geometry p) u) distance))
    (cohortThreads row warp active) t (LarkCollective.shuffleUpdates 9 (sumXorSnapshot p row warp active distance values) s) ht
  have hs := sum_xor_shuffled_other p row warp active distance t values s ht
  exact ⟨h.1.trans hs.1, h.2.trans hs.2⟩

theorem sum_stages_other (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp n remaining t : Nat) (s : State α) (ht : t ∉ cohortThreads row warp 64) :
    (sumStages p ops input row warp n remaining s).pc t = s.pc t ∧
    (sumStages p ops input row warp n remaining s).regs t = s.regs t := by
  induction remaining generalizing n s with
  | zero => exact ⟨rfl, rfl⟩
  | succ remaining ih =>
      have h := ih (n + 1) (sumXorStep p ops row warp 64 (70 + 2 * n) (sumDistance n) (sumWaveValues ops input row warp n) s)
      have step := sum_xor_step_other p ops row warp 64 (70 + 2 * n) (sumDistance n) t (sumWaveValues ops input row warp n) s ht
      exact ⟨h.1.trans step.1, h.2.trans step.2⟩

theorem sum_last_wave_other (p : Shape) (ops : Ops α) (row warp t : Nat) (values : Nat → α)
    (s : State α) (ht : t ∉ cohortThreads row warp 64) :
    (sumLastWave p ops row warp values s).pc t = s.pc t ∧
    (sumLastWave p ops row warp values s).regs t = s.regs t := by
  have h := sum_last_fold_other ops (sumWaveLeft p values) (sumWaveRight p values) (cohortThreads row warp 64) t
    (LarkCollective.shuffleUpdates 9 (sumXorSnapshot p row warp 64 1 values) s) ht
  have hs := sum_xor_shuffled_other p row warp 64 1 t values s ht
  exact ⟨h.1.trans hs.1, h.2.trans hs.2⟩

theorem exp_wave_indices_eq (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp : Nat) (s : State α) :
    (expWave p ops input row warp s).indices=(expScalarWave ops input row warp s).indices :=
  (sum_last_wave_preserves p ops row warp (sumWaveValues ops input row warp 4) _).1.trans
    (sum_stages_preserves p ops input row warp 0 4 _).2.1

theorem exp_wave_other (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp t : Nat) (s : State α) (hw : warp<16) (ht : t ∉ cohortThreads row warp 64) :
    OtherThread t t s (expWave p ops input row warp s) := by
  have h0 := exp_scalar_fold_other ops input row (cohortThreads row warp 64) t s ht (exp_cohort_row row warp hw)
  have h1 := sum_stages_other p ops input row warp 0 4 t (expScalarWave ops input row warp s) ht
  have h2 := sum_last_wave_other p ops row warp t (sumWaveValues ops input row warp 4)
    (sumStages p ops input row warp 0 4 (expScalarWave ops input row warp s)) ht
  exact ⟨h2.1.trans (h1.1.trans h0.1),
    (congrFun (exp_wave_indices_eq p ops input row warp s) t).trans h0.2.1,
    h2.2.trans (h1.2.trans h0.2.2)⟩

theorem exp_scalar_fold_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ts : List Nat) (s : State α) (reads : Reads p input s) :
    Reads p input (expScalarFold ops input row ts s) := by
  induction ts generalizing s with
  | nil => exact reads
  | cons t ts ih => exact ih _ (exp_prefix_reads p ops input row (t%1024) s reads)

theorem exp_scalar_fold_shared (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ts : List Nat) (s : State α) (l : Location) (hl : l.space=.shared) :
    (expScalarFold ops input row ts s).memory l=s.memory l := by
  induction ts generalizing s with
  | nil => rfl
  | cons t ts ih =>
    apply (ih (expLaneStep ops input row t s)).trans
    apply exp_prefix_memory_frame ops input row (t%1024) s l
    · left; rewrite [hl]; decide
    · intro i hi j hj hc he
      have h := congrArg Location.space he
      simp only [globalCell,hl] at h
      cases h

theorem exp_wave_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp : Nat) (s : State α) (reads : Reads p input s) : Reads p input (expWave p ops input row warp s) := by
  intro offset hb
  apply (sum_last_wave_memory_frame p ops row warp (sumWaveValues ops input row warp 4)
    (sumStages p ops input row warp 0 4 (expScalarWave ops input row warp s)) _ (Or.inl rfl)).trans
  apply (congrFun (sum_stages_preserves p ops input row warp 0 4 (expScalarWave ops input row warp s)).1 _).trans
  exact exp_scalar_fold_reads p ops input row (cohortThreads row warp 64) s reads offset hb

theorem sum_last_wave_partial_frame (p : Shape) (ops : Ops α) (row warp : Nat)
    (values : Nat → α) (s : State α) (l : Location)
    (hp : ∀ t ∈ cohortThreads row warp 64, ¬ SumPartialWrites t l) :
    (sumLastWave p ops row warp values s).memory l=s.memory l :=
  sum_last_fold_memory_other ops (sumWaveLeft p values) (sumWaveRight p values) (cohortThreads row warp 64)
    (LarkCollective.shuffleUpdates 9 (sumXorSnapshot p row warp 64 1 values) s) l hp

theorem exp_wave_shared_frame (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp : Nat) (s : State α) (l : Location) (hl : l.space=.shared)
    (hp : ∀ t ∈ cohortThreads row warp 64, ¬ SumPartialWrites t l) :
    (expWave p ops input row warp s).memory l=s.memory l :=
  (sum_last_wave_partial_frame p ops row warp (sumWaveValues ops input row warp 4)
    (sumStages p ops input row warp 0 4 (expScalarWave ops input row warp s)) l hp).trans
    ((congrFun (sum_stages_preserves p ops input row warp 0 4 (expScalarWave ops input row warp s)).1 l).trans
      (exp_scalar_fold_shared ops input row (cohortThreads row warp 64) s l hl))

theorem exp_wave_maximum_frame (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp : Nat) (s : State α) :
    (expWave p ops input row warp s).memory ⟨.shared,row,0,0⟩=s.memory ⟨.shared,row,0,0⟩ := by
  apply exp_wave_shared_frame p ops input row warp s _ rfl
  intro t ht hp
  have h := congrArg Location.buffer hp.2
  change 0=1 at h
  cases h

theorem exp_wave_partial_other (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp t : Nat) (s : State α) (l : Location)
    (ht : t ∉ cohortThreads row warp 64) (hp : SumPartialWrites t l) :
    (expWave p ops input row warp s).memory l=s.memory l := by
  apply exp_wave_shared_frame p ops input row warp s l
  · rewrite [hp.2]; rfl
  · intro u hu hpu
    have he := sum_partial_writes_unique t u l hp hpu
    exact ht (he ▸ hu)

theorem exp_wave_native (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp u : Nat) (s : State α) (hw : warp<16) (hi : MaxNativeIndices u s) :
    MaxNativeIndices u (expWave p ops input row warp s) := by
  have h := exp_scalar_fold_native ops input row (cohortThreads row warp 64) s u (exp_cohort_row row warp hw) hi
  simpa only [MaxNativeIndices,exp_wave_indices_eq] using h

#print axioms sum_xor_step_other
#print axioms sum_stages_other
#print axioms sum_last_wave_other
#print axioms exp_wave_indices_eq
#print axioms exp_wave_other
#print axioms exp_scalar_fold_reads
#print axioms exp_scalar_fold_shared
#print axioms exp_wave_reads
#print axioms sum_last_wave_partial_frame
#print axioms exp_wave_shared_frame
#print axioms exp_wave_maximum_frame
#print axioms exp_wave_partial_other
#print axioms exp_wave_native
end LarkNativeSoftmax
