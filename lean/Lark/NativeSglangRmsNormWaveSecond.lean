import Lark.NativeSglangRmsNormInverseFold

/-! Successful actual native wave64 execution of the guarded second reduction
from the reached first-block resumption. It returns at the second block barrier
without resuming that barrier or executing any output loop.
-/
namespace LarkNativeSglangRmsNorm
open LarkNonlinear LarkCollective
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
attribute [local irreducible] prefixFold reductionSnapshot partialFold firstBlockFold secondFold regAddFold inverseFold secondSnapshot

theorem second_barrier_next_none (ts : List Nat) (s : State α) (hp : ∀ t∈ts,s.pc t=76) :
    LarkPartitionCollective.nextCohort (program true) ts s=none := by
  have code : (program true)[76]?=some (.scalar (.barrier .block)) := by decide
  have hf : ts.filter (LarkPartitionCollective.isShuffle (program true) s)=[] := by
    apply List.filter_eq_nil_iff.mpr
    intro t ht
    simp only [LarkPartitionCollective.isShuffle,hp t ht,code,Bool.false_eq_true,not_false_eq_true]
  unfold LarkPartitionCollective.nextCohort
  rw [hf]
  rfl

theorem second_barrier_converged (ts : List Nat) (s : State α) (hn : ts≠[])
    (hp : ∀ t∈ts,s.pc t=76) :
    LarkCollective.converged (program true) ts s=some .block := by
  have code : (program true)[76]?=some (.scalar (.barrier .block)) := by decide
  cases ts with
  | nil => exact False.elim (hn rfl)
  | cons t ts =>
      have hp0 := hp t (by simp)
      have hall : (t::ts).all (fun u => s.pc u==76)=true := by
        apply List.all_eq_true.mpr
        intro u hu
        simp only [hp u hu,beq_self_eq_true]
      simp only [LarkCollective.converged,List.head?_cons,bind,Option.some_bind,
        LarkCollective.parked,hp0,hall,↓reduceIte,code,scalarCut]

theorem inverse_full_pc (ops : Ops α) (a b : Nat → α) (row : Nat) (s : State α)
    (inactive : ∀ lane,lane<32 → s.pc (cohortBase row 0+32+lane)=76) :
    ∀ t∈cohortThreads row 0 64,
      (inverseFold ops a b (cohortThreads row 0 32) s).pc t=76 := by
  intro t ht
  obtain ⟨lane,hl,rfl⟩ := (cohort_mem row 0 64 t).mp ht
  by_cases ha : lane<32
  · exact (inverse_fold_member ops a b _ s (cohort_nodup row 0 32)
      _ ((cohort_mem row 0 32 _).mpr ⟨lane,ha,rfl⟩)).1
  · have hn : cohortBase row 0+lane∉cohortThreads row 0 32 := by
      intro hm
      obtain ⟨l,hll,he⟩ := (cohort_mem row 0 32 _).mp hm
      omega
    have he : cohortBase row 0+lane=cohortBase row 0+32+(lane-32) := by omega
    exact (inverse_fold_other ops a b _ _ s hn).1.trans (he ▸ inactive (lane-32) (by omega))

theorem native_second_inverse_cohort (p : Shape) (ops : Ops α) (a b : Nat → α)
    (row n : Nat) (s : State α)
    (hi : ∀ t∈cohortThreads row 0 32,s.indices t 1=some ((t%1024 : Nat) : Int))
    (hp : ∀ t∈cohortThreads row 0 32,s.pc t=71)
    (ha : ∀ t∈cohortThreads row 0 32,s.regs t 7=some (a t))
    (hb : ∀ t∈cohortThreads row 0 32,s.regs t 8=some (b t))
    (inactive : ∀ lane,lane<32 → s.pc (cohortBase row 0+32+lane)=76) :
    LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel (program true)
      (cohortThreads row 0 64) (n+1) s=some (inverseFold ops a b (cohortThreads row 0 32) s) := by
  have bound : ∀ t∈cohortThreads row 0 32,t%1024<32 := by
    intro t ht
    obtain ⟨lane,hl,rfl⟩ := (cohort_mem row 0 32 t).mp ht
    rw [(cohort_arithmetic row 0 lane (by decide) (by omega)).2.1]
    omega
  have fold : (cohortThreads row 0 64).foldlM
      (fun u t => LarkCollective.runLane ops (layout p) (geometry p) (program true) t fuel.lane u) s=
      some (inverseFold ops a b (cohortThreads row 0 32) s) := by
    rw [cohort_split,List.foldlM_append,inverse_fold_run p ops a b _ s (cohort_nodup row 0 32) bound hi hp ha hb]
    apply barrier_lane_fold p ops
    intro t ht
    obtain ⟨lane,hl,rfl⟩ := (cohort_upper_mem row 0 t).mp ht
    exact (inverse_fold_other ops a b _ _ s (cohort_upper_excluded row lane)).1.trans (inactive lane hl)
  rw [run_warp_continue,fold]
  simp only [Option.some_bind]
  have hpc := inverse_full_pc ops a b row s inactive
  have hn : cohortThreads row 0 64≠[] := by
    intro he
    have hh := cohort_head row 0 64 (by decide)
    rw [he] at hh
    cases hh
  unfold continueCohort
  rw [second_barrier_next_none _ _ hpc,second_barrier_converged _ _ hn hpc]
  rfl

def waveSecondA (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row t : Nat) : α :=
  reductionValues ops (blockPartialValue ops input row) 4 (LarkPartitionCollective.nativeLane (geometry p) t)
def waveSecondB (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row t : Nat) : α :=
  reductionValues ops (blockPartialValue ops input row) 4
    (xorPeer32 (LarkPartitionCollective.nativeLane (geometry p) t) 1)
def waveSecondSnapshot (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row : Nat) (s : State α) : State α :=
  secondSnapshot p ops row (blockPartialValue ops input row) (secondPrepared ops input row s) 4
def waveSecond (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row : Nat) (s : State α) : State α :=
  inverseFold ops (waveSecondA p ops input row) (waveSecondB p ops input row)
    (cohortThreads row 0 32) (waveSecondSnapshot p ops input row s)

theorem second_snapshot_zero (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row : Nat) (s : State α) :
    secondSnapshot p ops row (blockPartialValue ops input row) (secondPrepared ops input row s) 0=
      secondFirstSnapshot p ops input row s := by rw [secondSnapshot]; rfl

theorem wave_second_snapshot_fields (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row lane : Nat) (s : State α) (hl : lane<32) :
    (waveSecondSnapshot p ops input row s).pc (cohortBase row 0+lane)=71 ∧
    (waveSecondSnapshot p ops input row s).regs (cohortBase row 0+lane) 7=
      some (waveSecondA p ops input row (cohortBase row 0+lane)) ∧
    (waveSecondSnapshot p ops input row s).regs (cohortBase row 0+lane) 8=
      some (waveSecondB p ops input row (cohortBase row 0+lane)) := by
  have h := second_snapshot_fields p ops row 4 lane (blockPartialValue ops input row)
    (secondPrepared ops input row s) hl
    (fun l hll => by simpa only [if_pos hll] using (second_prepared_fields ops input row l s (by omega)).1)
    (fun l hll => (second_prepared_fields ops input row l s (by omega)).2 hll)
  simpa only [waveSecondSnapshot,waveSecondA,waveSecondB,
    (cohort_coords p row 0 lane (by decide) (by omega)).2,reductionMask] using h

theorem wave_second_snapshot_inactive (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row lane : Nat) (s : State α) (hl : lane<32) :
    (waveSecondSnapshot p ops input row s).pc (cohortBase row 0+32+lane)=76 := by
  have h := second_snapshot_other p ops row 4 (cohortBase row 0+32+lane) (blockPartialValue ops input row)
    (secondPrepared ops input row s) (cohort_upper_excluded row lane)
  have hp := (second_prepared_fields ops input row (32+lane) s (by omega)).1
  have hn : ¬32+lane<32 := by omega
  exact h.1.trans (by simpa only [Nat.add_assoc,if_neg hn] using hp)

theorem wave_second_snapshot_indices (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) :
    (waveSecondSnapshot p ops input row s).indices=s.indices :=
  (second_snapshot_preserves p ops row 4 (blockPartialValue ops input row) (secondPrepared ops input row s)).2.1.trans
    (second_fold_preserves ops input (cohortThreads row 0 64) s).2.1

theorem native_second_wave (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row n : Nat)
    (s : State α) (reads : Reads p input s) :
    LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel (program true)
      (warpThreads (geometry p) row 0) (n+6) (resumedFirstBlock p ops input row s)=
      some (waveSecond p ops input row (resumedFirstBlock p ops input row s)) := by
  let carried := resumedFirstBlock p ops input row s
  have hp : ∀ lane,lane<32 → (secondPrepared ops input row carried).pc (cohortBase row 0+lane)=62 := by
    intro lane hl
    simpa only [if_pos hl] using (second_prepared_fields ops input row lane carried (by omega)).1
  have hr := fun lane hl => (second_prepared_fields ops input row lane carried (by omega)).2 hl
  have inactive : ∀ lane,lane<32 → (secondPrepared ops input row carried).pc (cohortBase row 0+32+lane)=76 := by
    intro lane hl
    have hn : ¬32+lane<32 := by omega
    simpa only [Nat.add_assoc,if_neg hn] using (second_prepared_fields ops input row (32+lane) carried (by omega)).1
  rw [native_second_entry p ops input row (n+5) s reads,← second_snapshot_zero]
  rw [show n+5=(n+1)+4 by omega,native_second_four p ops row (n+1) (blockPartialValue ops input row)
    (secondPrepared ops input row carried) hp hr inactive]
  apply native_second_inverse_cohort p ops _ _ row n
  · intro t ht
    change (waveSecondSnapshot p ops input row carried).indices t 1=_
    rw [wave_second_snapshot_indices]
    exact (resumed_first_block_indices p ops input row t s reads
      (cohort_in_block p row 0 t (by decide) (by rw [cohort_split]; exact List.mem_append_left _ ht))).2.1
  · intro t ht
    obtain ⟨lane,hl,rfl⟩ := (cohort_mem row 0 32 t).mp ht
    exact (wave_second_snapshot_fields p ops input row lane carried hl).1
  · intro t ht
    obtain ⟨lane,hl,rfl⟩ := (cohort_mem row 0 32 t).mp ht
    exact (wave_second_snapshot_fields p ops input row lane carried hl).2.1
  · intro t ht
    obtain ⟨lane,hl,rfl⟩ := (cohort_mem row 0 32 t).mp ht
    exact (wave_second_snapshot_fields p ops input row lane carried hl).2.2
  · exact fun lane hl => wave_second_snapshot_inactive p ops input row lane carried hl

#print axioms second_barrier_next_none
#print axioms second_barrier_converged
#print axioms inverse_full_pc
#print axioms native_second_inverse_cohort
#print axioms second_snapshot_zero
#print axioms wave_second_snapshot_fields
#print axioms wave_second_snapshot_inactive
#print axioms wave_second_snapshot_indices
#print axioms native_second_wave
end LarkNativeSglangRmsNorm
