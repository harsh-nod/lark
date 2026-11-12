import Lark.NativeSglangRmsNormWaveSecondState
import Lark.NativeSglangRmsNormInactiveWaves

/-! Actual second-phase block execution. Wave0 reduces and stores inverses;
the other15 waves skip without shared reads. All1024 threads converge at PC76,
and the unchanged native block runner resumes that barrier to PC77.
-/
namespace LarkNativeSglangRmsNorm
open LarkNonlinear LarkCollective
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
attribute [local irreducible] prefixFold reductionSnapshot partialFold firstBlockFold secondFold regAddFold inverseFold secondSnapshot skipFold inactiveWaves

def remainingWaves : List Nat := (List.range 15).map (fun n => n+1)

theorem block_waves_split : List.range 16=0::remainingWaves := by decide

theorem remaining_waves_nodup : remainingWaves.Nodup := by
  exact (List.nodup_cons.mp (block_waves_split ▸ List.nodup_range)).2

theorem remaining_waves_bounds (w : Nat) : w∈remainingWaves ↔ 0<w ∧ w<16 := by
  simp only [remainingWaves,List.mem_map,List.mem_range]
  constructor
  · rintro ⟨n,hn,rfl⟩; omega
  · rintro ⟨hpos,hw⟩
    exact ⟨w-1,by omega,by omega⟩

def secondBlock (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row : Nat) (s : State α) : State α :=
  inactiveWaves row remainingWaves (waveSecond p ops input row s)

theorem native_second_block_waves (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) (reads : Reads p input s) :
    (List.range 16).foldlM
      (fun u w => LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel (program true)
        (warpThreads (geometry p) row w) fuel.warp u) (resumedFirstBlock p ops input row s)=
      some (secondBlock p ops input row (resumedFirstBlock p ops input row s)) := by
  have first : LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel (program true)
      (warpThreads (geometry p) row 0) fuel.warp (resumedFirstBlock p ops input row s)=
      some (waveSecond p ops input row (resumedFirstBlock p ops input row s)) :=
    native_second_wave p ops input row 2 s reads
  rw [block_waves_split,List.foldlM_cons,first]
  apply inactive_waves_run p ops row remainingWaves _ remaining_waves_nodup
  · intro w hw; exact (remaining_waves_bounds w).mp hw
  · intro w hw t ht
    unfold NativeIndices
    rw [(wave_second_indices_epochs p ops input row _).1]
    exact resumed_first_block_indices p ops input row t s reads
      (cohort_in_block p row w t ((remaining_waves_bounds w).mp hw).2 ht)
  · intro w hw t ht
    have hne : w≠0 := by have h := ((remaining_waves_bounds w).mp hw).1; omega
    rw [(wave_second_other p ops input row t _ (distinct_cohorts row w 0 t hne ht)).1]
    exact resumed_first_block_pc p ops input row t s
      (cohort_in_block p row w t ((remaining_waves_bounds w).mp hw).2 ht)

theorem second_block_wave_pc (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row w lane : Nat) (s : State α) (hw : w<16) (hl : lane<64) :
    (secondBlock p ops input row s).pc (cohortBase row w+lane)=76 := by
  by_cases hzero : w=0
  · subst w
    have outside : ∀ v∈remainingWaves,cohortBase row 0+lane∉cohortThreads row v 64 := by
      intro v hv
      apply distinct_cohorts row 0 v _ _ ((cohort_mem row 0 64 _).mpr ⟨lane,hl,rfl⟩)
      have h := ((remaining_waves_bounds v).mp hv).1
      omega
    exact (inactive_waves_other row remainingWaves _ (waveSecond p ops input row s) outside).trans
      (wave_second_all_pc p ops input row s _ ((cohort_mem row 0 64 _).mpr ⟨lane,hl,rfl⟩))
  · exact inactive_waves_member_pc row remainingWaves _ remaining_waves_nodup w lane
      ((remaining_waves_bounds w).mpr ⟨by omega,hw⟩) hl

theorem second_block_all_pc (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) :
    ∀ t∈blockThreads (geometry p) row,(secondBlock p ops input row s).pc t=76 := by
  intro t ht
  obtain ⟨tid,htid,rfl⟩ := List.mem_map.mp ht
  have htid : tid<1024 := List.mem_range.mp htid
  have he : row*1024+tid=cohortBase row (tid/64)+tid%64 := by unfold cohortBase; omega
  change (secondBlock p ops input row s).pc (row*1024+tid)=_
  rw [he]
  exact second_block_wave_pc p ops input row (tid/64) (tid%64) s (by omega) (by omega)

def resumedSecondBlock (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row : Nat) (s : State α) : State α :=
  resume (blockThreads (geometry p) row) .block (secondBlock p ops input row s)

theorem native_second_block_step (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row n : Nat) (s : State α) (reads : Reads p input s) :
    LarkPartitionCollective.runBlock ops (layout p) (geometry p) fuel (program true) row (n+1)
      (resumedFirstBlock p ops input row s)=
    LarkPartitionCollective.runBlock ops (layout p) (geometry p) fuel (program true) row n
      (resumedSecondBlock p ops input row (resumedFirstBlock p ops input row s)) := by
  have hrun := native_second_block_waves p ops input row s reads
  have hn : blockThreads (geometry p) row≠[] := by
    intro he
    have hm : row*1024∈blockThreads (geometry p) row := by
      apply List.mem_map.mpr
      exact ⟨0,List.mem_range.mpr (by change 0<1024; decide),by simp [geometry]⟩
    rw [he] at hm
    cases hm
  have hc := second_barrier_converged (blockThreads (geometry p) row)
    (secondBlock p ops input row (resumedFirstBlock p ops input row s)) hn
    (second_block_all_pc p ops input row (resumedFirstBlock p ops input row s))
  have count : ((geometry p).block+(geometry p).warp-1)/(geometry p).warp=16 := by
    change (1024+64-1)/64=16
    decide
  rw [LarkPartitionCollective.runBlock,count,hrun]
  simp only [bind,Option.some_bind]
  rw [hc]
  rfl

theorem initial_two_block_steps (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row : Nat) (hr : row<p.rows) :
    LarkPartitionCollective.runBlock ops (layout p) (geometry p) fuel (program true) row fuel.block
      (initial p input outside)=
    LarkPartitionCollective.runBlock ops (layout p) (geometry p) fuel (program true) row 1
      (resumedSecondBlock p ops input row (resumedFirstBlock p ops input row (initial p input outside))) := by
  rw [initial_first_block_step p ops input outside row hr,native_second_block_step p ops input row 1 _
    (initial_reads p input outside)]

theorem resumed_second_block_pc (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row t : Nat) (s : State α) (ht : t∈blockThreads (geometry p) row) :
    (resumedSecondBlock p ops input row s).pc t=77 := by
  have hc := List.contains_iff_mem.mpr ht
  simp only [resumedSecondBlock,resume,hc,↓reduceIte,second_block_all_pc p ops input row s t ht]

theorem second_block_indices_epochs (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) :
    (secondBlock p ops input row s).indices=s.indices ∧ (secondBlock p ops input row s).epochs=s.epochs := by
  have h := inactive_waves_preserves row remainingWaves (waveSecond p ops input row s)
  have hs := wave_second_indices_epochs p ops input row s
  exact ⟨h.2.1.trans hs.1,h.2.2.2.1.trans hs.2⟩

theorem resumed_second_block_epochs (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row t : Nat) (s : State α) (ht : t∈blockThreads (geometry p) row) :
    ((resumedSecondBlock p ops input row s).epochs t).block=(s.epochs t).block+1 ∧
    ((resumedSecondBlock p ops input row s).epochs t).warp=(s.epochs t).warp ∧
    ((resumedSecondBlock p ops input row s).epochs t).grid=(s.epochs t).grid := by
  have hc := List.contains_iff_mem.mpr ht
  simp only [resumedSecondBlock,resume,hc,↓reduceIte,second_block_indices_epochs,bumpEpoch,and_self]

#print axioms block_waves_split
#print axioms remaining_waves_nodup
#print axioms remaining_waves_bounds
#print axioms native_second_block_waves
#print axioms second_block_wave_pc
#print axioms second_block_all_pc
#print axioms native_second_block_step
#print axioms initial_two_block_steps
#print axioms resumed_second_block_pc
#print axioms second_block_indices_epochs
#print axioms resumed_second_block_epochs
end LarkNativeSglangRmsNorm
