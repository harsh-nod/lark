import Lark.NativeSglangRmsNormWavePartial

/-! An actual initialized original-source wave reaches conflicting shared
writes. These events are taken from the native execution result, not an
assumed store cut state. Coincident stored values do not remove the accesses.
-/
namespace LarkNativeSglangRmsNorm
open LarkNonlinear LarkCollective
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
attribute [local irreducible] prefixFold reductionSnapshot partialFold

def originalWaveAccess (row warp lane : Nat) : Access :=
  let t := cohortBase row warp+lane
  ⟨t,partialSlot t ((t%1024)/32),true,{}⟩

theorem original_wave_access_member (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row warp lane : Nat) (hl : lane<64) :
    originalWaveAccess row warp lane∈
      (wavePartial p false ops input row warp (initial p input outside)).trace := by
  rw [wave_partial_trace]
  apply List.mem_append_left
  exact original_partial_events_member (initial p input outside).epochs (cohortThreads row warp 64) _
    ((cohort_mem row warp 64 _).mpr ⟨lane,hl,rfl⟩)

theorem original_wave_pair_conflict (p : Shape) (row warp : Nat) (hw : warp<16) :
    conflict (geometry p) (originalWaveAccess row warp 0) (originalWaveAccess row warp 1)=true := by
  have h0 := cohort_arithmetic row warp 0 hw (by decide)
  have h1 := cohort_arithmetic row warp 1 hw (by decide)
  have r0 : cohortBase row warp/1024=row := by simpa only [Nat.add_zero] using h0.1
  have d0 : (cohortBase row warp%1024)/32=warp*2 := by omega
  have d1 : ((cohortBase row warp+1)%1024)/32=warp*2 := by omega
  have hne : cohortBase row warp≠cohortBase row warp+1 := by omega
  simp [originalWaveAccess,conflict,ordered,sameLocation,partialSlot,geometry,
    r0,h1.1,d0,d1,hne]

theorem conflicting_trace_members (g : Geometry) (trace : List Access) (a b : Access)
    (ha : a∈trace) (hb : b∈trace) (hc : conflict g a b=true) : raceFree g trace=false := by
  apply List.all_eq_false.mpr
  refine ⟨a,ha,?_⟩
  intro hall
  have hp := List.all_eq_true.mp hall b hb
  rw [hc] at hp
  cases hp

theorem initial_original_wave_partial_racy (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row warp : Nat) (hw : warp<16) :
    raceFree (geometry p) (wavePartial p false ops input row warp (initial p input outside)).trace=false :=
  conflicting_trace_members (geometry p) _ _ _
    (original_wave_access_member p ops input outside row warp 0 (by decide))
    (original_wave_access_member p ops input outside row warp 1 (by decide))
    (original_wave_pair_conflict p row warp hw)

theorem initial_original_racy_native_wave (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row warp : Nat) (hr : row<p.rows) (hw : warp<16) :
    ∃ final, LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel (program false)
      (warpThreads (geometry p) row warp) fuel.warp (initial p input outside)=some final ∧
      raceFree (geometry p) final.trace=false :=
  ⟨wavePartial p false ops input row warp (initial p input outside),
    initial_native_wave_partial p false ops input outside row warp hr hw,
    initial_original_wave_partial_racy p ops input outside row warp hw⟩

#print axioms original_wave_access_member
#print axioms original_wave_pair_conflict
#print axioms conflicting_trace_members
#print axioms initial_original_wave_partial_racy
#print axioms initial_original_racy_native_wave
end LarkNativeSglangRmsNorm
