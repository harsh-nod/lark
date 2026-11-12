import Lark.NativeSglangRmsNormReductionEntry
import Lark.NativeSglangRmsNormPartialBarrier

/-! Complete initialized physical-wave execution through all five logical32
XOR/add rounds and the shared partial stores, parked at the first block
barrier. This does not resume that barrier or claim whole-block completion.
-/
namespace LarkNativeSglangRmsNorm
open LarkNonlinear LarkCollective
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
attribute [local irreducible] prefixFold reductionSnapshot partialFold

def wavePartialA (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row warp : Nat) : Nat → α :=
  fun t => reductionValues ops (waveBaseValues ops input row warp) 4
    (LarkPartitionCollective.nativeLane (geometry p) t)
def wavePartialB (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row warp : Nat) : Nat → α :=
  fun t => reductionValues ops (waveBaseValues ops input row warp) 4
    (xorPeer32 (LarkPartitionCollective.nativeLane (geometry p) t) 1)

def wavePartial (p : Shape) (repaired : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row warp : Nat) (s : State α) : State α :=
  partialFold repaired ops (wavePartialA p ops input row warp) (wavePartialB p ops input row warp)
    (cohortThreads row warp 64) (waveLastSnapshot p ops input row warp s)

theorem native_wave_partial (p : Shape) (repaired : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row warp : Nat) (s : State α) (hr : row<p.rows) (hw : warp<16)
    (hp : ∀ t∈cohortThreads row warp 64,s.pc t=0) (reads : Reads p input s) :
    LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel (program repaired)
      (warpThreads (geometry p) row warp) fuel.warp s = some (wavePartial p repaired ops input row warp s) := by
  rw [wave_last_snapshot_native p repaired ops input row warp s hr hw hp reads]
  apply native_partial_cohort p repaired ops _ _ row warp 2
  · intro t ht
    obtain ⟨lane,hl,rfl⟩ := (cohort_mem row warp 64 t).mp ht
    exact wave_last_snapshot_indices p ops input row warp lane s hl reads
  · intro t ht
    obtain ⟨lane,hl,rfl⟩ := (cohort_mem row warp 64 t).mp ht
    exact (wave_last_snapshot_fields p ops input row warp lane s hw hl reads).1
  · intro t ht
    obtain ⟨lane,hl,rfl⟩ := (cohort_mem row warp 64 t).mp ht
    simpa only [wavePartialA,(cohort_coords p row warp lane hw hl).2] using
      (wave_last_snapshot_fields p ops input row warp lane s hw hl reads).2.1
  · intro t ht
    obtain ⟨lane,hl,rfl⟩ := (cohort_mem row warp 64 t).mp ht
    simpa only [wavePartialB,(cohort_coords p row warp lane hw hl).2] using
      (wave_last_snapshot_fields p ops input row warp lane s hw hl reads).2.2

theorem initial_native_wave_partial (p : Shape) (repaired : Bool) (ops : Ops α)
    (input : Nat → Nat → α) (outside : Location → Option α) (row warp : Nat)
    (hr : row<p.rows) (hw : warp<16) :
    LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel (program repaired)
      (warpThreads (geometry p) row warp) fuel.warp (initial p input outside) =
      some (wavePartial p repaired ops input row warp (initial p input outside)) :=
  native_wave_partial p repaired ops input row warp _ hr hw (by intro t ht; rfl)
    (initial_reads p input outside)

theorem wave_partial_fields (p : Shape) (repaired : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row warp lane : Nat) (s : State α) (hw : warp<16) (hl : lane<64) :
    (wavePartial p repaired ops input row warp s).pc (cohortBase row warp+lane)=firstBarrier repaired ∧
    (wavePartial p repaired ops input row warp s).regs (cohortBase row warp+lane) 0=
      some (reductionValues ops (waveBaseValues ops input row warp) 5 lane) := by
  have h := partial_fold_member repaired ops (wavePartialA p ops input row warp)
    (wavePartialB p ops input row warp) (cohortThreads row warp 64)
    (waveLastSnapshot p ops input row warp s) (cohort_nodup row warp 64) _
    ((cohort_mem row warp 64 _).mpr ⟨lane,hl,rfl⟩)
  simpa only [wavePartialA,wavePartialB,(cohort_coords p row warp lane hw hl).2,reductionValues,reductionMask] using h

theorem wave_partial_indices_epochs (p : Shape) (repaired : Bool) (ops : Ops α)
    (input : Nat → Nat → α) (row warp : Nat) (s : State α) :
    (wavePartial p repaired ops input row warp s).indices=(wavePrepared ops input row warp s).indices ∧
    (wavePartial p repaired ops input row warp s).epochs=s.epochs := by
  have h := partial_fold_indices_epochs repaired ops (wavePartialA p ops input row warp)
    (wavePartialB p ops input row warp) (cohortThreads row warp 64) (waveLastSnapshot p ops input row warp s)
  have hs := wave_last_snapshot_preserves p ops input row warp s
  exact ⟨h.1.trans hs.2.1,h.2.trans hs.2.2.1⟩

theorem wave_partial_native_indices (p : Shape) (repaired : Bool) (ops : Ops α)
    (input : Nat → Nat → α) (row warp lane : Nat) (s : State α) (hl : lane<64) (reads : Reads p input s) :
    NativeIndices (cohortBase row warp+lane) (wavePartial p repaired ops input row warp s) := by
  unfold NativeIndices
  rw [(wave_partial_indices_epochs p repaired ops input row warp s).1]
  exact (wave_prepared_ready p ops input row warp lane s reads hl).indices

theorem wave_partial_caches (p : Shape) (repaired : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row warp lane : Nat) (s : State α) (hw : warp<16) (hl : lane<64) (reads : Reads p input s) :
    let t := cohortBase row warp+lane
    InputPrefix input row (warp*64+lane) 16 t (wavePartial p repaired ops input row warp s) ∧
    WeightPrefix input (warp*64+lane) 16 t (wavePartial p repaired ops input row warp s) := by
  have caches := wave_last_snapshot_caches p ops input row warp lane s hw hl reads
  exact partial_fold_caches repaired ops _ _ _ _ input row (warp*64+lane) _ caches.1 caches.2

theorem wave_partial_reads (p : Shape) (repaired : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row warp : Nat) (s : State α) (reads : Reads p input s) :
    Reads p input (wavePartial p repaired ops input row warp s) :=
  partial_fold_reads p repaired ops _ _ _ _ (wave_last_snapshot_reads p ops input row warp s reads)

theorem wave_partial_trace (p : Shape) (repaired : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row warp : Nat) (s : State α) :
    (wavePartial p repaired ops input row warp s).trace=
      partialEvents repaired s.epochs (cohortThreads row warp 64) ++ (wavePrepared ops input row warp s).trace := by
  change (partialFold repaired ops _ _ _ _).trace=_
  rw [partial_fold_trace,(wave_last_snapshot_preserves p ops input row warp s).2.2.1,
    (wave_last_snapshot_preserves p ops input row warp s).2.2.2]

theorem wave_partial_trace_tail (p : Shape) (repaired : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row warp : Nat) (s : State α) (reads : Reads p input s) :
    ∃ events, (wavePartial p repaired ops input row warp s).trace=
      partialEvents repaired s.epochs (cohortThreads row warp 64) ++ events ++ s.trace ∧
      events.length=5120 ∧ (∀ event∈events,Good event) := by
  obtain ⟨events,he,hl,hg⟩ := prefix_fold_trace_tail p ops input (cohortThreads row warp 64) s reads
  refine ⟨events,?_,?_,hg⟩
  · rw [wave_partial_trace]
    change _ ++ (prefixFold ops input _ s).trace=_
    rw [he,List.append_assoc]
  · simpa only [cohortThreads,List.length_map,List.length_range] using hl

theorem wave_partial_other (p : Shape) (repaired : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row warp t : Nat) (s : State α) (ht : t∉cohortThreads row warp 64) :
    (wavePartial p repaired ops input row warp s).pc t=s.pc t ∧
    (wavePartial p repaired ops input row warp s).indices t=s.indices t ∧
    (wavePartial p repaired ops input row warp s).regs t=s.regs t := by
  have hp := partial_fold_other repaired ops (wavePartialA p ops input row warp) (wavePartialB p ops input row warp)
    (cohortThreads row warp 64) t (waveLastSnapshot p ops input row warp s) ht
  have hs := reduction_snapshot_other p ops row warp 4 t (waveBaseValues ops input row warp)
    (wavePrepared ops input row warp s) ht
  have hf := prefix_fold_other ops input (cohortThreads row warp 64) t s ht
  exact ⟨hp.1.trans (hs.1.trans hf.1),
    (congrFun (wave_partial_indices_epochs p repaired ops input row warp s).1 t).trans hf.2.1,
    hp.2.trans (hs.2.trans hf.2.2)⟩

theorem wave_partial_memory (p : Shape) (repaired : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row warp : Nat) (s : State α) (l : Location)
    (privateOutside : ∀ t∈cohortThreads row warp 64,OutsidePrivate t l)
    (sharedOutside : ∀ t∈cohortThreads row warp 64,l≠partialSlot t ((t%1024)/32)) :
    (wavePartial p repaired ops input row warp s).memory l=s.memory l := by
  change (partialFold repaired ops _ _ _ _).memory l=_
  rw [partial_fold_memory repaired ops _ _ _ _ l sharedOutside,
    (wave_last_snapshot_preserves p ops input row warp s).1]
  exact prefix_fold_memory ops input _ s l privateOutside

theorem initial_fixed_wave_partial_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row warp : Nat) :
    ∀ event∈(wavePartial p true ops input row warp (initial p input outside)).trace,Good event := by
  apply fixed_partial_fold_good ops _ _ _ _
  · intro t ht
    rw [(wave_last_snapshot_preserves p ops input row warp _).2.2.1]
    rfl
  · obtain ⟨events,he,hl,hg⟩ := wave_last_snapshot_trace_tail p ops input row warp
      (initial p input outside) (initial_reads p input outside)
    rw [he]
    simpa only [initial,LarkNonlinear.initial,List.append_nil] using hg

theorem initial_fixed_wave_partial_race_free (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row warp : Nat) :
    raceFree (geometry p) (wavePartial p true ops input row warp (initial p input outside)).trace=true :=
  race_free p _ (initial_fixed_wave_partial_good p ops input outside row warp)

#print axioms native_wave_partial
#print axioms initial_native_wave_partial
#print axioms wave_partial_fields
#print axioms wave_partial_indices_epochs
#print axioms wave_partial_native_indices
#print axioms wave_partial_caches
#print axioms wave_partial_reads
#print axioms wave_partial_trace
#print axioms wave_partial_trace_tail
#print axioms wave_partial_other
#print axioms wave_partial_memory
#print axioms initial_fixed_wave_partial_good
#print axioms initial_fixed_wave_partial_race_free
end LarkNativeSglangRmsNorm
