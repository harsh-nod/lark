import Lark.NativeSglangRmsNormPartialFold

/-! The actual native runner returns a nonempty store cohort at the first
block barrier. Reaching the barrier does not resume it or change any epoch.
-/
namespace LarkNativeSglangRmsNorm
open LarkNonlinear LarkCollective
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
attribute [local irreducible] partialFold

theorem first_barrier_code (repaired : Bool) :
    (program repaired)[firstBarrier repaired]?=some (.scalar (.barrier .block)) := by
  cases repaired <;> decide

theorem barrier_next_none (repaired : Bool) (ts : List Nat) (s : State α)
    (hp : ∀ t∈ts,s.pc t=firstBarrier repaired) :
    LarkPartitionCollective.nextCohort (program repaired) ts s=none := by
  have hf : ts.filter (LarkPartitionCollective.isShuffle (program repaired) s)=[] := by
    apply List.filter_eq_nil_iff.mpr
    intro t ht
    simp [LarkPartitionCollective.isShuffle,hp t ht,first_barrier_code]
  unfold LarkPartitionCollective.nextCohort
  rw [hf]
  rfl

theorem barrier_converged (repaired : Bool) (ts : List Nat) (s : State α)
    (hn : ts≠[]) (hp : ∀ t∈ts,s.pc t=firstBarrier repaired) :
    LarkCollective.converged (program repaired) ts s=some .block := by
  cases ts with
  | nil => exact False.elim (hn rfl)
  | cons t ts =>
      have hp0 := hp t (by simp)
      have hall : (t::ts).all (fun u => s.pc u==firstBarrier repaired)=true := by
        apply List.all_eq_true.mpr
        intro u hu
        simp only [hp u hu,hp0,beq_self_eq_true]
      simp only [LarkCollective.converged,List.head?_cons,bind,Option.some_bind,hall,↓reduceIte,
        LarkCollective.parked,hp0,first_barrier_code,scalarCut]

theorem native_partial_cohort (p : Shape) (repaired : Bool) (ops : Ops α) (a b : Nat → α)
    (row warp n : Nat) (s : State α)
    (hi : ∀ t∈cohortThreads row warp 64,NativeIndices t s)
    (hp : ∀ t∈cohortThreads row warp 64,s.pc t=53)
    (ha : ∀ t∈cohortThreads row warp 64,s.regs t 0=some (a t))
    (hb : ∀ t∈cohortThreads row warp 64,s.regs t 1=some (b t)) :
    LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel (program repaired)
      (cohortThreads row warp 64) (n+1) s =
      some (partialFold repaired ops a b (cohortThreads row warp 64) s) := by
  rw [run_warp_continue,partial_fold_run p repaired ops a b _ s (cohort_nodup row warp 64) hi hp ha hb]
  simp only [Option.some_bind]
  have hn : cohortThreads row warp 64≠[] := by
    intro he
    have h := cohort_head row warp 64 (by decide)
    rw [he] at h
    cases h
  have hpc := fun t ht => (partial_fold_member repaired ops a b (cohortThreads row warp 64) s
    (cohort_nodup row warp 64) t ht).1
  unfold continueCohort
  rw [barrier_next_none repaired _ _ hpc]
  rw [barrier_converged repaired _ _ hn hpc]
  rfl

#print axioms first_barrier_code
#print axioms barrier_next_none
#print axioms barrier_converged
#print axioms native_partial_cohort
end LarkNativeSglangRmsNorm
