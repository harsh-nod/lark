import Lark.NativeQKNormRopeStores

/-! Actual partition scheduler convergence at either native source halt. -/
namespace LarkNativeQKNormRope
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem final_source_halt (neox : Bool) :
    (program neox)[storeStart neox + 8]? = some (.scalar .halt) := by cases neox <;> decide

theorem cohort_final_halt (neox : Bool) (block warp active : Nat) (s : State α) (hpos : 0 < active)
    (hp : ∀ lane, lane < active → s.pc (cohortBase block warp + lane) = storeStart neox + 8) :
    LarkPartitionCollective.nextCohort (program neox) (cohortThreads block warp active) s = none ∧
    LarkCollective.converged (program neox) (cohortThreads block warp active) s = some .halt := by
  have hp0 : s.pc (cohortBase block warp) = storeStart neox + 8 := by simpa only [Nat.add_zero] using hp 0 hpos
  have hf : (cohortThreads block warp active).filter (LarkPartitionCollective.isShuffle (program neox) s) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro t ht
    obtain ⟨lane, hl, rfl⟩ := (cohort_mem block warp active t).mp ht
    simp only [LarkPartitionCollective.isShuffle, hp lane hl, final_source_halt]
    decide
  have ha : (cohortThreads block warp active).all (fun t => s.pc t == s.pc (cohortBase block warp)) = true := by
    apply List.all_eq_true.mpr
    intro t ht
    obtain ⟨lane, hl, rfl⟩ := (cohort_mem block warp active t).mp ht
    simp [hp lane hl, hp0]
  constructor
  · simp only [LarkPartitionCollective.nextCohort, hf, List.head?_nil, bind, Option.bind]
  · unfold LarkCollective.converged
    rewrite [cohort_head block warp active hpos]
    simp only [bind, pure, Option.bind, ha, ↓reduceIte]
    unfold LarkCollective.parked
    rewrite [hp0, final_source_halt]
    rfl

theorem continue_at_final_halt (p : Shape) (neox : Bool) (ops : Ops α) (block warp active n : Nat)
    (s : State α) (hpos : 0 < active)
    (hp : ∀ lane, lane < active → s.pc (cohortBase block warp + lane) = storeStart neox + 8) :
    continueCohort p neox ops (cohortThreads block warp active) n s = some s := by
  obtain ⟨hc, hh⟩ := cohort_final_halt neox block warp active s hpos hp
  simp only [continueCohort, hc, hh, bind, pure, Option.some_bind, reduceCtorEq, ↓reduceIte]

#print axioms final_source_halt
#print axioms cohort_final_halt
#print axioms continue_at_final_halt
end LarkNativeQKNormRope
