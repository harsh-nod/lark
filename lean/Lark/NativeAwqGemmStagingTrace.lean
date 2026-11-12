import Lark.NativeAwqGemmStagingLaneTrace

/-! All source staging events are classified at an odd block epoch. The
actual middle-barrier resumption changes every participating lane to even. -/
namespace LarkNativeAwqGemm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option autoImplicit false
variable {α : Type}
attribute [local irreducible] aStageState bStageState stagingState stagingFold

def BlockParity (p : Shape) (b parity : Nat) (s : State α) : Prop :=
  ∀ t∈blockThreads (geometry p) b, (s.epochs t).block%2=parity

theorem staging_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (tile t : Nat) (s : State α)
    (good : GoodTrace p s) (odd : (s.epochs t).block%2=1) : GoodTrace p (stagingState p ops input tile t s) := by
  unfold stagingState
  exact b_stage_good p input tile t _ (a_stage_good p ops input tile t s good odd)
    (by rw [(a_stage_frames p ops input tile t s).2]; exact odd)

theorem staging_fold_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile : Nat) (ts : List Nat) (s : State α) (good : GoodTrace p s)
    (odd : ∀ t∈ts, (s.epochs t).block%2=1) : GoodTrace p (stagingFold p ops input tile ts s) := by
  induction ts generalizing s with
  | nil => simpa only [stagingFold,List.foldl_nil] using good
  | cons t ts ih =>
    have next := staging_good p ops input tile t s good (odd t (by simp))
    have rest := ih (stagingState p ops input tile t s) next
      (fun u hu => by rw [(staging_frames p ops input tile t s).2]; exact odd u (List.mem_cons_of_mem t hu))
    simpa only [stagingFold,List.foldl_cons] using rest

theorem after_middle_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b : Nat) (s : State α) (good : GoodTrace p s) (odd : BlockParity p b 1 s) :
    GoodTrace p (afterMiddleBarrier p ops input tile b s) :=
  staging_fold_good p ops input tile _ s good odd

theorem resume_epoch_block (p : Shape) (b t : Nat) (s : State α) (ht : t∈blockThreads (geometry p) b) :
    ((resume (blockThreads (geometry p) b) .block s).epochs t).block=(s.epochs t).block+1 := by
  simp only [resume,List.contains_iff_mem.mpr ht,ite_true,bumpEpoch]

theorem resume_epoch_other (p : Shape) (b t : Nat) (s : State α) (ht : t∉blockThreads (geometry p) b) :
    (resume (blockThreads (geometry p) b) .block s).epochs t=s.epochs t := by
  have outside : ¬(blockThreads (geometry p) b).contains t=true := by simpa only [List.contains_iff_mem] using ht
  simp only [resume,if_neg outside]

theorem after_middle_even (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b : Nat) (s : State α) (odd : BlockParity p b 1 s) :
    BlockParity p b 0 (afterMiddleBarrier p ops input tile b s) := by
  intro t ht
  rw [(after_middle_frames p ops input tile b s).2,resume_epoch_block p b t s ht]
  have h := odd t ht
  omega

theorem after_middle_epoch_other (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b t : Nat) (s : State α) (ht : t∉blockThreads (geometry p) b) :
    (afterMiddleBarrier p ops input tile b s).epochs t=s.epochs t := by
  rw [(after_middle_frames p ops input tile b s).2,resume_epoch_other p b t s ht]

#print axioms staging_good
#print axioms staging_fold_good
#print axioms after_middle_good
#print axioms resume_epoch_block
#print axioms resume_epoch_other
#print axioms after_middle_even
#print axioms after_middle_epoch_other
end LarkNativeAwqGemm
