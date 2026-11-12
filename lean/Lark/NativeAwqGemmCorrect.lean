import Lark.NativeAwqGemmBlockTrace

/-! Complete initialized native launch, classification of its actual trace,
race freedom and exact extraction of all source-order output values. The
independent dense exact-real bridge is a separate remaining obligation. -/
namespace LarkNativeAwqGemm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option autoImplicit false
variable {α : Type}
attribute [local irreducible] wholeBlock gridFold wholeGrid

theorem grid_fold_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (bs : List Nat) (s : State α) (good : GoodTrace p s) (even : ∀ t, (s.epochs t).block%2=0) :
    GoodTrace p (gridFold p ops input bs s) ∧ ∀ t, ((gridFold p ops input bs s).epochs t).block%2=0 := by
  induction bs generalizing s with
  | nil => simpa only [gridFold,List.foldl_nil] using And.intro good even
  | cons b bs ih =>
    have next := whole_block_good p ops input b s good (fun t _ => even t)
    have epochs := whole_block_even p ops input b s even
    simpa only [gridFold,List.foldl_cons] using ih (wholeBlock p ops input b s) next epochs

theorem initialized_whole_grid_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) : GoodTrace p (wholeGrid p ops input (initial (layout p) input outside)) := by
  unfold wholeGrid
  exact (grid_fold_good p ops input _ _ (initial_good_trace p input outside) (fun _ => rfl)).1

theorem initialized_whole_grid_race_free (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) :
    raceFree (geometry p) (wholeGrid p ops input (initial (layout p) input outside)).trace=true :=
  good_trace_race_free p _ (initialized_whole_grid_good p ops input outside)

theorem source_correct (p : Shape) (ops : Ops α) :
    LarkMFMA.Correct ops (layout p) (geometry p) (fuel p) (program p) (sourceSpec p ops) := by
  intro input outside
  exact ⟨wholeGrid p ops input (initial (layout p) input outside),whole_launch_run p ops input outside,
    initialized_whole_grid_race_free p ops input outside,whole_grid_extract p ops input _⟩

#print axioms grid_fold_good
#print axioms initialized_whole_grid_good
#print axioms initialized_whole_grid_race_free
#print axioms source_correct
end LarkNativeAwqGemm
