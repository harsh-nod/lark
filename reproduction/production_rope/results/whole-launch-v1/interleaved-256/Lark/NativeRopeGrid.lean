import Lark.NativeRopeInvariant

/-! Complete actual native wave/block/grid execution from the seeded mutable
interface, with derived race freedom and every thread halted at PC49. -/
namespace LarkNativeRope
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def finalState (p : Shape) (neox : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) : State α :=
  LarkScalarLaunch.launchPost (geometry p) (post ops input neox) (initial p input outside)

theorem final_launch (p : Shape) (neox : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) :
    runLaunch ops (layout p) (geometry p) fuel (program neox) (initial p input outside) =
        some (finalState p neox ops input outside) ∧
      Invariant p neox ops input (finalState p neox ops input outside) ∧
      (∀ t, t < p.rows * 512 → (finalState p neox ops input outside).pc t = 49) := by
  exact LarkScalarLaunch.launch_simulation ops (layout p) (geometry p) 256 49 (program neox)
    (post ops input neox) (Invariant p neox ops input) (final_halt neox) (lane_contract p neox ops input)
    p.positive (by change 0 < 512; decide) (by change 0 < 64; decide)
    (initial p input outside) (initial_invariant p neox ops input outside)

theorem final_good (p : Shape) (neox : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) :
    ∀ a ∈ (finalState p neox ops input outside).trace, Good neox a :=
  (final_launch p neox ops input outside).2.1.good

theorem final_race_free (p : Shape) (neox : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) :
    raceFree (geometry p) (finalState p neox ops input outside).trace = true :=
  race_free p neox _ (final_good p neox ops input outside)

theorem final_completed (p : Shape) (neox : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (t : Nat) (ht : t < p.rows * 512) :
    Completed ops input neox t (finalState p neox ops input outside) :=
  (final_launch p neox ops input outside).2.1.completed t ht ((final_launch p neox ops input outside).2.2 t ht)

theorem final_cache (p : Shape) (neox : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) : CacheReads p input (finalState p neox ops input outside) :=
  (final_launch p neox ops input outside).2.1.cache

#print axioms final_launch
#print axioms final_good
#print axioms final_race_free
#print axioms final_completed
#print axioms final_cache
end LarkNativeRope
