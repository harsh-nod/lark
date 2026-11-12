import Lark.NativeQKNormRopeStore

/-! Actual four out-of-place stores and the native final halt, in either layout. -/
namespace LarkNativeQKNormRope
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def StoreValues (neox : Bool) (values : Nat → α) (t : Nat) (s : State α) : Prop :=
  ∀ e, e < 4 → s.regs t (outputRegister neox e) = some (values e)

def storeFour (ops : Ops α) (neox : Bool) (t : Nat) (values : Nat → α) (s : State α) : State α :=
  storeAt ops neox t 3 (values 3) (storeAt ops neox t 2 (values 2)
    (storeAt ops neox t 1 (values 1) (storeAt ops neox t 0 (values 0) s)))

theorem store_four_eq (p : Shape) (neox : Bool) (ops : Ops α) (t extra : Nat) (values : Nat → α)
    (s : State α) (ht : t < p.rows * 1280) (hp : s.pc t = storeStart neox)
    (hi : s.indices t 6 = some ((outputAddress t 0 : Nat) : Int)) (hv : StoreValues neox values t s) :
    LarkCollective.runLane ops (layout p) (geometry p) (program neox) t (extra + 8) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program neox) t extra (storeFour ops neox t values s) := by
  let s1 := storeAt ops neox t 0 (values 0) s
  let s2 := storeAt ops neox t 1 (values 1) s1
  let s3 := storeAt ops neox t 2 (values 2) s2
  have hi1 := (store_at_low_index ops neox t 0 6 (values 0) s (by decide)).trans hi
  have hi2 := (store_at_low_index ops neox t 1 6 (values 1) s1 (by decide)).trans hi1
  have hi3 := (store_at_low_index ops neox t 2 6 (values 2) s2 (by decide)).trans hi2
  rewrite [store_at_eq p neox ops t 0 (extra + 6) (values 0) s ht (by decide) hp hi (hv 0 (by decide))]
  rewrite [store_at_eq p neox ops t 1 (extra + 4) (values 1) s1 ht (by decide)
    (store_at_pc ops neox t 0 (values 0) s) hi1 (hv 1 (by decide))]
  rewrite [store_at_eq p neox ops t 2 (extra + 2) (values 2) s2 ht (by decide)
    (by
      have h : s2.pc t = storeStart neox + 2 * 1 + 2 := store_at_pc ops neox t 1 (values 1) s1
      omega) hi2 (hv 2 (by decide))]
  rewrite [store_at_eq p neox ops t 3 extra (values 3) s3 ht (by decide)
    (by
      have h : s3.pc t = storeStart neox + 2 * 2 + 2 := store_at_pc ops neox t 2 (values 2) s2
      omega) hi3 (hv 3 (by decide))]
  rfl

theorem store_four_pc (ops : Ops α) (neox : Bool) (t : Nat) (values : Nat → α) (s : State α) :
    (storeFour ops neox t values s).pc t = storeStart neox + 8 := by
  exact store_at_pc ops neox t 3 (values 3) _

theorem store_four_parked (ops : Ops α) (neox : Bool) (t : Nat) (values : Nat → α) (s : State α) :
    LarkCollective.parked (program neox) (storeFour ops neox t values s) t = some .halt := by
  simp only [LarkCollective.parked, store_four_pc]
  cases neox <;> rfl

theorem store_four_lane (p : Shape) (neox : Bool) (ops : Ops α) (t : Nat) (values : Nat → α)
    (s : State α) (ht : t < p.rows * 1280) (hp : s.pc t = storeStart neox)
    (hi : s.indices t 6 = some ((outputAddress t 0 : Nat) : Int)) (hv : StoreValues neox values t s) :
    LarkCollective.runLane ops (layout p) (geometry p) (program neox) t fuel.lane s = some (storeFour ops neox t values s) := by
  change LarkCollective.runLane _ _ _ _ _ (248 + 8) s = _
  rw [store_four_eq p neox ops t 248 values s ht hp hi hv]
  simp only [LarkCollective.runLane, store_four_parked]

theorem store_four_values (ops : Ops α) (neox : Bool) (t e : Nat) (values : Nat → α)
    (s : State α) (he : e < 4) :
    (storeFour ops neox t values s).memory (globalCell 0 (outputAddress t e)) = some (ops.toHalf (values e)) := by
  have choices : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 := by omega
  rcases choices with rfl | rfl | rfl | rfl <;> simp [storeFour, store_at_memory, globalCell, output_linear]

theorem store_four_outside (ops : Ops α) (neox : Bool) (t : Nat) (values : Nat → α)
    (s : State α) (loc : Location) (hn : ∀ e, e < 4 → loc ≠ globalCell 0 (outputAddress t e)) :
    (storeFour ops neox t values s).memory loc = s.memory loc := by
  simp only [storeFour, store_at_memory, hn 3 (by decide), hn 2 (by decide), hn 1 (by decide), hn 0 (by decide), if_false]

theorem store_four_unowned (ops : Ops α) (neox : Bool) (t : Nat) (values : Nat → α)
    (s : State α) (loc : Location) (hn : loc.buffer ≠ 0 ∨ loc.offset / 4 ≠ t) :
    (storeFour ops neox t values s).memory loc = s.memory loc := by
  apply store_four_outside
  intro e he equal
  rcases hn with hb | ht
  · exact hb (congrArg Location.buffer equal)
  · exact ht ((congrArg (fun cell : Location => cell.offset / 4) equal).trans (output_owner t e he))

theorem store_four_preserves (ops : Ops α) (neox : Bool) (t : Nat) (values : Nat → α) (s : State α) :
    (storeFour ops neox t values s).regs = s.regs ∧ (storeFour ops neox t values s).epochs = s.epochs := ⟨rfl, rfl⟩

theorem store_four_low_index (ops : Ops α) (neox : Bool) (t r : Nat) (values : Nat → α)
    (s : State α) (hr : r < 19) : (storeFour ops neox t values s).indices t r = s.indices t r := by
  simp only [storeFour, store_at_low_index ops neox t _ r _ _ hr]

theorem store_four_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (neox : Bool)
    (t : Nat) (values : Nat → α) (s : State α) (hr : Reads p input s) : Reads p input (storeFour ops neox t values s) :=
  store_at_reads p ops input neox t 3 _ _ (store_at_reads p ops input neox t 2 _ _
    (store_at_reads p ops input neox t 1 _ _ (store_at_reads p ops input neox t 0 _ _ hr)))

theorem store_four_trace (ops : Ops α) (neox : Bool) (t : Nat) (values : Nat → α) (s : State α) :
    (storeFour ops neox t values s).trace = [
      ⟨t, globalCell 0 (outputAddress t 3), true, s.epochs t⟩,
      ⟨t, globalCell 0 (outputAddress t 2), true, s.epochs t⟩,
      ⟨t, globalCell 0 (outputAddress t 1), true, s.epochs t⟩,
      ⟨t, globalCell 0 (outputAddress t 0), true, s.epochs t⟩] ++ s.trace := rfl

theorem store_four_good (ops : Ops α) (neox : Bool) (t : Nat) (values : Nat → α) (s : State α)
    (good : ∀ access ∈ s.trace, Good access) : ∀ access ∈ (storeFour ops neox t values s).trace, Good access :=
  store_at_good ops neox t 3 _ _ (by decide) (store_at_good ops neox t 2 _ _ (by decide)
    (store_at_good ops neox t 1 _ _ (by decide) (store_at_good ops neox t 0 _ _ (by decide) good)))

theorem store_four_other (ops : Ops α) (neox : Bool) (t u : Nat) (values : Nat → α)
    (s : State α) (hu : u ≠ t) :
    (storeFour ops neox t values s).pc u = s.pc u ∧ (storeFour ops neox t values s).indices u = s.indices u := by
  let s1 := storeAt ops neox t 0 (values 0) s
  let s2 := storeAt ops neox t 1 (values 1) s1
  let s3 := storeAt ops neox t 2 (values 2) s2
  have h0 := store_at_other ops neox t 0 u (values 0) s hu
  have h1 := store_at_other ops neox t 1 u (values 1) s1 hu
  have h2 := store_at_other ops neox t 2 u (values 2) s2 hu
  have h3 := store_at_other ops neox t 3 u (values 3) s3 hu
  exact ⟨h3.1.trans (h2.1.trans (h1.1.trans h0.1)), h3.2.trans (h2.2.trans (h1.2.trans h0.2))⟩

#print axioms store_four_eq
#print axioms store_four_pc
#print axioms store_four_parked
#print axioms store_four_lane
#print axioms store_four_values
#print axioms store_four_outside
#print axioms store_four_unowned
#print axioms store_four_preserves
#print axioms store_four_low_index
#print axioms store_four_reads
#print axioms store_four_trace
#print axioms store_four_good
#print axioms store_four_other
end LarkNativeQKNormRope
