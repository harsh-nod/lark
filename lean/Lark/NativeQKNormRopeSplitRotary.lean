import Lark.NativeQKNormRopeSplitProducts

/-! All four actual split-half cache/product groups, ending at the source's
second warp fence. Earlier output registers survive later groups. -/
namespace LarkNativeQKNormRope
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def SplitRotaryInputs (values partners : Nat → α) (t : Nat) (s : State α) : Prop :=
  (∀ e, e < 4 → s.regs t (18 + 2 * e) = some (values e)) ∧
  (∀ e, e < 4 → s.regs t (25 + e) = some (partners e))

def splitCosValue (ops : Ops α) (input : Nat → Nat → α) (t e : Nat) : α :=
  ops.fromHalf (input 4 (splitCosAddress t e))
def splitSinValue (ops : Ops α) (input : Nat → Nat → α) (t e : Nat) : α :=
  ops.fromHalf (input 4 (splitSinAddress t e))
def splitRotaryValue (ops : Ops α) (input : Nat → Nat → α) (values partners : Nat → α) (t e : Nat) : α :=
  splitComponent ops (values e) (partners e) (splitCosValue ops input t e) (splitSinValue ops input t e)

def splitRotaryAt (ops : Ops α) (input : Nat → Nat → α) (values partners : Nat → α)
    (t e : Nat) (s : State α) : State α :=
  splitProductsAfter ops t e (values e) (partners e) (splitCosValue ops input t e)
    (splitSinValue ops input t e) (splitCacheAfter ops input t e s)

theorem split_rotary_at_eq (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (values partners : Nat → α)
    (t e extra : Nat) (s : State α) (ht : t < p.rows * 1280) (he : e < 4)
    (hp : s.pc t = 69 + 7 * e) (hv : SplitRotaryInputs values partners t s)
    (hi : NativeIndices t s) (hr : Reads p input s) :
    LarkCollective.runLane ops (layout p) (geometry p) (program true) t (extra + 7) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program true) t extra
        (splitRotaryAt ops input values partners t e s) := by
  rw [show extra + 7 = (extra + 3) + 4 by omega,
    split_cache_eq p ops input t e (extra + 3) s ht he hp hi.1 hi.2.2.2.1 hr]
  apply split_products_eq p ops t e extra _ _ _ _ _ he (split_cache_pc ops input t e s)
  · exact (split_cache_low_reg ops input t e (18 + 2 * e) s (by omega)).trans (hv.1 e he)
  · exact (split_cache_low_reg ops input t e (25 + e) s (by omega)).trans (hv.2 e he)
  · exact (split_cache_values ops input t e s).1
  · exact (split_cache_values ops input t e s).2

theorem split_rotary_at_pc (ops : Ops α) (input : Nat → Nat → α) (values partners : Nat → α)
    (t e : Nat) (s : State α) : (splitRotaryAt ops input values partners t e s).pc t = 69 + 7 * (e + 1) := by
  have pc := split_products_pc ops t e (values e) (partners e) (splitCosValue ops input t e)
    (splitSinValue ops input t e) (splitCacheAfter ops input t e s)
  simpa only [show 76 + 7 * e = 69 + 7 * (e + 1) by omega] using pc

theorem split_rotary_at_value (ops : Ops α) (input : Nat → Nat → α) (values partners : Nat → α)
    (t e : Nat) (s : State α) :
    (splitRotaryAt ops input values partners t e s).regs t (33 + 5 * e) =
      some (splitRotaryValue ops input values partners t e) :=
  split_products_value ops t e _ _ _ _ _

theorem split_rotary_at_before (ops : Ops α) (input : Nat → Nat → α) (values partners : Nat → α)
    (t e r : Nat) (s : State α) (hr : r < 29 + 5 * e) :
    (splitRotaryAt ops input values partners t e s).regs t r = s.regs t r :=
  (split_products_low ops t e r _ _ _ _ _ (by omega)).trans (split_cache_reg_before ops input t e r s hr)

theorem split_rotary_at_inputs (ops : Ops α) (input : Nat → Nat → α) (values partners : Nat → α)
    (t e : Nat) (s : State α) (hv : SplitRotaryInputs values partners t s) :
    SplitRotaryInputs values partners t (splitRotaryAt ops input values partners t e s) := by
  constructor
  · intro r hr; exact (split_rotary_at_before ops input values partners t e (18 + 2 * r) s (by omega)).trans (hv.1 r hr)
  · intro r hr; exact (split_rotary_at_before ops input values partners t e (25 + r) s (by omega)).trans (hv.2 r hr)

theorem split_rotary_at_index (ops : Ops α) (input : Nat → Nat → α) (values partners : Nat → α)
    (t e r : Nat) (s : State α) (hr : r < 15) :
    (splitRotaryAt ops input values partners t e s).indices t r = s.indices t r :=
  split_cache_low_index ops input t e r s hr

theorem split_rotary_at_indices (ops : Ops α) (input : Nat → Nat → α) (values partners : Nat → α)
    (t e : Nat) (s : State α) (hi : NativeIndices t s) :
    NativeIndices t (splitRotaryAt ops input values partners t e s) := by
  simpa only [NativeIndices, split_rotary_at_index ops input values partners t e 1 s (by decide),
    split_rotary_at_index ops input values partners t e 2 s (by decide),
    split_rotary_at_index ops input values partners t e 3 s (by decide),
    split_rotary_at_index ops input values partners t e 4 s (by decide),
    split_rotary_at_index ops input values partners t e 5 s (by decide),
    split_rotary_at_index ops input values partners t e 6 s (by decide)] using hi

theorem split_rotary_at_other (ops : Ops α) (input : Nat → Nat → α) (values partners : Nat → α)
    (t e u : Nat) (s : State α) (hu : u ≠ t) :
    (splitRotaryAt ops input values partners t e s).pc u = s.pc u ∧
    (splitRotaryAt ops input values partners t e s).indices u = s.indices u ∧
    (splitRotaryAt ops input values partners t e s).regs u = s.regs u := by
  have cache := split_cache_other ops input t e u s hu
  have products := split_products_other ops t e u (values e) (partners e) (splitCosValue ops input t e)
    (splitSinValue ops input t e) (splitCacheAfter ops input t e s) hu
  exact ⟨products.1.trans cache.1, cache.2.1, products.2.trans cache.2.2⟩

def splitRotaryParts (ops : Ops α) (input : Nat → Nat → α) (values partners : Nat → α) (t : Nat) :
    Nat → Nat → State α → State α
  | _, 0, s => s
  | n, remaining + 1, s => splitRotaryParts ops input values partners t (n + 1) remaining
      (splitRotaryAt ops input values partners t n s)

theorem split_rotary_parts_run (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (values partners : Nat → α)
    (t n remaining extra : Nat) (s : State α) (ht : t < p.rows * 1280) (hn : n + remaining ≤ 4)
    (hp : s.pc t = 69 + 7 * n) (hv : SplitRotaryInputs values partners t s)
    (hi : NativeIndices t s) (hr : Reads p input s) :
    LarkCollective.runLane ops (layout p) (geometry p) (program true) t (extra + 7 * remaining) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program true) t extra
        (splitRotaryParts ops input values partners t n remaining s) := by
  induction remaining generalizing n s with
  | zero => rfl
  | succ remaining ih =>
      rw [show extra + 7 * (remaining + 1) = (extra + 7 * remaining) + 7 by omega,
        split_rotary_at_eq p ops input values partners t n (extra + 7 * remaining) s ht (by omega) hp hv hi hr]
      exact ih (n + 1) _ (by omega) (split_rotary_at_pc ops input values partners t n s)
        (split_rotary_at_inputs ops input values partners t n s hv)
        (split_rotary_at_indices ops input values partners t n s hi) hr

theorem split_rotary_parts_before (ops : Ops α) (input : Nat → Nat → α) (values partners : Nat → α)
    (t n remaining r : Nat) (s : State α) (hr : r < 29 + 5 * n) :
    (splitRotaryParts ops input values partners t n remaining s).regs t r = s.regs t r := by
  induction remaining generalizing n s with
  | zero => rfl
  | succ remaining ih =>
      exact (ih (n + 1) _ (by omega)).trans (split_rotary_at_before ops input values partners t n r s hr)

theorem split_rotary_parts_value (ops : Ops α) (input : Nat → Nat → α) (values partners : Nat → α)
    (t n remaining e : Nat) (s : State α) (he : n ≤ e ∧ e < n + remaining) :
    (splitRotaryParts ops input values partners t n remaining s).regs t (33 + 5 * e) =
      some (splitRotaryValue ops input values partners t e) := by
  induction remaining generalizing n s with
  | zero => omega
  | succ remaining ih =>
      by_cases same : e = n
      · subst e
        exact (split_rotary_parts_before ops input values partners t (n + 1) remaining (33 + 5 * n)
          (splitRotaryAt ops input values partners t n s) (by omega)).trans
          (split_rotary_at_value ops input values partners t n s)
      · exact ih (n + 1) _ ⟨by omega, by omega⟩

theorem split_rotary_parts_index (ops : Ops α) (input : Nat → Nat → α) (values partners : Nat → α)
    (t n remaining r : Nat) (s : State α) (hr : r < 15) :
    (splitRotaryParts ops input values partners t n remaining s).indices t r = s.indices t r := by
  induction remaining generalizing n s with
  | zero => rfl
  | succ remaining ih => exact (ih (n + 1) _).trans (split_rotary_at_index ops input values partners t n r s hr)

theorem split_rotary_parts_preserves (ops : Ops α) (input : Nat → Nat → α) (values partners : Nat → α)
    (t n remaining : Nat) (s : State α) :
    (splitRotaryParts ops input values partners t n remaining s).memory = s.memory ∧
    (splitRotaryParts ops input values partners t n remaining s).epochs = s.epochs := by
  induction remaining generalizing n s with
  | zero => exact ⟨rfl, rfl⟩
  | succ remaining ih => exact ih (n + 1) (splitRotaryAt ops input values partners t n s)

theorem split_rotary_parts_trace_length (ops : Ops α) (input : Nat → Nat → α) (values partners : Nat → α)
    (t n remaining : Nat) (s : State α) :
    (splitRotaryParts ops input values partners t n remaining s).trace.length = s.trace.length + 2 * remaining := by
  induction remaining generalizing n s with
  | zero => simp [splitRotaryParts]
  | succ remaining ih =>
      change (splitRotaryParts ops input values partners t (n + 1) remaining
        (splitRotaryAt ops input values partners t n s)).trace.length = _
      rw [ih]
      have len : (splitRotaryAt ops input values partners t n s).trace.length = s.trace.length + 2 := by
        change (splitCacheAfter ops input t n s).trace.length = _
        rw [split_cache_trace]
        simp
      rw [len]
      omega

theorem split_rotary_parts_good (ops : Ops α) (input : Nat → Nat → α) (values partners : Nat → α)
    (t n remaining : Nat) (s : State α) (good : ∀ a ∈ s.trace, Good a) :
    ∀ a ∈ (splitRotaryParts ops input values partners t n remaining s).trace, Good a := by
  induction remaining generalizing n s with
  | zero => exact good
  | succ remaining ih => exact ih (n + 1) _ (split_cache_good ops input t n s good)

theorem split_rotary_parts_other (ops : Ops α) (input : Nat → Nat → α) (values partners : Nat → α)
    (t n remaining u : Nat) (s : State α) (hu : u ≠ t) :
    (splitRotaryParts ops input values partners t n remaining s).pc u = s.pc u ∧
    (splitRotaryParts ops input values partners t n remaining s).indices u = s.indices u ∧
    (splitRotaryParts ops input values partners t n remaining s).regs u = s.regs u := by
  induction remaining generalizing n s with
  | zero => exact ⟨rfl, rfl, rfl⟩
  | succ remaining ih =>
      have later := ih (n + 1) (splitRotaryAt ops input values partners t n s)
      have first := split_rotary_at_other ops input values partners t n u s hu
      exact ⟨later.1.trans first.1, later.2.1.trans first.2.1, later.2.2.trans first.2.2⟩

def splitRotaryFour (ops : Ops α) (input : Nat → Nat → α) (values partners : Nat → α)
    (t : Nat) (s : State α) : State α := splitRotaryParts ops input values partners t 0 4 s

theorem split_rotary_four_pc (ops : Ops α) (input : Nat → Nat → α) (values partners : Nat → α)
    (t : Nat) (s : State α) : (splitRotaryFour ops input values partners t s).pc t = 97 :=
  split_rotary_at_pc ops input values partners t 3 _

#print axioms split_rotary_at_eq
#print axioms split_rotary_at_pc
#print axioms split_rotary_at_value
#print axioms split_rotary_at_before
#print axioms split_rotary_at_inputs
#print axioms split_rotary_at_index
#print axioms split_rotary_at_indices
#print axioms split_rotary_at_other
#print axioms split_rotary_parts_run
#print axioms split_rotary_parts_before
#print axioms split_rotary_parts_value
#print axioms split_rotary_parts_index
#print axioms split_rotary_parts_preserves
#print axioms split_rotary_parts_trace_length
#print axioms split_rotary_parts_good
#print axioms split_rotary_parts_other
#print axioms split_rotary_four_pc
end LarkNativeQKNormRope
