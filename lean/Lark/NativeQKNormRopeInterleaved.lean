import Lark.NativeQKNormRopePairProducts

/-! Actual complete two-pair interleaved rotary computation at PCs59..78. -/
namespace LarkNativeQKNormRope
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def RotaryInputs (values : Nat → α) (t : Nat) (s : State α) : Prop :=
  ∀ e, e < 4 → s.regs t (18 + 2 * e) = some (values e)
def pairCosValue (ops : Ops α) (input : Nat → Nat → α) (t pair : Nat) : α :=
  ops.fromHalf (input 4 (pairCosAddress t pair))
def pairSinValue (ops : Ops α) (input : Nat → Nat → α) (t pair : Nat) : α :=
  ops.fromHalf (input 4 (pairSinAddress t pair))

def interleavedPairAfter (ops : Ops α) (input : Nat → Nat → α) (values : Nat → α)
    (t pair : Nat) (s : State α) : State α :=
  pairProductsAfter ops t pair (values (2 * pair)) (values (2 * pair + 1))
    (pairCosValue ops input t pair) (pairSinValue ops input t pair) (pairCacheAfter ops input t pair s)

theorem interleaved_pair_eq (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (values : Nat → α)
    (t pair extra : Nat) (s : State α) (ht : t < p.rows * 1280) (hj : pair < 2)
    (hp : s.pc t = 59 + 10 * pair) (hv : RotaryInputs values t s)
    (hrow : s.indices t 1 = some ((row t : Nat) : Int))
    (hlane : s.indices t 3 = some ((t % 32 : Nat) : Int)) (hr : Reads p input s) :
    LarkCollective.runLane ops (layout p) (geometry p) (program false) t (extra + 10) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program false) t extra
        (interleavedPairAfter ops input values t pair s) := by
  rw [show extra + 10 = (extra + 6) + 4 by omega,
    pair_cache_eq p ops input t pair (extra + 6) s ht hj hp hrow hlane hr]
  apply pair_products_eq p ops t pair extra _ _ _ _ _ hj (pair_cache_pc ops input t pair s)
  · have hf := pair_cache_low_reg ops input t pair (18 + 4 * pair) s (by omega)
    exact hf.trans (by simpa only [show 18 + 2 * (2 * pair) = 18 + 4 * pair by omega] using hv (2 * pair) (by omega))
  · have hf := pair_cache_low_reg ops input t pair (20 + 4 * pair) s (by omega)
    exact hf.trans (by simpa only [show 18 + 2 * (2 * pair + 1) = 20 + 4 * pair by omega] using hv (2 * pair + 1) (by omega))
  · exact (pair_cache_values ops input t pair s).1
  · exact (pair_cache_values ops input t pair s).2

theorem interleaved_pair_pc (ops : Ops α) (input : Nat → Nat → α) (values : Nat → α)
    (t pair : Nat) (s : State α) : (interleavedPairAfter ops input values t pair s).pc t = 69 + 10 * pair :=
  pair_products_pc ops t pair _ _ _ _ _

theorem interleaved_pair_values (ops : Ops α) (input : Nat → Nat → α) (values : Nat → α)
    (t pair : Nat) (s : State α) :
    (interleavedPairAfter ops input values t pair s).regs t (31 + 8 * pair) =
      some (interleavedReal ops (values (2 * pair)) (values (2 * pair + 1)) (pairCosValue ops input t pair) (pairSinValue ops input t pair)) ∧
    (interleavedPairAfter ops input values t pair s).regs t (32 + 8 * pair) =
      some (interleavedImaginary ops (values (2 * pair)) (values (2 * pair + 1)) (pairCosValue ops input t pair) (pairSinValue ops input t pair)) :=
  pair_products_values ops t pair _ _ _ _ _

theorem interleaved_pair_reg_before (ops : Ops α) (input : Nat → Nat → α) (values : Nat → α)
    (t pair r : Nat) (s : State α) (hr : r < 25 + 8 * pair) :
    (interleavedPairAfter ops input values t pair s).regs t r = s.regs t r :=
  (pair_products_low_reg ops t pair r _ _ _ _ _ (by omega)).trans (pair_cache_reg_before ops input t pair r s hr)

theorem interleaved_pair_inputs (ops : Ops α) (input : Nat → Nat → α) (values : Nat → α)
    (t pair : Nat) (s : State α) (hv : RotaryInputs values t s) :
    RotaryInputs values t (interleavedPairAfter ops input values t pair s) := by
  intro e he
  exact (interleaved_pair_reg_before ops input values t pair (18 + 2 * e) s (by omega)).trans (hv e he)

theorem interleaved_pair_low_index (ops : Ops α) (input : Nat → Nat → α) (values : Nat → α)
    (t pair r : Nat) (s : State α) (hr : r < 15) :
    (interleavedPairAfter ops input values t pair s).indices t r = s.indices t r :=
  pair_cache_low_index ops input t pair r s hr

theorem interleaved_pair_preserves (ops : Ops α) (input : Nat → Nat → α) (values : Nat → α)
    (t pair : Nat) (s : State α) :
    (interleavedPairAfter ops input values t pair s).memory = s.memory ∧
    (interleavedPairAfter ops input values t pair s).epochs = s.epochs := pair_cache_preserves ops input t pair s

theorem interleaved_pair_trace (ops : Ops α) (input : Nat → Nat → α) (values : Nat → α)
    (t pair : Nat) (s : State α) : (interleavedPairAfter ops input values t pair s).trace =
    [⟨t, globalCell 4 (pairSinAddress t pair), false, s.epochs t⟩,
     ⟨t, globalCell 4 (pairCosAddress t pair), false, s.epochs t⟩] ++ s.trace := rfl

theorem interleaved_pair_other (ops : Ops α) (input : Nat → Nat → α) (values : Nat → α)
    (t pair u : Nat) (s : State α) (hu : u ≠ t) :
    (interleavedPairAfter ops input values t pair s).pc u = s.pc u ∧
    (interleavedPairAfter ops input values t pair s).indices u = s.indices u ∧
    (interleavedPairAfter ops input values t pair s).regs u = s.regs u := by
  have hf := pair_cache_other ops input t pair u s hu
  have pf := pair_products_other ops t pair u (values (2 * pair)) (values (2 * pair + 1))
    (pairCosValue ops input t pair) (pairSinValue ops input t pair) (pairCacheAfter ops input t pair s) hu
  exact ⟨pf.1.trans hf.1, hf.2.1, pf.2.trans hf.2.2⟩

def interleavedAfter (ops : Ops α) (input : Nat → Nat → α) (values : Nat → α) (t : Nat)
    (s : State α) : State α :=
  interleavedPairAfter ops input values t 1 (interleavedPairAfter ops input values t 0 s)

theorem interleaved_eq (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (values : Nat → α)
    (t extra : Nat) (s : State α) (ht : t < p.rows * 1280) (hp : s.pc t = 59)
    (hv : RotaryInputs values t s) (hrow : s.indices t 1 = some ((row t : Nat) : Int))
    (hlane : s.indices t 3 = some ((t % 32 : Nat) : Int)) (hr : Reads p input s) :
    LarkCollective.runLane ops (layout p) (geometry p) (program false) t (extra + 20) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program false) t extra (interleavedAfter ops input values t s) := by
  rw [show extra + 20 = (extra + 10) + 10 by omega,
    interleaved_pair_eq p ops input values t 0 (extra + 10) s ht (by decide) hp hv hrow hlane hr]
  apply interleaved_pair_eq p ops input values t 1 extra _ ht (by decide)
    (interleaved_pair_pc ops input values t 0 s) (interleaved_pair_inputs ops input values t 0 s hv)
  · exact (interleaved_pair_low_index ops input values t 0 1 s (by decide)).trans hrow
  · exact (interleaved_pair_low_index ops input values t 0 3 s (by decide)).trans hlane
  · exact hr

def interleavedOutput (ops : Ops α) (input : Nat → Nat → α) (values : Nat → α) (t e : Nat) : α :=
  let pair := e / 2
  if e % 2 = 0 then interleavedReal ops (values (2 * pair)) (values (2 * pair + 1))
    (pairCosValue ops input t pair) (pairSinValue ops input t pair)
  else interleavedImaginary ops (values (2 * pair)) (values (2 * pair + 1))
    (pairCosValue ops input t pair) (pairSinValue ops input t pair)

theorem interleaved_pc (ops : Ops α) (input : Nat → Nat → α) (values : Nat → α) (t : Nat) (s : State α) :
    (interleavedAfter ops input values t s).pc t = 79 := interleaved_pair_pc ops input values t 1 _

theorem interleaved_values (ops : Ops α) (input : Nat → Nat → α) (values : Nat → α) (t e : Nat)
    (s : State α) (he : e < 4) :
    (interleavedAfter ops input values t s).regs t (31 + 8 * (e / 2) + e % 2) = some (interleavedOutput ops input values t e) := by
  have first := interleaved_pair_values ops input values t 0 s
  have second := interleaved_pair_values ops input values t 1 (interleavedPairAfter ops input values t 0 s)
  have choices : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 := by omega
  rcases choices with rfl | rfl | rfl | rfl
  · exact (interleaved_pair_reg_before ops input values t 1 31 _ (by decide)).trans first.1
  · exact (interleaved_pair_reg_before ops input values t 1 32 _ (by decide)).trans first.2
  · exact second.1
  · exact second.2

theorem interleaved_preserves (ops : Ops α) (input : Nat → Nat → α) (values : Nat → α) (t : Nat) (s : State α) :
    (interleavedAfter ops input values t s).memory = s.memory ∧ (interleavedAfter ops input values t s).epochs = s.epochs := ⟨rfl, rfl⟩

theorem interleaved_low_index (ops : Ops α) (input : Nat → Nat → α) (values : Nat → α) (t r : Nat)
    (s : State α) (hr : r < 15) : (interleavedAfter ops input values t s).indices t r = s.indices t r :=
  (interleaved_pair_low_index ops input values t 1 r _ hr).trans (interleaved_pair_low_index ops input values t 0 r s hr)

theorem interleaved_trace (ops : Ops α) (input : Nat → Nat → α) (values : Nat → α) (t : Nat) (s : State α) :
    (interleavedAfter ops input values t s).trace = [
      ⟨t, globalCell 4 (pairSinAddress t 1), false, s.epochs t⟩,
      ⟨t, globalCell 4 (pairCosAddress t 1), false, s.epochs t⟩,
      ⟨t, globalCell 4 (pairSinAddress t 0), false, s.epochs t⟩,
      ⟨t, globalCell 4 (pairCosAddress t 0), false, s.epochs t⟩] ++ s.trace := rfl

theorem interleaved_good (ops : Ops α) (input : Nat → Nat → α) (values : Nat → α) (t : Nat)
    (s : State α) (good : ∀ access ∈ s.trace, Good access) :
    ∀ access ∈ (interleavedAfter ops input values t s).trace, Good access := by
  exact pair_cache_good ops input t 1 (interleavedPairAfter ops input values t 0 s)
    (pair_cache_good ops input t 0 s good)

theorem interleaved_other (ops : Ops α) (input : Nat → Nat → α) (values : Nat → α) (t u : Nat)
    (s : State α) (hu : u ≠ t) :
    (interleavedAfter ops input values t s).pc u = s.pc u ∧
    (interleavedAfter ops input values t s).indices u = s.indices u ∧
    (interleavedAfter ops input values t s).regs u = s.regs u := by
  have first := interleaved_pair_other ops input values t 0 u s hu
  have second := interleaved_pair_other ops input values t 1 u (interleavedPairAfter ops input values t 0 s) hu
  exact ⟨second.1.trans first.1, second.2.1.trans first.2.1, second.2.2.trans first.2.2⟩

#print axioms interleaved_pair_eq
#print axioms interleaved_pair_pc
#print axioms interleaved_pair_values
#print axioms interleaved_pair_reg_before
#print axioms interleaved_pair_inputs
#print axioms interleaved_pair_low_index
#print axioms interleaved_pair_preserves
#print axioms interleaved_pair_trace
#print axioms interleaved_pair_other
#print axioms interleaved_eq
#print axioms interleaved_pc
#print axioms interleaved_values
#print axioms interleaved_preserves
#print axioms interleaved_low_index
#print axioms interleaved_trace
#print axioms interleaved_good
#print axioms interleaved_other
end LarkNativeQKNormRope
