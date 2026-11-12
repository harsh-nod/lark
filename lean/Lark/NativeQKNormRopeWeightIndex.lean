import Lark.NativeQKNormRopeScale

/-! Actual four column indices at PCs37..40, before the Q/K weight branch. -/
namespace LarkNativeQKNormRope
open LarkNonlinear
open LarkReduction (setIndex execute_index_of int32_cast)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def weightIndexAt (t e : Nat) (s : State α) : State α :=
  setIndex s t (11 + e) ((column t e : Nat) : Int) (38 + e)

theorem weight_index_eq (p : Shape) (neox : Bool) (ops : Ops α) (t e extra : Nat)
    (s : State α) (he : e < 4) (hp : s.pc t = 37 + e)
    (hc : s.indices t 4 = some ((column t 0 : Nat) : Int)) :
    LarkCollective.runLane ops (layout p) (geometry p) (program neox) t (extra + 1) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program neox) t extra (weightIndexAt t e s) := by
  have hsum : column t 0 + e = column t e := by simp [column]
  have hb := column_bound t e he
  have hi := eval_nat_add (geometry p) t s (.ivar 4) (.const (e : Int)) (column t 0) e
    hc (int32_cast e (by omega)) (by rw [hsum]; omega)
  rw [hsum] at hi
  have ex := execute_index_of ops (layout p) (geometry p) t (11 + e) (38 + e)
    (.add (.ivar 4) (.const (e : Int))) s _ hi (by omega)
  have code : (program neox)[37 + e]? =
      some (.scalar (.index (11 + e) (.add (.ivar 4) (.const (e : Int))))) := by
    have hc : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 := by omega
    rcases hc with rfl | rfl | rfl | rfl <;> cases neox <;> decide
  exact scalar_step p neox ops t (37 + e) extra _ s _ code hp ex

def weightIndexed (t : Nat) (s : State α) : State α :=
  weightIndexAt t 3 (weightIndexAt t 2 (weightIndexAt t 1 (weightIndexAt t 0 s)))

theorem weight_indexed_eq (p : Shape) (neox : Bool) (ops : Ops α) (t extra : Nat)
    (s : State α) (hp : s.pc t = 37)
    (hc : s.indices t 4 = some ((column t 0 : Nat) : Int)) :
    LarkCollective.runLane ops (layout p) (geometry p) (program neox) t (extra + 4) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program neox) t extra (weightIndexed t s) := by
  rewrite [weight_index_eq p neox ops t 0 (extra + 3) s (by decide) hp hc]
  rewrite [weight_index_eq p neox ops t 1 (extra + 2) _ (by decide)
    (by simp [weightIndexAt, setIndex, advance]) (by simpa [weightIndexAt, setIndex, advance] using hc)]
  rewrite [weight_index_eq p neox ops t 2 (extra + 1) _ (by decide)
    (by simp [weightIndexAt, setIndex, advance]) (by simpa [weightIndexAt, setIndex, advance] using hc)]
  rewrite [weight_index_eq p neox ops t 3 extra _ (by decide)
    (by simp [weightIndexAt, setIndex, advance]) (by simpa [weightIndexAt, setIndex, advance] using hc)]
  rfl

theorem weight_indexed_pc (t : Nat) (s : State α) : (weightIndexed t s).pc t = 41 := by
  simp [weightIndexed, weightIndexAt, setIndex, advance]

theorem weight_indexed_value (t e : Nat) (s : State α) (he : e < 4) :
    (weightIndexed t s).indices t (11 + e) = some ((column t e : Nat) : Int) := by
  have hc : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 := by omega
  rcases hc with rfl | rfl | rfl | rfl <;> simp [weightIndexed, weightIndexAt, setIndex, advance]

theorem weight_indexed_low (t r : Nat) (s : State α) (hr : r < 11) :
    (weightIndexed t s).indices t r = s.indices t r := by
  have h11 : r ≠ 11 := by omega
  have h12 : r ≠ 12 := by omega
  have h13 : r ≠ 13 := by omega
  have h14 : r ≠ 14 := by omega
  simp [weightIndexed, weightIndexAt, setIndex, advance, h11, h12, h13, h14]

theorem weight_indexed_preserves (t : Nat) (s : State α) :
    (weightIndexed t s).memory = s.memory ∧ (weightIndexed t s).regs = s.regs ∧
    (weightIndexed t s).epochs = s.epochs ∧ (weightIndexed t s).trace = s.trace := ⟨rfl, rfl, rfl, rfl⟩

theorem weight_indexed_other (t u : Nat) (s : State α) (hu : u ≠ t) :
    (weightIndexed t s).pc u = s.pc u ∧ (weightIndexed t s).indices u = s.indices u := by
  constructor
  · simp [weightIndexed, weightIndexAt, setIndex, advance, hu]
  · funext r; simp [weightIndexed, weightIndexAt, setIndex, advance, hu]

#print axioms weight_index_eq
#print axioms weight_indexed_eq
#print axioms weight_indexed_pc
#print axioms weight_indexed_value
#print axioms weight_indexed_low
#print axioms weight_indexed_preserves
#print axioms weight_indexed_other
end LarkNativeQKNormRope
