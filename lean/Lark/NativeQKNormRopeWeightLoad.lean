import Lark.NativeQKNormRopeWeightIndex

/-! Actual four weight loads, with buffer selection supplied by the branch. -/
namespace LarkNativeQKNormRope
open LarkNonlinear
open LarkReduction (setReg)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def weightValue (ops : Ops α) (input : Nat → Nat → α) (t buffer e : Nat) : α :=
  ops.fromHalf (input buffer (column t e))

def weightLoadAt (ops : Ops α) (input : Nat → Nat → α) (t buffer start e : Nat)
    (s : State α) : State α :=
  loaded ops t (13 + e) (start + e + 1) buffer (column t e) (input buffer (column t e)) s

theorem weight_load_at_eq (p : Shape) (neox : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (t buffer start e extra : Nat) (s : State α)
    (hb : buffer = 2 ∧ start = 42 ∨ buffer = 3 ∧ start = 47) (he : e < 4)
    (hp : s.pc t = start + e) (hi : s.indices t (11 + e) = some ((column t e : Nat) : Int))
    (hr : Reads p input s) :
    LarkCollective.runLane ops (layout p) (geometry p) (program neox) t (extra + 1) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program neox) t extra
        (weightLoadAt ops input t buffer start e s) := by
  have hcol := column_bound t e he
  have loc : location (layout p) (geometry p) t .global buffer (column t e : Int) false =
      some (globalCell buffer (column t e)) := by
    rcases hb with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp [location, layout, globalCell, hcol]
  have mem : s.memory (globalCell buffer (column t e)) = some (input buffer (column t e)) := by
    rcases hb with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact hr.2.1 _ hcol
    · exact hr.2.2.1 _ hcol
  have ex : execute ops (layout p) (geometry p) t
      (.assign (13 + e) (.un .fromHalf (.load .global buffer (.ivar (11 + e))))) s =
      some (weightLoadAt ops input t buffer start e s) := by
    simp only [execute, evalExpr, evalIndex, hi, loc, mem, applyUnary, bind, pure, Option.bind]
    simp only [weightLoadAt, loaded, setReg, advance, record, hp]
  have code : (program neox)[start + e]? =
      some (.scalar (.assign (13 + e) (.un .fromHalf (.load .global buffer (.ivar (11 + e)))))) := by
    have hc : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 := by omega
    rcases hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hc with rfl | rfl | rfl | rfl <;> cases neox <;> decide
  exact scalar_step p neox ops t (start + e) extra _ s _ code hp ex

def weightFourLoads (ops : Ops α) (input : Nat → Nat → α) (t buffer start : Nat)
    (s : State α) : State α :=
  weightLoadAt ops input t buffer start 3 (weightLoadAt ops input t buffer start 2
    (weightLoadAt ops input t buffer start 1 (weightLoadAt ops input t buffer start 0 s)))

theorem weight_four_eq (p : Shape) (neox : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (t buffer start extra : Nat) (s : State α)
    (hb : buffer = 2 ∧ start = 42 ∨ buffer = 3 ∧ start = 47)
    (hp : s.pc t = start) (hi : ∀ e, e < 4 → s.indices t (11 + e) = some ((column t e : Nat) : Int))
    (hr : Reads p input s) :
    LarkCollective.runLane ops (layout p) (geometry p) (program neox) t (extra + 4) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program neox) t extra
        (weightFourLoads ops input t buffer start s) := by
  rewrite [weight_load_at_eq p neox ops input t buffer start 0 (extra + 3) s hb (by decide) hp (hi 0 (by decide)) hr]
  rewrite [weight_load_at_eq p neox ops input t buffer start 1 (extra + 2)
    (weightLoadAt ops input t buffer start 0 s) hb (by decide)
    (by simp [weightLoadAt, loaded, setReg, advance]) (hi 1 (by decide)) hr]
  rewrite [weight_load_at_eq p neox ops input t buffer start 2 (extra + 1)
    (weightLoadAt ops input t buffer start 1 (weightLoadAt ops input t buffer start 0 s)) hb (by decide)
    (by simp [weightLoadAt, loaded, setReg, advance] <;> omega) (hi 2 (by decide)) hr]
  rewrite [weight_load_at_eq p neox ops input t buffer start 3 extra
    (weightLoadAt ops input t buffer start 2 (weightLoadAt ops input t buffer start 1
      (weightLoadAt ops input t buffer start 0 s))) hb (by decide)
    (by simp [weightLoadAt, loaded, setReg, advance] <;> omega) (hi 3 (by decide)) hr]
  rfl

theorem weight_four_pc (ops : Ops α) (input : Nat → Nat → α) (t buffer start : Nat) (s : State α) :
    (weightFourLoads ops input t buffer start s).pc t = start + 4 := by
  simp [weightFourLoads, weightLoadAt, loaded, setReg, advance] <;> omega

theorem weight_four_value (ops : Ops α) (input : Nat → Nat → α) (t buffer start e : Nat)
    (s : State α) (he : e < 4) :
    (weightFourLoads ops input t buffer start s).regs t (13 + e) = some (weightValue ops input t buffer e) := by
  have hc : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 := by omega
  rcases hc with rfl | rfl | rfl | rfl <;>
    simp [weightFourLoads, weightLoadAt, loaded, setReg, record, advance, weightValue]

theorem weight_four_low (ops : Ops α) (input : Nat → Nat → α) (t buffer start r : Nat)
    (s : State α) (hr : r < 13) :
    (weightFourLoads ops input t buffer start s).regs t r = s.regs t r := by
  have h13 : r ≠ 13 := by omega
  have h14 : r ≠ 14 := by omega
  have h15 : r ≠ 15 := by omega
  have h16 : r ≠ 16 := by omega
  simp [weightFourLoads, weightLoadAt, loaded, setReg, record, advance, h13, h14, h15, h16]

theorem weight_four_preserves (ops : Ops α) (input : Nat → Nat → α) (t buffer start : Nat) (s : State α) :
    (weightFourLoads ops input t buffer start s).memory = s.memory ∧
    (weightFourLoads ops input t buffer start s).indices = s.indices ∧
    (weightFourLoads ops input t buffer start s).epochs = s.epochs := ⟨rfl, rfl, rfl⟩

theorem weight_four_trace (ops : Ops α) (input : Nat → Nat → α) (t buffer start : Nat) (s : State α) :
    (weightFourLoads ops input t buffer start s).trace =
      [⟨t, globalCell buffer (column t 3), false, s.epochs t⟩,
       ⟨t, globalCell buffer (column t 2), false, s.epochs t⟩,
       ⟨t, globalCell buffer (column t 1), false, s.epochs t⟩,
       ⟨t, globalCell buffer (column t 0), false, s.epochs t⟩] ++ s.trace := rfl

theorem weight_four_good (ops : Ops α) (input : Nat → Nat → α) (t buffer start : Nat) (s : State α)
    (hb : 1 ≤ buffer ∧ buffer ≤ 4) (good : ∀ a ∈ s.trace, Good a) :
    ∀ a ∈ (weightFourLoads ops input t buffer start s).trace, Good a := by
  intro a ha
  rw [weight_four_trace] at ha
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with (rfl | rfl | rfl | rfl) | ha
  · exact input_access_good t buffer _ _ hb
  · exact input_access_good t buffer _ _ hb
  · exact input_access_good t buffer _ _ hb
  · exact input_access_good t buffer _ _ hb
  · exact good a ha

theorem weight_four_other (ops : Ops α) (input : Nat → Nat → α) (t buffer start u : Nat)
    (s : State α) (hu : u ≠ t) :
    (weightFourLoads ops input t buffer start s).pc u = s.pc u ∧
    (weightFourLoads ops input t buffer start s).regs u = s.regs u := by
  constructor
  · simp [weightFourLoads, weightLoadAt, loaded, setReg, record, advance, hu]
  · funext r; simp [weightFourLoads, weightLoadAt, loaded, setReg, record, advance, hu]

#print axioms weight_load_at_eq
#print axioms weight_four_eq
#print axioms weight_four_pc
#print axioms weight_four_value
#print axioms weight_four_low
#print axioms weight_four_preserves
#print axioms weight_four_trace
#print axioms weight_four_good
#print axioms weight_four_other
end LarkNativeQKNormRope
