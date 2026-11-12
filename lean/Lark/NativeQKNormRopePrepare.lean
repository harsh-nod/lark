import Lark.NativeQKNormRopeSquare

/-! The complete actual first lane slice: 24 scalar instructions, four input
loads and four ordered square accumulations, parking at the first shuffle. -/
namespace LarkNativeQKNormRope
open LarkNonlinear
open LarkReduction (setReg execute_pure_of)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def squaresStart (ops : Ops α) (t : Nat) (s : State α) : State α :=
  setReg s t 4 (ops.literal 0 1) 16

theorem squares_start_values (ops : Ops α) (input : Nat → Nat → α) (t : Nat)
    (s : State α) (hv : InputValues ops input t s) : InputValues ops input t (squaresStart ops t s) := by
  intro e he
  have hn : e ≠ 4 := by omega
  simpa [squaresStart, setReg, advance, hn] using hv e he

def sumFour (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) : State α :=
  squareAt ops input t 3 (squareAt ops input t 2 (squareAt ops input t 1
    (squareAt ops input t 0 (squaresStart ops t s))))

theorem sum_four_eq (p : Shape) (neox : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (t extra : Nat) (s : State α) (hp : s.pc t = 15) (hv : InputValues ops input t s) :
    LarkCollective.runLane ops (layout p) (geometry p) (program neox) t (extra + 9) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program neox) t extra (sumFour ops input t s) := by
  let s0 := squaresStart ops t s
  let s1 := squareAt ops input t 0 s0
  let s2 := squareAt ops input t 1 s1
  let s3 := squareAt ops input t 2 s2
  have e0 := execute_pure_of ops (layout p) (geometry p) t 4 16 (.lit 0 1) s (ops.literal 0 1)
    (by simp [evalExpr]) (by omega)
  change execute _ _ _ _ _ s = some s0 at e0
  rewrite [scalar_step p neox ops t 15 (extra + 8) _ s s0 (by cases neox <;> decide) hp e0]
  have hv0 := squares_start_values ops input t s hv
  have ha0 : s0.regs t 4 = some (squarePrefix ops input t 0) := by simp [s0, squaresStart, setReg, advance, squarePrefix]
  rewrite [show extra + 8 = (extra + 6) + 2 by omega,
    square_at_eq p neox ops input t 0 (extra + 6) s0 (by decide)
      (by simp [s0, squaresStart, setReg, advance]) hv0 ha0]
  change LarkCollective.runLane _ _ _ _ _ (extra + 6) s1 = _
  have hv1 := square_at_values ops input t 0 s0 hv0
  rewrite [show extra + 6 = (extra + 4) + 2 by omega,
    square_at_eq p neox ops input t 1 (extra + 4) s1 (by decide)
      (by simp [s1, square_at_pc]) hv1 (square_at_acc ops input t 0 s0)]
  change LarkCollective.runLane _ _ _ _ _ (extra + 4) s2 = _
  have hv2 := square_at_values ops input t 1 s1 hv1
  rewrite [show extra + 4 = (extra + 2) + 2 by omega,
    square_at_eq p neox ops input t 2 (extra + 2) s2 (by decide)
      (by simp [s2, square_at_pc]) hv2 (square_at_acc ops input t 1 s1)]
  change LarkCollective.runLane _ _ _ _ _ (extra + 2) s3 = _
  rewrite [square_at_eq p neox ops input t 3 extra s3 (by decide)
    (by simp [s3, square_at_pc]) (square_at_values ops input t 2 s2 hv2)
    (square_at_acc ops input t 2 s2)]
  rfl

theorem sum_four_values (ops : Ops α) (input : Nat → Nat → α) (t : Nat)
    (s : State α) (hv : InputValues ops input t s) : InputValues ops input t (sumFour ops input t s) := by
  unfold sumFour
  apply square_at_values
  apply square_at_values
  apply square_at_values
  apply square_at_values
  exact squares_start_values ops input t s hv

theorem sum_four_pc (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) :
    (sumFour ops input t s).pc t = 24 := by simp [sumFour, square_at_pc]

theorem sum_four_acc (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) :
    (sumFour ops input t s).regs t 4 = some (squarePrefix ops input t 4) := by simp [sumFour, square_at_acc]

def prepared (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) : State α :=
  sumFour ops input t (loadedPrefix ops input t s)

theorem prepared_values (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) :
    InputValues ops input t (prepared ops input t s) :=
  sum_four_values ops input t _ (fun e he => four_loads_values ops input t e (indexed t s) he)

theorem prepared_acc (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) :
    (prepared ops input t s).regs t 4 = some (squarePrefix ops input t 4) := sum_four_acc ops input t _

theorem prepared_pc (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) :
    (prepared ops input t s).pc t = 24 := sum_four_pc ops input t _

theorem prepared_eq (p : Shape) (neox : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (t extra : Nat) (s : State α) (ht : t < p.rows * 1280) (hp : s.pc t = 0) (hr : Reads p input s) :
    LarkCollective.runLane ops (layout p) (geometry p) (program neox) t (extra + 24) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program neox) t extra (prepared ops input t s) := by
  rewrite [show extra + 24 = (extra + 9) + 15 by omega,
    loaded_prefix_eq p neox ops input t (extra + 9) s ht hp hr]
  rewrite [sum_four_eq p neox ops input t extra (loadedPrefix ops input t s)
    (four_loads_pc ops input t _) (fun e he => four_loads_values ops input t e (indexed t s) he)]
  rfl

theorem prepared_parked (neox : Bool) (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) :
    LarkCollective.parked (program neox) (prepared ops input t s) t = some .shuffle := by
  have hi : (program neox)[24]? = some (.shuffle .xor 9 4 (.const 16) 32) := by cases neox <;> decide
  simp [LarkCollective.parked, prepared_pc, hi]

theorem prepared_lane (p : Shape) (neox : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (t : Nat) (s : State α) (ht : t < p.rows * 1280) (hp : s.pc t = 0) (hr : Reads p input s) :
    LarkCollective.runLane ops (layout p) (geometry p) (program neox) t fuel.lane s =
      some (prepared ops input t s) := by
  change LarkCollective.runLane _ _ _ _ _ (232 + 24) s = _
  rw [prepared_eq p neox ops input t 232 s ht hp hr]
  change LarkCollective.runLane _ _ _ _ _ (231 + 1) (prepared ops input t s) = _
  rw [LarkCollective.runLane, prepared_parked]

theorem prepared_preserves (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) :
    (prepared ops input t s).memory = s.memory ∧ (prepared ops input t s).epochs = s.epochs := ⟨rfl, rfl⟩

theorem prepared_trace (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) :
    (prepared ops input t s).trace =
      [⟨t, globalCell 1 (inputAddress t 3), false, s.epochs t⟩,
       ⟨t, globalCell 1 (inputAddress t 2), false, s.epochs t⟩,
       ⟨t, globalCell 1 (inputAddress t 1), false, s.epochs t⟩,
       ⟨t, globalCell 1 (inputAddress t 0), false, s.epochs t⟩] ++ s.trace := rfl

theorem prepared_good (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α)
    (good : ∀ a ∈ s.trace, Good a) : ∀ a ∈ (prepared ops input t s).trace, Good a :=
  four_loads_good ops input t (indexed t s) good

theorem prepared_low_indices (ops : Ops α) (input : Nat → Nat → α) (t r : Nat) (s : State α)
    (hr : r < 7) : (prepared ops input t s).indices t r = (indexed t s).indices t r :=
  four_loads_low_indices ops input t r (indexed t s) hr

theorem prepared_other (ops : Ops α) (input : Nat → Nat → α) (t u : Nat) (s : State α)
    (hu : u ≠ t) : (prepared ops input t s).pc u = s.pc u ∧
      (prepared ops input t s).indices u = s.indices u ∧
      (prepared ops input t s).regs u = s.regs u := by
  refine ⟨?_, ?_, ?_⟩
  · simp [prepared, sumFour, squaresStart, squareAt, loadedPrefix, fourLoads, loadAt, loaded,
      indexed, LarkReduction.setIndex, setReg, record, advance, hu]
  · funext r
    simp [prepared, sumFour, squaresStart, squareAt, loadedPrefix, fourLoads, loadAt, loaded,
      indexed, LarkReduction.setIndex, setReg, record, advance, hu]
  · funext r
    simp [prepared, sumFour, squaresStart, squareAt, loadedPrefix, fourLoads, loadAt, loaded,
      indexed, LarkReduction.setIndex, setReg, record, advance, hu]

#print axioms squares_start_values
#print axioms sum_four_eq
#print axioms sum_four_values
#print axioms sum_four_pc
#print axioms sum_four_acc
#print axioms prepared_values
#print axioms prepared_acc
#print axioms prepared_pc
#print axioms prepared_eq
#print axioms prepared_parked
#print axioms prepared_lane
#print axioms prepared_preserves
#print axioms prepared_trace
#print axioms prepared_good
#print axioms prepared_low_indices
#print axioms prepared_other
end LarkNativeQKNormRope
