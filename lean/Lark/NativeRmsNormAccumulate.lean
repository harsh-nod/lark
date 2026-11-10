import Lark.NativeRmsNormAddress

/-! Actual six-instruction accumulation cycle inside an eight-element vector.
This phase is proved for the fixed collective-machine program and native layout.
-/
namespace LarkNativeRmsNorm
open LarkNonlinear
open LarkReduction (setIndex setReg int32_cast execute_index_of execute_pure_of)
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def termAt (ops : Ops α) (input : Nat → Nat → α) (row vector component : Nat) : α :=
  let x := ops.fromHalf (input 1 (scalarAddress row vector component))
  ops.mul x x

theorem termAt_square (ops : Ops α) (input : Nat → Nat → α) (row vector component : Nat) :
    termAt ops input row vector component = square ops input row (vector * 8 + component) := by
  simp [termAt, square, scalarAddress, Nat.add_assoc]

def componentAfter (ops : Ops α) (input : Nat → Nat → α) (row vector component t : Nat)
    (acc : α) (s : State α) : State α :=
  let s := advance s t 11
  let s := setReg (record s t (globalCell 1 (scalarAddress row vector component)) false) t 2
    (ops.fromHalf (input 1 (scalarAddress row vector component))) 12
  let s := setReg s t 3 (termAt ops input row vector component) 13
  let s := setReg s t 0 (ops.add acc (termAt ops input row vector component)) 14
  let s := setIndex s t 6 ((component + 1 : Nat) : Int) 15
  advance s t 10

theorem component_cycle (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row vector component t extra : Nat) (acc : α) (s : State α)
    (reads : Reads p input s) (hr : row < p.rows) (hv : vector < 2048) (hc : component < 8)
    (hi0 : s.indices t 0 = some (row : Int)) (hi5 : s.indices t 5 = some (vector : Int))
    (hi6 : s.indices t 6 = some (component : Int)) (ha : s.regs t 0 = some acc) (hp : s.pc t = 10) :
    LarkCollective.runLane ops (layout p) (geometry p) program t (extra + 6) s =
      LarkCollective.runLane ops (layout p) (geometry p) program t extra
        (componentAfter ops input row vector component t acc s) := by
  let x := ops.fromHalf (input 1 (scalarAddress row vector component))
  let term := termAt ops input row vector component
  let s1 := advance s t 11
  let s2 := setReg (record s1 t (globalCell 1 (scalarAddress row vector component)) false) t 2 x 12
  let s3 := setReg s2 t 3 term 13
  let s4 := setReg s3 t 0 (ops.add acc term) 14
  let s5 := setIndex s4 t 6 ((component + 1 : Nat) : Int) 15
  have hpred := LarkReduction.predicate_lt_of (geometry p) t s (.ivar 6) (.const 8)
    (component : Int) 8 hi6 (by rfl) (by omega)
  have h1 : execute ops (layout p) (geometry p) t
      (.branch (.lt (.ivar 6) (.const 8)) 16) s = some s1 := by
    simp only [execute, hpred, hp, bind, pure, Option.bind]
    rfl
  have he2 := load_input p ops input t 5 6 row vector component s1 reads hi0 hi5 hi6 hr hv hc
  have h2 : execute ops (layout p) (geometry p) t
      (.assign 2 (.un .fromHalf (.load .global 1 (rowIndex 5 6)))) s1 = some s2 := by
    simp only [execute, he2, bind, pure, Option.bind]
    have hn : s1.pc t + 1 = 12 := by simp [s1, advance]
    rewrite [hn]
    rfl
  have h3 := execute_pure_of ops (layout p) (geometry p) t 3 13
    (.bin .mul (.reg 2) (.reg 2)) s2 term
    (by simp [evalExpr, applyBinary, s2, setReg, advance, term, termAt, x])
    (by simp [s2, setReg, advance])
  change execute _ _ _ _ _ s2 = some s3 at h3
  have h4 := execute_pure_of ops (layout p) (geometry p) t 0 14
    (.bin .add (.reg 0) (.reg 3)) s3 (ops.add acc term)
    (by simp [evalExpr, applyBinary, s3, s2, s1, setReg, record, advance, ha])
    (by simp [s3, setReg, advance])
  change execute _ _ _ _ _ s3 = some s4 at h4
  have he5 := LarkReduction.eval_add_of (geometry p) t s4 (.ivar 6) (.const 1)
    (component : Int) 1 ((component + 1 : Nat) : Int) hi6 (by rfl)
    ((congrArg int32 (Int.natCast_add component 1).symm).trans (int32_cast _ (by omega)))
  have h5 := execute_index_of ops (layout p) (geometry p) t 6 15
    (.add (.ivar 6) (.const 1)) s4 ((component + 1 : Nat) : Int) he5
    (by simp [s4, setReg, advance])
  change execute _ _ _ _ _ s4 = some s5 at h5
  have h6 : execute ops (layout p) (geometry p) t (.jump 10) s5 =
      some (componentAfter ops input row vector component t acc s) := rfl
  rewrite [scalar_step ops _ _ _ _ _ _ _ _
    (by simp [LarkCollective.parked, program, hp]) (by simp [program, hp]) h1]
  rewrite [scalar_step ops _ _ _ _ _ _ _ _
    (by simp [LarkCollective.parked, program, s1, advance]) (by simp [program, s1, advance]) h2]
  rewrite [scalar_step ops _ _ _ _ _ _ _ _
    (by simp [LarkCollective.parked, program, s2, setReg, advance])
    (by simp [program, s2, setReg, advance]) h3]
  rewrite [scalar_step ops _ _ _ _ _ _ _ _
    (by simp [LarkCollective.parked, program, s3, setReg, advance])
    (by simp [program, s3, setReg, advance]) h4]
  rewrite [scalar_step ops _ _ _ _ _ _ _ _
    (by simp [LarkCollective.parked, program, s4, setReg, advance])
    (by simp [program, s4, setReg, advance]) h5]
  rewrite [scalar_step ops _ _ _ _ _ _ _ _
    (by simp [LarkCollective.parked, program, s5, setIndex, advance])
    (by simp [program, s5, setIndex, advance]) h6]
  rfl

theorem component_preserves (ops : Ops α) (input : Nat → Nat → α)
    (row vector component t : Nat) (acc : α) (s : State α) :
    (componentAfter ops input row vector component t acc s).memory = s.memory ∧
    (componentAfter ops input row vector component t acc s).epochs = s.epochs := ⟨rfl, rfl⟩

theorem component_trace (ops : Ops α) (input : Nat → Nat → α)
    (row vector component t : Nat) (acc : α) (s : State α) :
    (componentAfter ops input row vector component t acc s).trace =
      ⟨t, globalCell 1 (scalarAddress row vector component), false, s.epochs t⟩ :: s.trace := rfl

theorem component_fields (ops : Ops α) (input : Nat → Nat → α)
    (row vector component t : Nat) (acc : α) (s : State α) :
    (componentAfter ops input row vector component t acc s).pc t = 10 ∧
    (componentAfter ops input row vector component t acc s).indices t 0 = s.indices t 0 ∧
    (componentAfter ops input row vector component t acc s).indices t 5 = s.indices t 5 ∧
    (componentAfter ops input row vector component t acc s).indices t 6 = some ((component + 1 : Nat) : Int) ∧
    (componentAfter ops input row vector component t acc s).regs t 0 =
      some (ops.add acc (termAt ops input row vector component)) := by
  simp [componentAfter, setIndex, setReg, record, advance]

theorem component_other (ops : Ops α) (input : Nat → Nat → α)
    (row vector component t u : Nat) (acc : α) (s : State α) (hu : u ≠ t) :
    (componentAfter ops input row vector component t acc s).pc u = s.pc u ∧
    (componentAfter ops input row vector component t acc s).indices u = s.indices u ∧
    (componentAfter ops input row vector component t acc s).regs u = s.regs u := by
  simp [componentAfter, setIndex, setReg, record, advance, hu]

theorem component_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row vector component t : Nat) (acc : α) (s : State α)
    (good : ∀ a ∈ s.trace, LarkReductionFootprint.Good (traversal p) 0 a) :
    ∀ a ∈ (componentAfter ops input row vector component t acc s).trace,
      LarkReductionFootprint.Good (traversal p) 0 a := by
  intro a ha
  rewrite [component_trace] at ha
  rcases List.mem_cons.mp ha with he | ht
  · subst a
    exact input_access_good p s t 1 _ (by decide)
  · exact good a ht

#print axioms component_cycle
#print axioms component_fields
#print axioms component_good
end LarkNativeRmsNorm
