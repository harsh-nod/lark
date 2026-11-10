import Lark.NativeRmsNormOutputComponent

/-! Actual bounded eight-component output loop, including its false guard. -/
namespace LarkNativeRmsNorm
open LarkNonlinear
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem output_exit_eq (p : Shape) (ops : Ops α) (t extra : Nat) (s : State α)
    (hi : s.indices t 8 = some 8) (hp : s.pc t = 60) :
    LarkCollective.runLane ops (layout p) (geometry p) program t (extra + 1) s =
      LarkCollective.runLane ops (layout p) (geometry p) program t extra (advance s t 68) := by
  have hg := LarkReduction.predicate_nlt_of (geometry p) t s (.ivar 8) (.const 8) 8 8 hi (by rfl) (by omega)
  have he : execute ops (layout p) (geometry p) t (.branch (.lt (.ivar 8) (.const 8)) 68) s =
      some (advance s t 68) := by
    simp only [execute, hg, bind, pure, Option.bind]
    rfl
  exact output_scalar_step p ops t 60 extra _ s _ (output_codes 0 (by decide)) hp he

def outputComponents (ops : Ops α) (input : Nat → Nat → α) (row vector t : Nat) (inverse : α) :
    Nat → Nat → State α → State α
  | _, 0, s => advance s t 68
  | component, remaining + 1, s => outputComponents ops input row vector t inverse (component + 1) remaining
      (outputComponent ops input row vector component t inverse s)

theorem output_components_eq (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row vector component remaining t extra : Nat) (inverse : α) (s : State α)
    (stop : component + remaining = 8) (reads : Reads p input s) (hr : row < p.rows) (hv : vector < 2048)
    (hi0 : s.indices t 0 = some (row : Int)) (hi7 : s.indices t 7 = some (vector : Int))
    (hi8 : s.indices t 8 = some (component : Int)) (hx : s.regs t 4 = some inverse) (hp : s.pc t = 60) :
    LarkCollective.runLane ops (layout p) (geometry p) program t (extra + 8 * remaining + 1) s =
      LarkCollective.runLane ops (layout p) (geometry p) program t extra
        (outputComponents ops input row vector t inverse component remaining s) := by
  induction remaining generalizing component s with
  | zero =>
      have he : component = 8 := by omega
      subst component
      exact output_exit_eq p ops t extra s hi8 hp
  | succ remaining ih =>
      have hc : component < 8 := by omega
      have hf := output_component_fields ops input row vector component t inverse s
      rewrite [show extra + 8 * (remaining + 1) + 1 = (extra + 8 * remaining + 1) + 8 by omega,
        output_component_cycle p ops input row vector component t (extra + 8 * remaining + 1)
          inverse s reads hr hv hc hi0 hi7 hi8 hx hp]
      exact ih (component + 1) (outputComponent ops input row vector component t inverse s) (by omega)
        (output_component_reads p ops input row vector component t inverse s reads)
        (hf.2.1.trans hi0) (hf.2.2.1.trans hi7) hf.2.2.2.1 (hf.2.2.2.2.1.trans hx) hf.1

theorem output_components_fields (ops : Ops α) (input : Nat → Nat → α)
    (row vector t component remaining : Nat) (inverse : α) (s : State α) :
    (outputComponents ops input row vector t inverse component remaining s).pc t = 68 ∧
    (outputComponents ops input row vector t inverse component remaining s).indices t 0 = s.indices t 0 ∧
    (outputComponents ops input row vector t inverse component remaining s).indices t 7 = s.indices t 7 ∧
    (outputComponents ops input row vector t inverse component remaining s).regs t 4 = s.regs t 4 ∧
    (outputComponents ops input row vector t inverse component remaining s).epochs = s.epochs := by
  induction remaining generalizing component s with
  | zero => exact ⟨by simp [outputComponents, advance], rfl, rfl, rfl, rfl⟩
  | succ remaining ih =>
      have h := ih (component + 1) (outputComponent ops input row vector component t inverse s)
      have h1 := output_component_fields ops input row vector component t inverse s
      exact ⟨h.1, h.2.1.trans h1.2.1, h.2.2.1.trans h1.2.2.1,
        h.2.2.2.1.trans h1.2.2.2.2.1, h.2.2.2.2.trans h1.2.2.2.2.2⟩

theorem output_components_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row vector t component remaining : Nat) (inverse : α) (s : State α) (reads : Reads p input s) :
    Reads p input (outputComponents ops input row vector t inverse component remaining s) := by
  induction remaining generalizing component s with
  | zero => exact reads
  | succ remaining ih => exact ih (component + 1) _ (output_component_reads p ops input row vector component t inverse s reads)

theorem output_components_memory_other (ops : Ops α) (input : Nat → Nat → α)
    (row vector t component remaining : Nat) (inverse : α) (s : State α) (l : Location)
    (hl : ∀ c, component ≤ c → c < component + remaining → l ≠ globalCell 0 (scalarAddress row vector c)) :
    (outputComponents ops input row vector t inverse component remaining s).memory l = s.memory l := by
  induction remaining generalizing component s with
  | zero => rfl
  | succ remaining ih =>
      have h := ih (component + 1) (outputComponent ops input row vector component t inverse s)
        (by intro c hc hb; exact hl c (by omega) (by omega))
      rewrite [output_component_memory, if_neg (hl component (by omega) (by omega))] at h
      exact h

theorem output_components_other (ops : Ops α) (input : Nat → Nat → α)
    (row vector t u component remaining : Nat) (inverse : α) (s : State α) (hu : u ≠ t) :
    (outputComponents ops input row vector t inverse component remaining s).pc u = s.pc u ∧
    (outputComponents ops input row vector t inverse component remaining s).indices u = s.indices u ∧
    (outputComponents ops input row vector t inverse component remaining s).regs u = s.regs u := by
  induction remaining generalizing component s with
  | zero => exact ⟨by simp [outputComponents, advance, hu], rfl, rfl⟩
  | succ remaining ih =>
      have h := ih (component + 1) (outputComponent ops input row vector component t inverse s)
      have h1 := output_component_other ops input row vector component t u inverse s hu
      exact ⟨h.1.trans h1.1, h.2.1.trans h1.2.1, h.2.2.trans h1.2.2⟩

theorem scalar_component_ne (row vector a b : Nat) (hab : a ≠ b) :
    globalCell 0 (scalarAddress row vector a) ≠ globalCell 0 (scalarAddress row vector b) := by
  intro he
  have he := congrArg Location.offset he
  simp only [globalCell, scalarAddress] at he
  omega

theorem output_components_value (ops : Ops α) (input : Nat → Nat → α)
    (row vector t component remaining c : Nat) (inverse : α) (s : State α)
    (hc : component ≤ c) (hb : c < component + remaining) :
    (outputComponents ops input row vector t inverse component remaining s).memory
      (globalCell 0 (scalarAddress row vector c)) =
        some (ops.toHalf (outputWeighted ops input row vector c inverse)) := by
  induction remaining generalizing component s with
  | zero => omega
  | succ remaining ih =>
      by_cases he : c = component
      · subst c
        have hf := output_components_memory_other ops input row vector t (component + 1) remaining inverse
          (outputComponent ops input row vector component t inverse s) (globalCell 0 (scalarAddress row vector component))
          (by intro c hc hb; exact scalar_component_ne row vector component c (by omega))
        exact hf.trans (by rewrite [output_component_memory, if_pos rfl]; rfl)
      · exact ih (component + 1) (outputComponent ops input row vector component t inverse s) (by omega) (by omega)

theorem output_components_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row vector t component remaining : Nat) (inverse : α) (s : State α)
    (stop : component + remaining = 8) (hv : vector < 2048) (ht : t = row * 1024 + vector % 1024)
    (good : ∀ a ∈ s.trace, LarkReductionFootprint.Good (traversal p) 0 a) :
    ∀ a ∈ (outputComponents ops input row vector t inverse component remaining s).trace,
      LarkReductionFootprint.Good (traversal p) 0 a := by
  induction remaining generalizing component s with
  | zero => exact good
  | succ remaining ih =>
      exact ih (component + 1) _ (by omega)
        (output_component_good p ops input row vector component t inverse s hv (by omega) ht good)

#print axioms output_components_eq
#print axioms output_components_fields
#print axioms output_components_memory_other
#print axioms output_components_value
#print axioms output_components_good
end LarkNativeRmsNorm
