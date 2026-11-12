import Lark.NativeFlashInferRmsNormOutputControl

/-! Values of the explicit output-state transformer, independent of its incoming
controls and registers. These do not assert execution without readiness; they
let later lane folds retain values already established by actual execution.
-/
namespace LarkNativeFlashInferRmsNorm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem output_components_completed (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t component remaining : Nat) (inverse : α) (s : State α)
    (hi : iteration < 2) (hc : component + remaining ≤ 8)
    (done : OutputCompleted ops input row tid inverse (iteration * 8 + component) s) :
    OutputCompleted ops input row tid inverse (iteration * 8 + component + remaining)
      (outputComponents ops input row tid iteration t inverse component remaining s) := by
  induction remaining generalizing component s with
  | zero => simpa only [outputComponents, Nat.add_zero] using done
  | succ remaining ih =>
      have next := output_component_completed ops input row tid iteration component t inverse s hi (by omega) done
      have step := ih (component + 1) (outputComponent ops input row tid iteration component t inverse s) (by omega)
        (by simpa only [Nat.add_assoc] using next)
      simpa only [outputComponents, show iteration * 8 + (component + 1) + remaining = iteration * 8 + component + (remaining + 1) by omega] using step

theorem output_round_completed (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t : Nat) (inverse : α) (s : State α) (hi : iteration < 2)
    (done : OutputCompleted ops input row tid inverse (iteration * 8) s) :
    OutputCompleted ops input row tid inverse ((iteration + 1) * 8)
      (outputRound ops input row tid iteration t inverse s) := by
  have first : OutputCompleted ops input row tid inverse (iteration * 8 + 0) (outputBeginRound t s) := by
    simpa only [Nat.add_zero] using done
  have last := output_components_completed ops input row tid iteration t 0 8 inverse (outputBeginRound t s)
    hi (by decide) first
  simpa only [Nat.add_zero, show (iteration + 1) * 8 = iteration * 8 + 8 by omega] using last

theorem output_lane_completed (ops : Ops α) (input : Nat → Nat → α)
    (row tid t : Nat) (total : α) (s : State α) :
    OutputCompleted ops input row tid (outputInverse ops total) 16 (outputLane ops input row tid t total s) := by
  let inverse := outputInverse ops total
  let s0 := outputEntered ops t row total s
  let s1 := outputRound ops input row tid 0 t inverse s0
  have h0 : OutputCompleted ops input row tid inverse (0 * 8) s0 := by intro j hj; omega
  have h1 := output_round_completed ops input row tid 0 t inverse s0 (by decide) h0
  have h2 := output_round_completed ops input row tid 1 t inverse s1 (by decide) h1
  exact h2

theorem output_lane_reads (ops : Ops α) (input : Nat → Nat → α)
    (row tid t : Nat) (total : α) (s : State α) (reads : OutputReads ops input row s) :
    OutputReads ops input row (outputLane ops input row tid t total s) := by
  intro col hc
  exact ⟨(output_lane_input ops input row tid t (address row col) total s).trans (reads col hc).1,
    (output_lane_frame ops input row tid t total s _ (by rintro ⟨j,hj,he⟩; cases he)).trans (reads col hc).2⟩

theorem output_lane_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid t : Nat) (total : α) (s : State α) (ht : tid < 1024) (he : t = row * 1024 + tid)
    (epoch : (s.epochs t).block = 2) (good : ∀ a ∈ s.trace, Good a) :
    ∀ a ∈ (outputLane ops input row tid t total s).trace, Good a := by
  have hrow : t / 1024 = row := by omega
  have start := output_entry_good ops t row total s hrow epoch good
  have componentGood : ∀ (iteration component remaining : Nat) (inverse : α) (u : State α),
      iteration < 2 → component + remaining ≤ 8 → (∀ a ∈ u.trace, Good a) →
      ∀ a ∈ (outputComponents ops input row tid iteration t inverse component remaining u).trace, Good a := by
    intro iteration component remaining inverse u hi hc hg
    induction remaining generalizing component u with
    | zero => exact hg
    | succ remaining ih =>
        exact ih (component + 1) (outputComponent ops input row tid iteration component t inverse u) (by omega)
          (output_component_good p ops input row tid iteration component t inverse u ht hi (by omega) he hg)
  have roundGood : ∀ (iteration : Nat) (inverse : α) (u : State α), iteration < 2 →
      (∀ a ∈ u.trace, Good a) → ∀ a ∈ (outputRound ops input row tid iteration t inverse u).trace, Good a := by
    intro iteration inverse u hi hg
    exact componentGood iteration 0 8 inverse (outputBeginRound t u) hi (by decide) hg
  exact roundGood 1 (outputInverse ops total)
    (outputRound ops input row tid 0 t (outputInverse ops total) (outputEntered ops t row total s)) (by decide)
    (roundGood 0 (outputInverse ops total) (outputEntered ops t row total s) (by decide) start)

theorem output_writes_unique (p : Shape) (row tid other : Nat) (l : Location)
    (ht : tid < 1024) (hu : other < 1024) (hne : tid ≠ other)
    (hl : OutputWrites row tid l) : ¬ OutputWrites row other l := by
  intro ho
  have h1 := (output_writes_writer p row tid (row * 1024 + tid) l ht rfl hl).2.2
  have h2 := (output_writes_writer p row other (row * 1024 + other) l hu rfl ho).2.2
  omega

#print axioms output_components_completed
#print axioms output_round_completed
#print axioms output_lane_completed
#print axioms output_lane_reads
#print axioms output_lane_good
#print axioms output_writes_unique
end LarkNativeFlashInferRmsNorm
