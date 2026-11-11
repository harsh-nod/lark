import Lark.NativeFusedRmsNormOutputLane

/-! Output-phase frame and ownership. A lane changes only its sixteen output
cells; all residual, shared, weight and outside cells retain their exact values.
-/
namespace LarkNativeFusedRmsNorm
open LarkNonlinear
open LarkReduction (setIndex setReg)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def OutputWrites (row tid : Nat) (l : Location) : Prop :=
  ∃ j < 16, l = globalCell 0 (flatAddress row tid j)

theorem output_component_frame (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component t : Nat) (inverse : α) (s : State α) (l : Location)
    (hi : iteration < 2) (hc : component < 8) (hl : ¬ OutputWrites row tid l) :
    (outputComponent ops input row tid iteration component t inverse s).memory l = s.memory l := by
  have hn : l ≠ globalCell 0 (address row (column tid iteration component)) := by
    intro h
    apply hl
    refine ⟨iteration * 8 + component, by omega, ?_⟩
    simpa only [flatAddress, slot_rank tid iteration component hc] using h
  simp only [output_component_memory, if_neg hn]

theorem output_components_frame (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t component remaining : Nat) (inverse : α) (s : State α) (l : Location)
    (hi : iteration < 2) (hc : component + remaining ≤ 8) (hl : ¬ OutputWrites row tid l) :
    (outputComponents ops input row tid iteration t inverse component remaining s).memory l = s.memory l := by
  induction remaining generalizing component s with
  | zero => rfl
  | succ remaining ih =>
      exact (ih (component + 1) (outputComponent ops input row tid iteration component t inverse s) (by omega)).trans
        (output_component_frame ops input row tid iteration component t inverse s l hi (by omega) hl)

theorem output_round_frame (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t : Nat) (inverse : α) (s : State α) (l : Location)
    (hi : iteration < 2) (hl : ¬ OutputWrites row tid l) :
    (outputRound ops input row tid iteration t inverse s).memory l = s.memory l :=
  output_components_frame ops input row tid iteration t 0 8 inverse (outputBeginRound t s) l hi (by decide) hl

theorem output_lane_frame (ops : Ops α) (input : Nat → Nat → α)
    (row tid t : Nat) (total : α) (s : State α) (l : Location) (hl : ¬ OutputWrites row tid l) :
    (outputLane ops input row tid t total s).memory l = s.memory l := by
  change (outputBeforeHalt ops input row tid t total s).memory l = s.memory l
  change (outputRound ops input row tid 1 t (outputInverse ops total)
    (outputRound ops input row tid 0 t (outputInverse ops total) (outputEntered ops t row total s))).memory l = s.memory l
  let inverse := outputInverse ops total
  let s0 := outputEntered ops t row total s
  let s1 := outputRound ops input row tid 0 t inverse s0
  have h0 := output_round_frame ops input row tid 0 t inverse s0 l (by decide) hl
  have h1 := output_round_frame ops input row tid 1 t inverse s1 l (by decide) hl
  exact h1.trans (h0.trans (congrArg (fun memory => memory l) (output_entry_preserves ops t row total s).1))

theorem output_lane_residual (ops : Ops α) (input : Nat → Nat → α)
    (row tid t offset : Nat) (total : α) (s : State α) :
    (outputLane ops input row tid t total s).memory (globalCell 1 offset) = s.memory (globalCell 1 offset) :=
  output_lane_frame ops input row tid t total s _ (by rintro ⟨j,hj,he⟩; cases he)

theorem output_lane_shared (ops : Ops α) (input : Nat → Nat → α)
    (row tid t owner buffer offset : Nat) (total : α) (s : State α) :
    (outputLane ops input row tid t total s).memory ⟨.shared,owner,buffer,offset⟩ = s.memory ⟨.shared,owner,buffer,offset⟩ :=
  output_lane_frame ops input row tid t total s _ (by rintro ⟨j,hj,he⟩; cases he)

theorem output_components_epochs (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t component remaining : Nat) (inverse : α) (s : State α) :
    (outputComponents ops input row tid iteration t inverse component remaining s).epochs = s.epochs := by
  induction remaining generalizing component s with
  | zero => rfl
  | succ remaining ih =>
      exact (ih (component + 1) _).trans (output_component_epochs ops input row tid iteration component t inverse s)

theorem output_round_epochs (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t : Nat) (inverse : α) (s : State α) :
    (outputRound ops input row tid iteration t inverse s).epochs = s.epochs :=
  output_components_epochs ops input row tid iteration t 0 8 inverse (outputBeginRound t s)

theorem output_lane_epochs (ops : Ops α) (input : Nat → Nat → α)
    (row tid t : Nat) (total : α) (s : State α) :
    (outputLane ops input row tid t total s).epochs = s.epochs := by
  change (outputBeforeHalt ops input row tid t total s).epochs = s.epochs
  change (outputRound ops input row tid 1 t (outputInverse ops total)
    (outputRound ops input row tid 0 t (outputInverse ops total) (outputEntered ops t row total s))).epochs = s.epochs
  let inverse := outputInverse ops total
  let s0 := outputEntered ops t row total s
  let s1 := outputRound ops input row tid 0 t inverse s0
  have h0 := output_round_epochs ops input row tid 0 t inverse s0
  have h1 := output_round_epochs ops input row tid 1 t inverse s1
  exact h1.trans (h0.trans (output_entry_preserves ops t row total s).2)

theorem output_writes_writer (p : Shape) (row tid t : Nat) (l : Location)
    (ht : tid < 1024) (he : t = row * 1024 + tid) (hl : OutputWrites row tid l) :
    l.space = .global ∧ l.buffer = 0 ∧ writer l.offset = t := by
  obtain ⟨j,hj,rfl⟩ := hl
  exact ⟨rfl,rfl, (address_writer p row tid (j / 8) (j % 8) ht (by omega) (Nat.mod_lt _ (by decide))).trans he.symm⟩

theorem out_ready_output_values (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid : Nat) (s : State α) (ready : OutReady p ops input row s) (ht : tid < 1024) :
    let result := outputLane ops input row tid (row * 1024 + tid) (blockSum ops input row) s
    OutputCompleted ops input row tid (outputInverse ops (blockSum ops input row)) 16 result ∧
    (∀ a ∈ result.trace, Good a) ∧ raceFree (geometry p) result.trace = true := by
  have hrow : (row * 1024 + tid) / 1024 = row := by omega
  have htid : (row * 1024 + tid) % 1024 = tid := by omega
  have inds := ready.indices tid ht
  have values := output_lane_values p ops input row tid (row * 1024 + tid) (blockSum ops input row) s ht rfl
    (by simpa only [hrow] using inds.1) (by simpa only [htid] using inds.2.1)
    (out_ready_reads p ops input row s ready) (ready.epoch tid ht) ready.good
  exact ⟨values.1, values.2.2, race_free p _ values.2.2⟩

#print axioms output_component_frame
#print axioms output_components_frame
#print axioms output_round_frame
#print axioms output_lane_frame
#print axioms output_lane_residual
#print axioms output_lane_shared
#print axioms output_components_epochs
#print axioms output_round_epochs
#print axioms output_lane_epochs
#print axioms output_writes_writer
#print axioms out_ready_output_values
end LarkNativeFusedRmsNorm
