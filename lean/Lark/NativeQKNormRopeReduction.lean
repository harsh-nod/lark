import Lark.NativeQKNormRopeStages

/-! Actual source execution through all five reduction snapshots. The state is
at PC33 with the old accumulator and final peer, before normalization's add. -/
namespace LarkNativeQKNormRope
open LarkNonlinear LarkCollective
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def firstFourState (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (block warp : Nat) (s : State α) : State α :=
  firstStages p ops input block warp 0 4 (prepareFold ops input (cohortThreads block warp 64) s)

theorem first_four_ready (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (block warp : Nat) (s : State α) (hw : warp < 4) :
    WaveReady ops input block warp 4 (firstFourState p ops input block warp s) := by
  apply first_stages_ready p ops input block warp 0 4 _ hw
  intro lane hl
  have h := native_prepare_ready ops input block warp lane s hl
  exact ⟨h.pc, h.accumulator⟩

theorem first_four_preserves (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (block warp : Nat) (s : State α) :
    (firstFourState p ops input block warp s).memory = (prepareFold ops input (cohortThreads block warp 64) s).memory ∧
    (firstFourState p ops input block warp s).indices = (prepareFold ops input (cohortThreads block warp 64) s).indices ∧
    (firstFourState p ops input block warp s).epochs = (prepareFold ops input (cohortThreads block warp 64) s).epochs ∧
    (firstFourState p ops input block warp s).trace = (prepareFold ops input (cohortThreads block warp 64) s).trace := by
  dsimp only [firstFourState]
  exact first_stages_preserves p ops input block warp 0 4 _

theorem native_first_four_step (p : Shape) (neox : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (block warp : Nat) (s : State α) (hb : block < p.rows * 5) (hw : warp < 4)
    (hp : ∀ t ∈ cohortThreads block warp 64, s.pc t = 0) (hr : Reads p input s) :
    LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel (program neox)
      (warpThreads (geometry p) block warp) fuel.warp s =
      continueCohort p neox ops (cohortThreads block warp 64) 11 (firstFourState p ops input block warp s) := by
  rw [show fuel.warp = 15 + 1 by decide, native_prepare_step p neox ops input block warp 15 s hb hw hp hr]
  apply first_stages_run p neox ops input block warp 0 4 11 _ hw (by decide)
  intro lane hl
  have h := native_prepare_ready ops input block warp lane s hl
  exact ⟨h.pc, h.accumulator⟩

def fifthSnapshot (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (block warp : Nat) (s : State α) : State α :=
  shuffleUpdates 9 (xorSnapshot p block warp 64 1 (waveValues ops input block warp 4))
    (firstFourState p ops input block warp s)

theorem fifth_shuffle (p : Shape) (neox : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (block warp : Nat) (s : State α) (hw : warp < 4) :
    LarkPartitionCollective.runShuffle (geometry p) (program neox) (cohortThreads block warp 64)
      (firstFourState p ops input block warp s) = some (fifthSnapshot p ops input block warp s) := by
  have ready := first_four_ready p ops input block warp s hw
  apply cohort_xor_shuffle p neox block warp 64 1 32 9 4 _ _ hw (Or.inr rfl) (by decide)
  · intro lane hl; exact (ready lane hl).1
  · intro lane hl; exact (ready lane hl).2
  · cases neox <;> decide

theorem native_fifth_snapshot (p : Shape) (neox : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (block warp : Nat) (s : State α) (hb : block < p.rows * 5) (hw : warp < 4)
    (hp : ∀ t ∈ cohortThreads block warp 64, s.pc t = 0) (hr : Reads p input s) :
    LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel (program neox)
      (warpThreads (geometry p) block warp) fuel.warp s =
      LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel (program neox)
        (cohortThreads block warp 64) 11 (fifthSnapshot p ops input block warp s) := by
  rw [native_first_four_step p neox ops input block warp s hb hw hp hr]
  have hcohort : LarkPartitionCollective.nextCohort (program neox) (cohortThreads block warp 64)
      (firstFourState p ops input block warp s) = some (cohortThreads block warp 64) := by
    apply cohort_next neox block warp 64 32 _ (by decide)
      (fun lane hl => (first_four_ready p ops input block warp s hw lane hl).1)
    intro t ht
    simp only [LarkPartitionCollective.isShuffle, ht]
    cases neox <;> rfl
  rw [continue_shuffle p neox ops _ _ 11 _ hcohort, fifth_shuffle p neox ops input block warp s hw]
  rfl

theorem fifth_snapshot_fields (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (block warp lane : Nat) (s : State α) (hw : warp < 4) (hl : lane < 64) :
    let t := cohortBase block warp + lane
    let next := fifthSnapshot p ops input block warp s
    next.pc t = 33 ∧ next.regs t 4 = some (waveValues ops input block warp 4 lane) ∧
      next.regs t 9 = some (waveValues ops input block warp 4 (xorPeer32 lane 1)) := by
  have h := xor_shuffled_fields p block warp 64 1 lane 9 (waveValues ops input block warp 4)
    (firstFourState p ops input block warp s) hw (by decide) hl
  have ready := first_four_ready p ops input block warp s hw lane hl
  dsimp only
  refine ⟨?_, ?_, h.2⟩
  · simpa only [ready.1] using h.1
  · exact (xor_shuffled_reg p block warp 64 1 9 _ 4 _ _ (by decide)).trans ready.2

theorem fifth_snapshot_values (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (block warp lane : Nat) (s : State α) (hl : lane < 64) :
    InputValues ops input (cohortBase block warp + lane) (fifthSnapshot p ops input block warp s) := by
  intro r hr
  have hs := xor_shuffled_reg p block warp 64 1 9 (cohortBase block warp + lane) r
    (waveValues ops input block warp 4) (firstFourState p ops input block warp s) (by omega)
  have hi := first_stages_input_reg p ops input block warp 0 4 (cohortBase block warp + lane) r
    (prepareFold ops input (cohortThreads block warp 64) s) hr
  exact hs.trans (hi.trans ((native_prepare_ready ops input block warp lane s hl).values r hr))

theorem fifth_snapshot_preserves (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (block warp : Nat) (s : State α) :
    (fifthSnapshot p ops input block warp s).memory = s.memory ∧
    (fifthSnapshot p ops input block warp s).epochs = s.epochs ∧
    (fifthSnapshot p ops input block warp s).trace = (prepareFold ops input (cohortThreads block warp 64) s).trace := by
  have stages := first_four_preserves p ops input block warp s
  have preparedFrame := prepare_fold_preserves ops input (cohortThreads block warp 64) s
  have snapshotFrame := xor_shuffled_preserves p block warp 64 1 9 (waveValues ops input block warp 4)
    (firstFourState p ops input block warp s)
  exact ⟨snapshotFrame.1.trans (stages.1.trans preparedFrame.1),
    snapshotFrame.2.2.1.trans (stages.2.2.1.trans preparedFrame.2), snapshotFrame.2.2.2.trans stages.2.2.2⟩

theorem fifth_snapshot_indices (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (block warp lane : Nat) (s : State α) (hl : lane < 64) :
    NativeIndices (cohortBase block warp + lane) (fifthSnapshot p ops input block warp s) := by
  have h := first_stages_preserves p ops input block warp 0 4 (prepareFold ops input (cohortThreads block warp 64) s)
  simpa only [NativeIndices, h.2.1] using (native_prepare_ready ops input block warp lane s hl).indices

theorem fifth_snapshot_race_free (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (block warp : Nat) :
    raceFree (geometry p) (fifthSnapshot p ops input block warp (initial (layout p) input outside)).trace = true := by
  rw [(fifth_snapshot_preserves p ops input block warp _).2.2]
  exact native_prepare_race_free p ops input outside block warp

#print axioms first_four_ready
#print axioms first_four_preserves
#print axioms native_first_four_step
#print axioms fifth_shuffle
#print axioms native_fifth_snapshot
#print axioms fifth_snapshot_fields
#print axioms fifth_snapshot_values
#print axioms fifth_snapshot_preserves
#print axioms fifth_snapshot_indices
#print axioms fifth_snapshot_race_free
end LarkNativeQKNormRope
