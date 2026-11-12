import Lark.NativeAwqGemmTraceSafety

/-! Actual A/B load/store trace classification through both guarded A
paths, all B element loops and all B chunks at the odd staging epoch. -/
namespace LarkNativeAwqGemm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option autoImplicit false
variable {α : Type}
attribute [local irreducible] aLoopState aRoundState aBodyState bLoopState bRoundState bBodyState bChunkState bChunkBody bChunksState

theorem a_stored_good (p : Shape) (input : Nat → Nat → α) (tile t e : Nat) (s : State α)
    (he : e<8) (good : GoodTrace p s) (odd : (s.epochs t).block%2=1) :
    GoodTrace p (aStored p input tile t e s) := by
  intro a ha
  rw [a_stored_trace] at ha
  rcases List.mem_cons.mp ha with same | rest
  · subst a; exact good_a_event p t e (s.epochs t) he odd
  · rcases List.mem_cons.mp rest with same | member
    · subst a; exact good_input_event p t 0 _ _ (Or.inl rfl)
    · exact good a member

theorem a_zero_stored_good (p : Shape) (ops : Ops α) (t e : Nat) (s : State α)
    (he : e<8) (good : GoodTrace p s) (odd : (s.epochs t).block%2=1) :
    GoodTrace p (aZeroStored p ops t e s) := by
  intro a ha
  rw [a_zero_stored_trace] at ha
  rcases List.mem_cons.mp ha with same | member
  · subst a; exact good_a_event p t e (s.epochs t) he odd
  · exact good a member

theorem a_round_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile t e : Nat) (zero : Bool) (s : State α) (he : e<8) (good : GoodTrace p s)
    (odd : (s.epochs t).block%2=1) : GoodTrace p (aRoundState p ops input tile t e zero s) := by
  unfold aRoundState aBodyState
  cases zero with
  | false => exact a_stored_good p input tile t e _ he good odd
  | true => exact a_zero_stored_good p ops t e _ he good odd

theorem a_loop_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile t e n : Nat) (zero : Bool) (s : State α) (hn : e+n≤8) (good : GoodTrace p s)
    (odd : (s.epochs t).block%2=1) : GoodTrace p (aLoopState p ops input tile t zero e n s) := by
  induction n generalizing e s with
  | zero => simpa only [aLoopState] using good
  | succ n ih =>
    rw [aLoopState]
    exact ih (e+1) _ (by omega) (a_round_good p ops input tile t e zero s (by omega) good odd)
      (by rw [(a_round_frames p ops input tile t e zero s).2]; exact odd)

theorem a_stage_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile t : Nat) (s : State α) (good : GoodTrace p s) (odd : (s.epochs t).block%2=1) :
    GoodTrace p (aStageState p ops input tile t s) := by
  unfold aStageState
  split
  · exact a_loop_good p ops input tile t 0 8 false (aEntryState p t false s) (by decide) good odd
  · exact a_loop_good p ops input tile t 0 8 true (aEntryState p t true s) (by decide) good odd

theorem b_stored_good (p : Shape) (input : Nat → Nat → α) (tile t chunk e : Nat) (s : State α)
    (he : e<8) (good : GoodTrace p s) (odd : (s.epochs t).block%2=1) :
    GoodTrace p (bStored p input tile t chunk e s) := by
  intro a ha
  rw [b_stored_trace] at ha
  rcases List.mem_cons.mp ha with same | rest
  · subst a; exact good_b_event p t chunk e (s.epochs t) he odd
  · rcases List.mem_cons.mp rest with same | member
    · subst a; exact good_input_event p t 1 _ _ (Or.inr rfl)
    · exact good a member

theorem b_round_good (p : Shape) (input : Nat → Nat → α) (tile t chunk e : Nat) (s : State α)
    (he : e<8) (good : GoodTrace p s) (odd : (s.epochs t).block%2=1) :
    GoodTrace p (bRoundState p input tile t chunk e s) := by
  unfold bRoundState bBodyState
  exact b_stored_good p input tile t chunk e _ he good odd

theorem b_loop_good (p : Shape) (input : Nat → Nat → α) (tile t chunk e n : Nat) (s : State α)
    (hn : e+n≤8) (good : GoodTrace p s) (odd : (s.epochs t).block%2=1) :
    GoodTrace p (bLoopState p input tile t chunk e n s) := by
  induction n generalizing e s with
  | zero => simpa only [bLoopState] using good
  | succ n ih =>
    rw [bLoopState]
    exact ih (e+1) _ (by omega) (b_round_good p input tile t chunk e s (by omega) good odd)
      (by rw [(b_round_frames p input tile t chunk e s).2]; exact odd)

theorem b_chunk_good (p : Shape) (input : Nat → Nat → α) (tile t chunk : Nat) (s : State α)
    (good : GoodTrace p s) (odd : (s.epochs t).block%2=1) : GoodTrace p (bChunkState p input tile t chunk s) := by
  unfold bChunkState bChunkBody
  exact b_loop_good p input tile t chunk 0 8 (bEntryState p t chunk s) (by decide) good odd

theorem b_chunks_good (p : Shape) (input : Nat → Nat → α) (tile t chunk n : Nat) (s : State α)
    (good : GoodTrace p s) (odd : (s.epochs t).block%2=1) : GoodTrace p (bChunksState p input tile t chunk n s) := by
  induction n generalizing chunk s with
  | zero => simpa only [bChunksState] using good
  | succ n ih =>
    rw [bChunksState]
    exact ih (chunk+1) _ (b_chunk_good p input tile t chunk s good odd)
      (by rw [(b_chunk_frames p input tile t chunk s).2]; exact odd)

theorem b_stage_good (p : Shape) (input : Nat → Nat → α) (tile t : Nat) (s : State α)
    (good : GoodTrace p s) (odd : (s.epochs t).block%2=1) : GoodTrace p (bStageState p input tile t s) :=
  b_chunks_good p input tile t 0 (banks p) (bStageEntry p t s) good odd

#print axioms a_stored_good
#print axioms a_zero_stored_good
#print axioms a_round_good
#print axioms a_loop_good
#print axioms a_stage_good
#print axioms b_stored_good
#print axioms b_round_good
#print axioms b_loop_good
#print axioms b_chunk_good
#print axioms b_chunks_good
#print axioms b_stage_good
end LarkNativeAwqGemm
