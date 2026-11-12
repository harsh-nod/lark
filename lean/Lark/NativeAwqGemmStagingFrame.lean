import Lark.NativeAwqGemmStaging

/-! Staging changes only the executing lane's PC and scalar indices. These
frames compose over the actual scheduler without expanding fixed-trip loops. -/
namespace LarkNativeAwqGemm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option autoImplicit false
variable {α : Type}
attribute [local irreducible] aLoopState aRoundState aBodyState bChunksState bChunkState bChunkBody bLoopState bRoundState bBodyState

theorem a_round_other (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile t u e : Nat) (zero : Bool) (s : State α) (hu : u≠t) :
    (aRoundState p ops input tile t e zero s).pc u=s.pc u ∧
      (aRoundState p ops input tile t e zero s).indices u=s.indices u := by
  cases zero <;> constructor
  all_goals simp [aRoundState,aBodyState,aStored,aZeroStored,aLoaded,written,record,setIndex,advance,hu]

theorem a_loop_other (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile t u e n : Nat) (zero : Bool) (s : State α) (hu : u≠t) :
    (aLoopState p ops input tile t zero e n s).pc u=s.pc u ∧
      (aLoopState p ops input tile t zero e n s).indices u=s.indices u := by
  induction n generalizing e s with
  | zero => rw [aLoopState]; exact ⟨rfl,rfl⟩
  | succ n ih =>
    rw [aLoopState]
    have one := a_round_other p ops input tile t u e zero s hu
    have rest := ih (e+1) (aRoundState p ops input tile t e zero s)
    exact ⟨rest.1.trans one.1,rest.2.trans one.2⟩

theorem a_stage_body_other (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile t u : Nat) (zero : Bool) (s : State α) (hu : u≠t) :
    (aStageBody p ops input tile t zero s).pc u=s.pc u ∧
      (aStageBody p ops input tile t zero s).indices u=s.indices u := by
  have loop := a_loop_other p ops input tile t u 0 8 zero (aEntryState p t zero s) hu
  simpa [aStageBody,aEntryState,setIndex,advance,hu] using loop

theorem a_stage_other (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile t u : Nat) (s : State α) (hu : u≠t) :
    (aStageState p ops input tile t s).pc u=s.pc u ∧
      (aStageState p ops input tile t s).indices u=s.indices u := by
  by_cases valid : inputRow p t<p.m
  · simpa only [aStageState,if_pos valid,advance,if_neg hu] using a_stage_body_other p ops input tile t u false s hu
  · simpa only [aStageState,if_neg valid,advance,if_neg hu] using a_stage_body_other p ops input tile t u true s hu

theorem b_round_other (p : Shape) (input : Nat → Nat → α) (tile t u chunk e : Nat) (s : State α) (hu : u≠t) :
    (bRoundState p input tile t chunk e s).pc u=s.pc u ∧
      (bRoundState p input tile t chunk e s).indices u=s.indices u := by
  constructor
  all_goals simp [bRoundState,bBodyState,bStored,bLoaded,written,record,setIndex,advance,hu]

theorem b_loop_other (p : Shape) (input : Nat → Nat → α) (tile t u chunk e n : Nat) (s : State α) (hu : u≠t) :
    (bLoopState p input tile t chunk e n s).pc u=s.pc u ∧
      (bLoopState p input tile t chunk e n s).indices u=s.indices u := by
  induction n generalizing e s with
  | zero => rw [bLoopState]; exact ⟨rfl,rfl⟩
  | succ n ih =>
    rw [bLoopState]
    have one := b_round_other p input tile t u chunk e s hu
    have rest := ih (e+1) (bRoundState p input tile t chunk e s)
    exact ⟨rest.1.trans one.1,rest.2.trans one.2⟩

theorem b_entry_other (p : Shape) (t u chunk : Nat) (s : State α) (hu : u≠t) :
    (bEntryState p t chunk s).pc u=s.pc u ∧ (bEntryState p t chunk s).indices u=s.indices u := by
  constructor
  all_goals simp [bEntryState,bEntryCol,bEntryRow,setIndex,advance,hu]

theorem b_chunk_other (p : Shape) (input : Nat → Nat → α) (tile t u chunk : Nat) (s : State α) (hu : u≠t) :
    (bChunkState p input tile t chunk s).pc u=s.pc u ∧
      (bChunkState p input tile t chunk s).indices u=s.indices u := by
  have entry := b_entry_other p t u chunk s hu
  have loop := b_loop_other p input tile t u chunk 0 8 (bEntryState p t chunk s) hu
  constructor
  · simpa only [bChunkState,bChunkBody,setIndex,advance,if_neg hu] using loop.1.trans entry.1
  · funext q
    simpa only [bChunkState,bChunkBody,setIndex,advance,hu,false_and,ite_false] using congrFun (loop.2.trans entry.2) q

theorem b_chunks_other (p : Shape) (input : Nat → Nat → α) (tile t u chunk n : Nat) (s : State α) (hu : u≠t) :
    (bChunksState p input tile t chunk n s).pc u=s.pc u ∧
      (bChunksState p input tile t chunk n s).indices u=s.indices u := by
  induction n generalizing chunk s with
  | zero => rw [bChunksState]; exact ⟨rfl,rfl⟩
  | succ n ih =>
    rw [bChunksState]
    have one := b_chunk_other p input tile t u chunk s hu
    have rest := ih (chunk+1) (bChunkState p input tile t chunk s)
    exact ⟨rest.1.trans one.1,rest.2.trans one.2⟩

theorem b_stage_other (p : Shape) (input : Nat → Nat → α) (tile t u : Nat) (s : State α) (hu : u≠t) :
    (bStageState p input tile t s).pc u=s.pc u ∧ (bStageState p input tile t s).indices u=s.indices u := by
  have loop := b_chunks_other p input tile t u 0 (banks p) (bStageEntry p t s) hu
  constructor
  · simpa only [bStageState,bStageEntry,setIndex,advance,if_neg hu] using loop.1
  · funext q
    simpa only [bStageState,bStageEntry,setIndex,advance,hu,false_and,ite_false] using congrFun loop.2 q

theorem staging_other (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile t u : Nat) (s : State α) (hu : u≠t) :
    (stagingState p ops input tile t s).pc u=s.pc u ∧ (stagingState p ops input tile t s).indices u=s.indices u := by
  have a := a_stage_other p ops input tile t u s hu
  have b := b_stage_other p input tile t u (aStageState p ops input tile t s) hu
  exact ⟨b.1.trans a.1,b.2.trans a.2⟩

#print axioms a_round_other
#print axioms a_loop_other
#print axioms a_stage_body_other
#print axioms a_stage_other
#print axioms b_round_other
#print axioms b_loop_other
#print axioms b_entry_other
#print axioms b_chunk_other
#print axioms b_chunks_other
#print axioms b_stage_other
#print axioms staging_other
end LarkNativeAwqGemm
