import Lark.NativeAwqGemmAStage

/-! Pointwise shared values and memory frames of the actual complete A stage.
The per-lane statements preserve the later scheduler's A-then-B source order. -/
namespace LarkNativeAwqGemm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option autoImplicit false
variable {α : Type}
attribute [local irreducible] aLoopState aRoundState aBodyState

def aCell (t e : Nat) : Location := sharedCell t 0 (aStoreAddress (laneId t) e)
def aValue (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile t e : Nat) (zero : Bool) : α :=
  if zero then ops.toHalf (ops.literal 0 1) else input 0 (aSourceOffset p tile t e)

theorem a_cells_distinct (t e q : Nat) (different : e≠q) : aCell t e≠aCell t q := by
  intro same
  have offset : aStoreAddress (laneId t) e=aStoreAddress (laneId t) q := congrArg Location.offset same
  unfold aStoreAddress aStoreCol at offset
  exact different (by omega)

theorem a_round_value (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile t e : Nat) (zero : Bool) (s : State α) :
    (aRoundState p ops input tile t e zero s).memory (aCell t e)=some (aValue p ops input tile t e zero) := by
  unfold aRoundState aBodyState
  cases zero with
  | false => exact a_stored_value p input tile t e (advance s t (aLoopPC p false+1))
  | true => exact a_zero_stored_value p ops t e (advance s t (aLoopPC p true+1))

theorem a_round_memory_other (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile t e : Nat) (zero : Bool) (s : State α) (loc : Location) (hl : loc≠aCell t e) :
    (aRoundState p ops input tile t e zero s).memory loc=s.memory loc := by
  have different : loc≠sharedCell t 0 (aStoreAddress (laneId t) e) := hl
  cases zero <;>
    simp [aRoundState,aBodyState,aStored,aZeroStored,written,aLoaded,setIndex,advance,record,different]

theorem a_loop_memory_outside (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile t e n : Nat) (zero : Bool) (s : State α) (loc : Location)
    (hl : ∀ q, e≤q → q<e+n → loc≠aCell t q) :
    (aLoopState p ops input tile t zero e n s).memory loc=s.memory loc := by
  induction n generalizing e s with
  | zero => simp only [aLoopState]
  | succ n ih =>
    rw [aLoopState]
    have rest := ih (e+1) (aRoundState p ops input tile t e zero s)
      (by intro q hlo hhi; exact hl q (by omega) (by omega))
    exact rest.trans (a_round_memory_other p ops input tile t e zero s loc (hl e (by omega) (by omega)))

theorem a_loop_memory_written (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile t e n q : Nat) (zero : Bool) (s : State α) (hlo : e≤q) (hhi : q<e+n) :
    (aLoopState p ops input tile t zero e n s).memory (aCell t q)=some (aValue p ops input tile t q zero) := by
  induction n generalizing e s with
  | zero => omega
  | succ n ih =>
    rw [aLoopState]
    by_cases same : q=e
    · subst q
      have rest := a_loop_memory_outside p ops input tile t (e+1) n zero
        (aRoundState p ops input tile t e zero s) (aCell t e)
        (by intro q hlo hhi; exact a_cells_distinct t e q (by omega))
      exact rest.trans (a_round_value p ops input tile t e zero s)
    · exact ih (e+1) (aRoundState p ops input tile t e zero s) (by omega) (by omega)

theorem a_stage_value (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile t q : Nat) (s : State α) (hq : q<8) :
    (aStageState p ops input tile t s).memory (aCell t q)=
      some (if inputRow p t<p.m then input 0 (aSourceOffset p tile t q) else ops.toHalf (ops.literal 0 1)) := by
  by_cases valid : inputRow p t<p.m
  · rw [aStageState,if_pos valid,if_pos valid]
    exact a_loop_memory_written p ops input tile t 0 8 q false (aEntryState p t false s) (by omega) hq
  · rw [aStageState,if_neg valid,if_neg valid]
    exact a_loop_memory_written p ops input tile t 0 8 q true (aEntryState p t true s) (by omega) hq

theorem a_stage_memory_outside (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile t : Nat) (s : State α) (loc : Location) (hl : ∀ q, q<8 → loc≠aCell t q) :
    (aStageState p ops input tile t s).memory loc=s.memory loc := by
  by_cases valid : inputRow p t<p.m
  · rw [aStageState,if_pos valid]
    exact a_loop_memory_outside p ops input tile t 0 8 false (aEntryState p t false s) loc
      (by intro q hlo hhi; exact hl q hhi)
  · rw [aStageState,if_neg valid]
    exact a_loop_memory_outside p ops input tile t 0 8 true (aEntryState p t true s) loc
      (by intro q hlo hhi; exact hl q hhi)

theorem a_owner_bound (row col : Nat) (hr : row<16) (hc : col<32) : aOwner row col<64 := by
  unfold aOwner
  omega

theorem a_owner_coordinates (row col : Nat) (hc : col<32) :
    aStoreRow (aOwner row col)=row ∧ aStoreCol (aOwner row col) (col%8)=col := by
  unfold aOwner aStoreRow aStoreCol
  omega

def aWriter (loc : Location) : Nat := loc.owner*64+aOwner (loc.offset/40) (loc.offset%40)

theorem a_cell_writer (t e : Nat) (he : e<8) : aWriter (aCell t e)=t := by
  have col := (a_store_coordinates (laneId t) e (lane_bound t) he).2
  have quotient := dense_row 40 (aStoreRow (laneId t)) (aStoreCol (laneId t) e) (by omega)
  have remainder := dense_col 40 (aStoreRow (laneId t)) (aStoreCol (laneId t) e) (by omega)
  change t/64*64+aOwner (denseAddress 40 (aStoreRow (laneId t)) (aStoreCol (laneId t) e)/40)
    (denseAddress 40 (aStoreRow (laneId t)) (aStoreCol (laneId t) e)%40)=t
  rw [quotient,remainder,(a_store_owner (laneId t) e he).1]
  unfold laneId
  omega

#print axioms a_cells_distinct
#print axioms a_round_value
#print axioms a_round_memory_other
#print axioms a_loop_memory_outside
#print axioms a_loop_memory_written
#print axioms a_stage_value
#print axioms a_stage_memory_outside
#print axioms a_owner_bound
#print axioms a_owner_coordinates
#print axioms a_cell_writer
end LarkNativeAwqGemm
