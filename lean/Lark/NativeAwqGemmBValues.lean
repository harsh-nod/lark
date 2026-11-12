import Lark.NativeAwqGemmBStage

/-! Pointwise B values and frames for the actual full per-lane source stage.
The shared-cell inverse retains both its unique global writer and chunk. -/
namespace LarkNativeAwqGemm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option autoImplicit false
variable {α : Type}
attribute [local irreducible] bChunksState bChunkState bChunkBody bLoopState bRoundState bBodyState

def bKey (p : Shape) (loc : Location) : Nat × Nat × Nat :=
  (loc.owner*64+bOwner p (loc.offset/(tileN p+8)) (loc.offset%(tileN p+8)),
    bChunk p (loc.offset/(tileN p+8)),loc.offset%(tileN p+8)%8)

theorem b_cell_key (p : Shape) (t chunk e : Nat) (he : e<8) : bKey p (bCell p t chunk e)=(t,chunk,e) := by
  have col : bStoreCol p (laneId t) e<tileN p+8 := by
    rcases tile_cases p with hn | hn <;> simp only [bStoreCol,hn] <;> omega
  have quotient := dense_row (tileN p+8) (bStoreRow p (laneId t) chunk) (bStoreCol p (laneId t) e) col
  have remainder := dense_col (tileN p+8) (bStoreRow p (laneId t) chunk) (bStoreCol p (laneId t) e) col
  have owner := b_store_owner p (laneId t) chunk e (lane_bound t) he
  change (t/64*64+bOwner p
      (denseAddress (tileN p+8) (bStoreRow p (laneId t) chunk) (bStoreCol p (laneId t) e)/(tileN p+8))
      (denseAddress (tileN p+8) (bStoreRow p (laneId t) chunk) (bStoreCol p (laneId t) e)%(tileN p+8)),
    bChunk p (denseAddress (tileN p+8) (bStoreRow p (laneId t) chunk) (bStoreCol p (laneId t) e)/(tileN p+8)),
    denseAddress (tileN p+8) (bStoreRow p (laneId t) chunk) (bStoreCol p (laneId t) e)%(tileN p+8)%8)=(t,chunk,e)
  rw [quotient,remainder,owner.1,owner.2.1,owner.2.2]
  rw [show t/64*64+laneId t=t by unfold laneId; omega]

theorem b_chunk_cells_distinct (p : Shape) (t chunk otherChunk e q : Nat)
    (different : chunk≠otherChunk) (he : e<8) (hq : q<8) : bCell p t chunk e≠bCell p t otherChunk q := by
  intro same
  have keys := congrArg (bKey p) same
  rw [b_cell_key p t chunk e he,b_cell_key p t otherChunk q hq] at keys
  exact different (congrArg (fun key => key.2.1) keys)

theorem b_element_cells_distinct (p : Shape) (t chunk e q : Nat)
    (different : e≠q) : bCell p t chunk e≠bCell p t chunk q := by
  intro same
  have offset := congrArg Location.offset same
  change bStoreAddress p (laneId t) chunk e=bStoreAddress p (laneId t) chunk q at offset
  unfold bStoreAddress bStoreCol at offset
  exact different (by omega)

theorem b_round_value (p : Shape) (input : Nat → Nat → α) (tile t chunk e : Nat) (s : State α) :
    (bRoundState p input tile t chunk e s).memory (bCell p t chunk e)=
      some (input 1 (bSourceOffset p tile t chunk e)) := by
  unfold bRoundState bBodyState
  exact b_stored_value p input tile t chunk e (advance s t (bLoopPC p+1))

theorem b_round_memory_other (p : Shape) (input : Nat → Nat → α) (tile t chunk e : Nat) (s : State α)
    (loc : Location) (hl : loc≠bCell p t chunk e) :
    (bRoundState p input tile t chunk e s).memory loc=s.memory loc := by
  unfold bRoundState bBodyState
  exact b_stored_other p input tile t chunk e (advance s t (bLoopPC p+1)) loc hl

theorem b_loop_memory_outside (p : Shape) (input : Nat → Nat → α) (tile t chunk e n : Nat) (s : State α)
    (loc : Location) (hl : ∀ q, e≤q → q<e+n → loc≠bCell p t chunk q) :
    (bLoopState p input tile t chunk e n s).memory loc=s.memory loc := by
  induction n generalizing e s with
  | zero => rw [bLoopState]
  | succ n ih =>
    rw [bLoopState]
    have rest := ih (e+1) (bRoundState p input tile t chunk e s)
      (by intro q hlo hhi; exact hl q (by omega) (by omega))
    exact rest.trans (b_round_memory_other p input tile t chunk e s loc (hl e (by omega) (by omega)))

theorem b_loop_memory_written (p : Shape) (input : Nat → Nat → α) (tile t chunk e n q : Nat) (s : State α)
    (hlo : e≤q) (hhi : q<e+n) :
    (bLoopState p input tile t chunk e n s).memory (bCell p t chunk q)=
      some (input 1 (bSourceOffset p tile t chunk q)) := by
  induction n generalizing e s with
  | zero => omega
  | succ n ih =>
    rw [bLoopState]
    by_cases same : q=e
    · subst q
      have rest := b_loop_memory_outside p input tile t chunk (e+1) n
        (bRoundState p input tile t chunk e s) (bCell p t chunk e)
        (by intro q hlo hhi; exact b_element_cells_distinct p t chunk e q (by omega))
      exact rest.trans (b_round_value p input tile t chunk e s)
    · exact ih (e+1) (bRoundState p input tile t chunk e s) (by omega) (by omega)

theorem b_chunk_memory_outside (p : Shape) (input : Nat → Nat → α) (tile t chunk : Nat) (s : State α)
    (loc : Location) (hl : ∀ q, q<8 → loc≠bCell p t chunk q) :
    (bChunkState p input tile t chunk s).memory loc=s.memory loc := by
  unfold bChunkState bChunkBody
  exact b_loop_memory_outside p input tile t chunk 0 8 (bEntryState p t chunk s) loc
    (by intro q hlo hhi; exact hl q hhi)

theorem b_chunk_value (p : Shape) (input : Nat → Nat → α) (tile t chunk q : Nat) (s : State α) (hq : q<8) :
    (bChunkState p input tile t chunk s).memory (bCell p t chunk q)=
      some (input 1 (bSourceOffset p tile t chunk q)) := by
  unfold bChunkState bChunkBody
  exact b_loop_memory_written p input tile t chunk 0 8 q (bEntryState p t chunk s) (by omega) hq

theorem b_chunks_memory_outside (p : Shape) (input : Nat → Nat → α) (tile t chunk n : Nat) (s : State α)
    (loc : Location) (hl : ∀ c, chunk≤c → c<chunk+n → ∀ q, q<8 → loc≠bCell p t c q) :
    (bChunksState p input tile t chunk n s).memory loc=s.memory loc := by
  induction n generalizing chunk s with
  | zero => rw [bChunksState]
  | succ n ih =>
    rw [bChunksState]
    have rest := ih (chunk+1) (bChunkState p input tile t chunk s)
      (by intro c hlo hhi q hq; exact hl c (by omega) (by omega) q hq)
    exact rest.trans (b_chunk_memory_outside p input tile t chunk s loc (hl chunk (by omega) (by omega)))

theorem b_chunks_memory_written (p : Shape) (input : Nat → Nat → α) (tile t chunk n c q : Nat) (s : State α)
    (hlo : chunk≤c) (hhi : c<chunk+n) (hq : q<8) :
    (bChunksState p input tile t chunk n s).memory (bCell p t c q)=
      some (input 1 (bSourceOffset p tile t c q)) := by
  induction n generalizing chunk s with
  | zero => omega
  | succ n ih =>
    rw [bChunksState]
    by_cases same : c=chunk
    · subst c
      have rest := b_chunks_memory_outside p input tile t (chunk+1) n
        (bChunkState p input tile t chunk s) (bCell p t chunk q)
        (by intro c hlo hhi e he; exact b_chunk_cells_distinct p t chunk c q e (by omega) hq he)
      exact rest.trans (b_chunk_value p input tile t chunk q s hq)
    · exact ih (chunk+1) (bChunkState p input tile t chunk s) (by omega) (by omega)

theorem b_stage_value (p : Shape) (input : Nat → Nat → α) (tile t chunk e : Nat) (s : State α)
    (hc : chunk<banks p) (he : e<8) :
    (bStageState p input tile t s).memory (bCell p t chunk e)=
      some (input 1 (bSourceOffset p tile t chunk e)) := by
  unfold bStageState
  exact b_chunks_memory_written p input tile t 0 (banks p) chunk e (bStageEntry p t s) (by omega) (by omega) he

theorem b_stage_memory_outside (p : Shape) (input : Nat → Nat → α) (tile t : Nat) (s : State α)
    (loc : Location) (hl : ∀ chunk, chunk<banks p → ∀ e, e<8 → loc≠bCell p t chunk e) :
    (bStageState p input tile t s).memory loc=s.memory loc := by
  unfold bStageState
  exact b_chunks_memory_outside p input tile t 0 (banks p) (bStageEntry p t s) loc
    (by intro c hlo hhi e he; exact hl c (by omega) e he)

#print axioms b_cell_key
#print axioms b_chunk_cells_distinct
#print axioms b_element_cells_distinct
#print axioms b_round_value
#print axioms b_round_memory_other
#print axioms b_loop_memory_outside
#print axioms b_loop_memory_written
#print axioms b_chunk_memory_outside
#print axioms b_chunk_value
#print axioms b_chunks_memory_outside
#print axioms b_chunks_memory_written
#print axioms b_stage_value
#print axioms b_stage_memory_outside
end LarkNativeAwqGemm
