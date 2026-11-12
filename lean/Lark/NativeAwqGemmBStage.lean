import Lark.NativeAwqGemmBChunk

/-! Complete source B staging: chunk initialization, all four/eight chunks,
and the final failed chunk test reaching the middle block barrier. -/
namespace LarkNativeAwqGemm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option autoImplicit false
variable {α : Type}
attribute [local irreducible] bLoopState bRoundState bBodyState bChunkState bChunkBody

def bChunksState (p : Shape) (input : Nat → Nat → α) (tile t : Nat) : Nat → Nat → State α → State α
  | _,0,s => s
  | chunk,n+1,s => bChunksState p input tile t (chunk+1) n (bChunkState p input tile t chunk s)

theorem b_chunks_outer (p : Shape) (input : Nat → Nat → α) (tile t chunk n : Nat) (s : State α)
    (h : BOuterIndices p tile t chunk s) : BOuterIndices p tile t (chunk+n) (bChunksState p input tile t chunk n s) := by
  induction n generalizing chunk s with
  | zero => exact h
  | succ n ih =>
    have next := ih (chunk+1) (bChunkState p input tile t chunk s) (b_chunk_outer p input tile t chunk s h)
    simpa only [bChunksState,show (chunk+1)+n=chunk+(n+1) by omega] using next

theorem b_chunks_reads (p : Shape) (input : Nat → Nat → α) (tile t chunk n : Nat) (s : State α)
    (h : Reads p input s) : Reads p input (bChunksState p input tile t chunk n s) := by
  induction n generalizing chunk s with
  | zero => exact h
  | succ n ih => exact ih (chunk+1) _ (b_chunk_reads p input tile t chunk s h)

theorem b_chunks_pc (p : Shape) (input : Nat → Nat → α) (tile t chunk n : Nat) (s : State α)
    (hp : s.pc t=bChunkPC p) : (bChunksState p input tile t chunk n s).pc t=bChunkPC p := by
  induction n generalizing chunk s with
  | zero => exact hp
  | succ n ih => exact ih (chunk+1) _ (b_chunk_pc p input tile t chunk s)

theorem b_chunks_frames (p : Shape) (input : Nat → Nat → α) (tile t chunk n : Nat) (s : State α) :
    (bChunksState p input tile t chunk n s).regs=s.regs ∧
      (bChunksState p input tile t chunk n s).epochs=s.epochs := by
  induction n generalizing chunk s with
  | zero => exact ⟨rfl,rfl⟩
  | succ n ih =>
    rw [bChunksState]
    have round := b_chunk_frames p input tile t chunk s
    have rest := ih (chunk+1) (bChunkState p input tile t chunk s)
    exact ⟨rest.1.trans round.1,rest.2.trans round.2⟩

theorem b_chunks_eq (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile t chunk n extra : Nat) (s : State α) (hk : tile<p.k/32) (hn : chunk+n≤banks p)
    (h : BOuterIndices p tile t chunk s) (reads : Reads p input s) (hp : s.pc t=bChunkPC p) :
    LarkMFMA.runLane ops (layout p) (geometry p) (program p) t (extra+39*n) s=
      LarkMFMA.runLane ops (layout p) (geometry p) (program p) t extra (bChunksState p input tile t chunk n s) := by
  induction n generalizing chunk extra s with
  | zero => rfl
  | succ n ih =>
    rewrite [show extra+39*(n+1)=(extra+39*n)+39 by omega,
      b_chunk_eq p ops input tile t chunk (extra+39*n) s hk (by omega) h reads hp]
    rw [bChunksState]
    exact ih (chunk+1) extra (bChunkState p input tile t chunk s) (by omega)
      (b_chunk_outer p input tile t chunk s h) (b_chunk_reads p input tile t chunk s reads)
      (b_chunk_pc p input tile t chunk s)

theorem b_chunks_trace_length (p : Shape) (input : Nat → Nat → α) (tile t chunk n : Nat) (s : State α) :
    (bChunksState p input tile t chunk n s).trace.length=s.trace.length+16*n := by
  induction n generalizing chunk s with
  | zero => simp [bChunksState]
  | succ n ih => rw [bChunksState,ih,b_chunk_trace_length]; omega

theorem b_chunk_init_site (p : Shape) : (program p)[firstBarrier p+12]?=some (ix 15 (c 0)) := by
  rw [show firstBarrier p+12=16+4*banks p+11 by unfold firstBarrier; omega,staging_site p 11 (by decide)]
  rfl

def bStageEntry (p : Shape) (t : Nat) (s : State α) : State α := setIndex s t 15 0 (bChunkPC p)

theorem b_stage_entry_indices (p : Shape) (tile t : Nat) (s : State α)
    (setup : SetupIndices p t s) (ki : s.indices t 13=some (tile : Int)) :
    BOuterIndices p tile t 0 (bStageEntry p t s) := by
  exact {setup := setIndex_setup p t 15 (bChunkPC p) 0 s setup (by decide)
         k := by simpa [bStageEntry,setIndex,advance] using ki
         chunkIndex := by simp [bStageEntry,setIndex,advance]}

theorem b_chunks_exit_eq (p : Shape) (ops : Ops α) (tile t extra : Nat) (s : State α)
    (h : BOuterIndices p tile t (banks p) s) (hp : s.pc t=bChunkPC p) :
    LarkMFMA.runLane ops (layout p) (geometry p) (program p) t (extra+1) s=
      LarkMFMA.runLane ops (layout p) (geometry p) (program p) t extra (advance s t (middleBarrier p)) := by
  have hb : banks p<2147483648 := by rcases banks_cases p with hb | hb <;> omega
  have predicate := eval_int_lt_false (geometry p) t s (v 15) (c (banks p)) (banks p : Int) (banks p : Int)
    h.chunkIndex (eval_nat_const _ _ _ _ hb) (by omega)
  exact scalar_step p ops t (bChunkPC p) extra _ s _ (b_chunk_test_site p) hp
    (execute_branch_false ops p t (middleBarrier p) (.lt (v 15) (c (banks p))) s predicate)

def bStageState (p : Shape) (input : Nat → Nat → α) (tile t : Nat) (s : State α) : State α :=
  advance (bChunksState p input tile t 0 (banks p) (bStageEntry p t s)) t (middleBarrier p)

def bStageCost (p : Shape) : Nat := 2+39*banks p

theorem b_stage_eq (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile t extra : Nat) (s : State α) (hk : tile<p.k/32) (setup : SetupIndices p t s)
    (ki : s.indices t 13=some (tile : Int)) (reads : Reads p input s) (hp : s.pc t=firstBarrier p+12) :
    LarkMFMA.runLane ops (layout p) (geometry p) (program p) t (extra+bStageCost p) s=
      LarkMFMA.runLane ops (layout p) (geometry p) (program p) t extra (bStageState p input tile t s) := by
  let entered := bStageEntry p t s
  let looped := bChunksState p input tile t 0 (banks p) entered
  have ready : BOuterIndices p tile t 0 entered := b_stage_entry_indices p tile t s setup ki
  have entryPC : entered.pc t=bChunkPC p := by simp [entered,bStageEntry,setIndex,advance]
  have loopReady : BOuterIndices p tile t (banks p) looped := by
    simpa only [Nat.zero_add] using b_chunks_outer p input tile t 0 (banks p) entered ready
  have loopPC : looped.pc t=bChunkPC p := b_chunks_pc p input tile t 0 (banks p) entered entryPC
  have initStep := execute_index_of ops p t 15 (bChunkPC p) (c 0) s 0
    (eval_nat_const _ _ _ _ (by decide)) (by rw [hp]; unfold bChunkPC; omega)
  rewrite [show extra+bStageCost p=(extra+1+39*banks p)+1 by unfold bStageCost; omega,
    scalar_step p ops t (firstBarrier p+12) (extra+1+39*banks p) _ s entered (b_chunk_init_site p) hp initStep]
  rewrite [b_chunks_eq p ops input tile t 0 (banks p) (extra+1) entered hk (by omega) ready reads entryPC]
  exact b_chunks_exit_eq p ops tile t extra looped loopReady loopPC

theorem b_stage_pc (p : Shape) (input : Nat → Nat → α) (tile t : Nat) (s : State α) :
    (bStageState p input tile t s).pc t=middleBarrier p := by simp [bStageState,advance]

theorem b_stage_indices (p : Shape) (input : Nat → Nat → α) (tile t : Nat) (s : State α)
    (setup : SetupIndices p t s) (ki : s.indices t 13=some (tile : Int)) :
    BOuterIndices p tile t (banks p) (bStageState p input tile t s) := by
  have ready : BOuterIndices p tile t (banks p) (bChunksState p input tile t 0 (banks p) (bStageEntry p t s)) := by
    simpa only [Nat.zero_add] using
      b_chunks_outer p input tile t 0 (banks p) (bStageEntry p t s) (b_stage_entry_indices p tile t s setup ki)
  exact b_outer_of_indices p tile t (banks p) _ _ ready rfl

theorem b_stage_reads (p : Shape) (input : Nat → Nat → α) (tile t : Nat) (s : State α)
    (reads : Reads p input s) : Reads p input (bStageState p input tile t s) :=
  b_chunks_reads p input tile t 0 (banks p) (bStageEntry p t s) reads

theorem b_stage_frames (p : Shape) (input : Nat → Nat → α) (tile t : Nat) (s : State α) :
    (bStageState p input tile t s).regs=s.regs ∧ (bStageState p input tile t s).epochs=s.epochs :=
  b_chunks_frames p input tile t 0 (banks p) (bStageEntry p t s)

theorem b_stage_trace_length (p : Shape) (input : Nat → Nat → α) (tile t : Nat) (s : State α) :
    (bStageState p input tile t s).trace.length=s.trace.length+16*banks p :=
  b_chunks_trace_length p input tile t 0 (banks p) (bStageEntry p t s)

#print axioms b_chunks_outer
#print axioms b_chunks_reads
#print axioms b_chunks_pc
#print axioms b_chunks_frames
#print axioms b_chunks_eq
#print axioms b_chunks_trace_length
#print axioms b_chunk_init_site
#print axioms b_stage_entry_indices
#print axioms b_chunks_exit_eq
#print axioms b_stage_eq
#print axioms b_stage_pc
#print axioms b_stage_indices
#print axioms b_stage_reads
#print axioms b_stage_frames
#print axioms b_stage_trace_length
end LarkNativeAwqGemm
