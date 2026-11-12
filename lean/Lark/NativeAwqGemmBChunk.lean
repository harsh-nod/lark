import Lark.NativeAwqGemmBEntry

/-! One complete 39-instruction B chunk, retaining the final failed element
test, chunk increment and outer back edge. -/
namespace LarkNativeAwqGemm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option autoImplicit false
variable {α : Type}
attribute [local irreducible] bLoopState bRoundState bBodyState

theorem b_chunk_increment_site (p : Shape) : (program p)[bExitPC p]?=
    some (.scalar (.index 15 (.add (v 15) (c 1)))) := by
  rw [show bExitPC p=16+4*banks p+20 by unfold bExitPC firstBarrier; omega,staging_site p 20 (by decide)]
  rfl

theorem b_chunk_jump_site (p : Shape) : (program p)[firstBarrier p+22]?=
    some (.scalar (.jump (bChunkPC p))) := by
  rw [show firstBarrier p+22=16+4*banks p+21 by unfold firstBarrier; omega,staging_site p 21 (by decide)]
  rfl

def bChunkBody (p : Shape) (input : Nat → Nat → α) (tile t chunk : Nat) (s : State α) : State α :=
  advance (bLoopState p input tile t chunk 0 8 (bEntryState p t chunk s)) t (bExitPC p)

def bChunkState (p : Shape) (input : Nat → Nat → α) (tile t chunk : Nat) (s : State α) : State α :=
  advance (setIndex (bChunkBody p input tile t chunk s) t 15 ((chunk+1 : Nat) : Int)
    (firstBarrier p+22)) t (bChunkPC p)

theorem b_chunk_body_indices (p : Shape) (input : Nat → Nat → α) (tile t chunk : Nat) (s : State α)
    (h : BOuterIndices p tile t chunk s) : BIndices p tile t chunk 8 (bChunkBody p input tile t chunk s) :=
  b_indices_of_indices p tile t chunk 8 _ _
    (b_loop_indices p input tile t chunk 0 8 (bEntryState p t chunk s) (b_entry_indices p tile t chunk s h)) rfl

theorem b_chunk_eq (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile t chunk extra : Nat) (s : State α) (hk : tile<p.k/32) (hc : chunk<banks p)
    (h : BOuterIndices p tile t chunk s) (reads : Reads p input s) (hp : s.pc t=bChunkPC p) :
    LarkMFMA.runLane ops (layout p) (geometry p) (program p) t (extra+39) s=
      LarkMFMA.runLane ops (layout p) (geometry p) (program p) t extra (bChunkState p input tile t chunk s) := by
  let entered := bEntryState p t chunk s
  let looped := bLoopState p input tile t chunk 0 8 entered
  let body := bChunkBody p input tile t chunk s
  let incremented := setIndex body t 15 ((chunk+1 : Nat) : Int) (firstBarrier p+22)
  have entryIndices : BIndices p tile t chunk 0 entered := b_entry_indices p tile t chunk s h
  have loopIndices : BIndices p tile t chunk 8 looped := b_loop_indices p input tile t chunk 0 8 entered entryIndices
  have loopPC : looped.pc t=bLoopPC p := b_loop_pc p input tile t chunk 0 8 entered (b_entry_pc p t chunk s)
  have bodyIndices : BOuterIndices p tile t chunk body := (b_chunk_body_indices p input tile t chunk s h).outer
  have bodyPC : body.pc t=bExitPC p := by simp [body,bChunkBody,advance]
  have incrementStep := execute_index_of ops p t 15 (firstBarrier p+22) (.add (v 15) (c 1)) body
    ((chunk+1 : Nat) : Int) (eval_chunk_increment p tile t chunk body hc bodyIndices)
    (by rw [bodyPC]; unfold bExitPC; omega)
  rewrite [show extra+39=(extra+35)+4 by omega,b_entry_eq p ops tile t chunk (extra+35) s hc h hp]
  rewrite [show extra+35=(extra+3)+4*8 by omega,
    b_loop_eq p ops input tile t chunk 0 8 (extra+3) entered hk hc (by decide) entryIndices reads (b_entry_pc p t chunk s)]
  change LarkMFMA.runLane ops (layout p) (geometry p) (program p) t (extra+3) looped=_
  rewrite [show extra+3=(extra+2)+1 by omega,b_loop_exit_eq p ops tile t chunk (extra+2) looped loopIndices loopPC]
  change LarkMFMA.runLane ops (layout p) (geometry p) (program p) t (extra+2) body=_
  rewrite [show extra+2=(extra+1)+1 by omega,
    scalar_step p ops t (bExitPC p) (extra+1) _ body incremented (b_chunk_increment_site p) bodyPC incrementStep]
  exact scalar_step p ops t (firstBarrier p+22) extra _ incremented _ (b_chunk_jump_site p)
    (by simp [incremented,setIndex,advance]) (execute_jump ops p t (bChunkPC p) incremented)

theorem b_chunk_outer (p : Shape) (input : Nat → Nat → α) (tile t chunk : Nat) (s : State α)
    (h : BOuterIndices p tile t chunk s) : BOuterIndices p tile t (chunk+1) (bChunkState p input tile t chunk s) :=
  b_outer_of_indices p tile t (chunk+1) _ _
    (b_outer_set_chunk p tile t chunk (chunk+1) (firstBarrier p+22) _ (b_chunk_body_indices p input tile t chunk s h).outer) rfl

theorem b_chunk_pc (p : Shape) (input : Nat → Nat → α) (tile t chunk : Nat) (s : State α) :
    (bChunkState p input tile t chunk s).pc t=bChunkPC p := by simp [bChunkState,advance]

theorem b_chunk_reads (p : Shape) (input : Nat → Nat → α) (tile t chunk : Nat) (s : State α)
    (reads : Reads p input s) : Reads p input (bChunkState p input tile t chunk s) :=
  b_loop_reads p input tile t chunk 0 8 (bEntryState p t chunk s) reads

theorem b_chunk_frames (p : Shape) (input : Nat → Nat → α) (tile t chunk : Nat) (s : State α) :
    (bChunkState p input tile t chunk s).regs=s.regs ∧
      (bChunkState p input tile t chunk s).epochs=s.epochs :=
  b_loop_frames p input tile t chunk 0 8 (bEntryState p t chunk s)

theorem b_chunk_trace_length (p : Shape) (input : Nat → Nat → α) (tile t chunk : Nat) (s : State α) :
    (bChunkState p input tile t chunk s).trace.length=s.trace.length+16 :=
  b_loop_trace_length p input tile t chunk 0 8 (bEntryState p t chunk s)

#print axioms b_chunk_increment_site
#print axioms b_chunk_jump_site
#print axioms b_chunk_body_indices
#print axioms b_chunk_eq
#print axioms b_chunk_outer
#print axioms b_chunk_pc
#print axioms b_chunk_reads
#print axioms b_chunk_frames
#print axioms b_chunk_trace_length
end LarkNativeAwqGemm
