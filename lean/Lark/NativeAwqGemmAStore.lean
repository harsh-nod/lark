import Lark.NativeAwqGemmAIndex

/-! Actual native A-staging store instructions, including guarded input reads,
typed zero padding, source-ordered access events and preserved input memory. -/
namespace LarkNativeAwqGemm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option autoImplicit false
variable {α : Type}

def aSourceOffset (p : Shape) (tile t e : Nat) : Nat :=
  aGlobal p (inputRow p t) tile (inputCol t+e)

def aLoaded (p : Shape) (tile t e : Nat) (s : State α) : State α :=
  record s t (globalCell 0 (aSourceOffset p tile t e)) false

def aStored (p : Shape) (input : Nat → Nat → α) (tile t e : Nat) (s : State α) : State α :=
  written (aLoaded p tile t e s) t (sharedCell t 0 (aStoreAddress (laneId t) e))
    (input 0 (aSourceOffset p tile t e)) (firstBarrier p+5)

def aZeroStored (p : Shape) (ops : Ops α) (t e : Nat) (s : State α) : State α :=
  written s t (sharedCell t 0 (aStoreAddress (laneId t) e))
    (ops.toHalf (ops.literal 0 1)) (firstBarrier p+10)

theorem a_store_execute (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile t e : Nat) (s : State α) (hr : inputRow p t<p.m) (hk : tile<p.k/32) (he : e<8)
    (h : AIndices p tile t e s) (reads : Reads p input s) (hp : s.pc t=firstBarrier p+4) :
    execute ops (layout p) (geometry p) t
      (.store .shared 0 aStageIndex (.load .global 0 (aGlobalIndex p))) s=some (aStored p input tile t e s) := by
  have bound := a_global_bound p (inputRow p t) tile (inputCol t+e) hr hk (a_input_component_bound t e he)
  exact execute_store_of ops p t 0 (firstBarrier p+5) .shared aStageIndex (.load .global 0 (aGlobalIndex p))
    s (aLoaded p tile t e s) ((aStoreAddress (laneId t) e : Nat) : Int)
    (sharedCell t 0 (aStoreAddress (laneId t) e)) (input 0 (aSourceOffset p tile t e))
    (eval_a_stage p tile t e s he h)
    (location_shared_a p t _ true (a_store_bound (laneId t) e (lane_bound t) he))
    (load_global_a ops p t (aSourceOffset p tile t e) s input (aGlobalIndex p) bound reads
      (eval_a_global p tile t e s hr hk he h)) (by omega)

theorem a_zero_store_execute (p : Shape) (ops : Ops α) (tile t e : Nat) (s : State α)
    (he : e<8) (h : AIndices p tile t e s) (hp : s.pc t=firstBarrier p+9) :
    execute ops (layout p) (geometry p) t
      (.store .shared 0 aStageIndex (.un .toHalf (.lit 0 1))) s=some (aZeroStored p ops t e s) := by
  exact execute_store_of ops p t 0 (firstBarrier p+10) .shared aStageIndex (.un .toHalf (.lit 0 1))
    s s ((aStoreAddress (laneId t) e : Nat) : Int) (sharedCell t 0 (aStoreAddress (laneId t) e))
    (ops.toHalf (ops.literal 0 1)) (eval_a_stage p tile t e s he h)
    (location_shared_a p t _ true (a_store_bound (laneId t) e (lane_bound t) he))
    (by simp [evalExpr,applyUnary]) (by omega)

theorem a_store_run (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile t e extra : Nat) (s : State α) (hr : inputRow p t<p.m) (hk : tile<p.k/32) (he : e<8)
    (h : AIndices p tile t e s) (reads : Reads p input s) (hp : s.pc t=firstBarrier p+4) :
    LarkMFMA.runLane ops (layout p) (geometry p) (program p) t (extra+1) s=
      LarkMFMA.runLane ops (layout p) (geometry p) (program p) t extra (aStored p input tile t e s) :=
  scalar_step p ops t (firstBarrier p+4) extra _ s _ (a_store_site p) hp
    (a_store_execute p ops input tile t e s hr hk he h reads hp)

theorem a_zero_store_run (p : Shape) (ops : Ops α) (tile t e extra : Nat) (s : State α)
    (he : e<8) (h : AIndices p tile t e s) (hp : s.pc t=firstBarrier p+9) :
    LarkMFMA.runLane ops (layout p) (geometry p) (program p) t (extra+1) s=
      LarkMFMA.runLane ops (layout p) (geometry p) (program p) t extra (aZeroStored p ops t e s) :=
  scalar_step p ops t (firstBarrier p+9) extra _ s _ (a_zero_store_site p) hp
    (a_zero_store_execute p ops tile t e s he h hp)

theorem a_stored_value (p : Shape) (input : Nat → Nat → α) (tile t e : Nat) (s : State α) :
    (aStored p input tile t e s).memory (sharedCell t 0 (aStoreAddress (laneId t) e))=
      some (input 0 (aSourceOffset p tile t e)) := by simp [aStored,written,advance]

theorem a_zero_stored_value (p : Shape) (ops : Ops α) (t e : Nat) (s : State α) :
    (aZeroStored p ops t e s).memory (sharedCell t 0 (aStoreAddress (laneId t) e))=
      some (ops.toHalf (ops.literal 0 1)) := by simp [aZeroStored,written,advance]

theorem a_stored_trace (p : Shape) (input : Nat → Nat → α) (tile t e : Nat) (s : State α) :
    (aStored p input tile t e s).trace=
      ⟨t,sharedCell t 0 (aStoreAddress (laneId t) e),true,s.epochs t⟩::
        ⟨t,globalCell 0 (aSourceOffset p tile t e),false,s.epochs t⟩::s.trace := rfl

theorem a_zero_stored_trace (p : Shape) (ops : Ops α) (t e : Nat) (s : State α) :
    (aZeroStored p ops t e s).trace=
      ⟨t,sharedCell t 0 (aStoreAddress (laneId t) e),true,s.epochs t⟩::s.trace := rfl

theorem a_stored_indices (p : Shape) (input : Nat → Nat → α) (tile t e : Nat) (s : State α)
    (h : AIndices p tile t e s) : AIndices p tile t e (aStored p input tile t e s) :=
  a_indices_of_indices p tile t e s _ h rfl

theorem a_zero_stored_indices (p : Shape) (ops : Ops α) (tile t e : Nat) (s : State α)
    (h : AIndices p tile t e s) : AIndices p tile t e (aZeroStored p ops t e s) :=
  a_indices_of_indices p tile t e s _ h rfl

theorem a_stored_reads (p : Shape) (input : Nat → Nat → α) (tile t e : Nat) (s : State α)
    (h : Reads p input s) : Reads p input (aStored p input tile t e s) :=
  written_shared_reads p input (aLoaded p tile t e s) t (firstBarrier p+5)
    (sharedCell t 0 (aStoreAddress (laneId t) e)) _ rfl
    (record_reads p input s t (globalCell 0 (aSourceOffset p tile t e)) false h)

theorem a_zero_stored_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t e : Nat) (s : State α) (h : Reads p input s) : Reads p input (aZeroStored p ops t e s) :=
  written_shared_reads p input s t (firstBarrier p+10) (sharedCell t 0 (aStoreAddress (laneId t) e)) _ rfl h

theorem a_stored_frames (p : Shape) (input : Nat → Nat → α) (tile t e : Nat) (s : State α) :
    (aStored p input tile t e s).indices=s.indices ∧ (aStored p input tile t e s).regs=s.regs ∧
      (aStored p input tile t e s).epochs=s.epochs := ⟨rfl,rfl,rfl⟩

theorem a_zero_stored_frames (p : Shape) (ops : Ops α) (t e : Nat) (s : State α) :
    (aZeroStored p ops t e s).indices=s.indices ∧ (aZeroStored p ops t e s).regs=s.regs ∧
      (aZeroStored p ops t e s).epochs=s.epochs := ⟨rfl,rfl,rfl⟩

#print axioms a_store_execute
#print axioms a_zero_store_execute
#print axioms a_store_run
#print axioms a_zero_store_run
#print axioms a_stored_value
#print axioms a_zero_stored_value
#print axioms a_stored_trace
#print axioms a_zero_stored_trace
#print axioms a_stored_indices
#print axioms a_zero_stored_indices
#print axioms a_stored_reads
#print axioms a_zero_stored_reads
#print axioms a_stored_frames
#print axioms a_zero_stored_frames
end LarkNativeAwqGemm
