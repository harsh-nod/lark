import Lark.NativeAwqGemmBIndex

/-! Actual B input loads and shared stores retain their access order. -/
namespace LarkNativeAwqGemm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option autoImplicit false
variable {α : Type}

def bSourceOffset (p : Shape) (tile t chunk e : Nat) : Nat :=
  bGlobal p (columnTileId p t) tile (laneId t) chunk e
def bCell (p : Shape) (t chunk e : Nat) : Location := sharedCell t 1 (bStoreAddress p (laneId t) chunk e)

theorem location_global_b (p : Shape) (t offset : Nat) (hi : offset<p.k*p.n) :
    location (layout p) (geometry p) t .global 1 (offset : Int) false=some (globalCell 1 offset) := by
  have h0 : ¬(offset : Int)<0 := by omega
  simp [location,layout,globalCell,h0,hi]

theorem location_shared_b (p : Shape) (t offset : Nat) (write : Bool) (hi : offset<32*(tileN p+8)) :
    location (layout p) (geometry p) t .shared 1 (offset : Int) write=some (sharedCell t 1 offset) := by
  have h0 : ¬(offset : Int)<0 := by omega
  simp [location,layout,geometry,sharedCell,h0,hi]

theorem load_global_b (ops : Ops α) (p : Shape) (t offset : Nat) (s : State α)
    (input : Nat → Nat → α) (index : Index) (hi : offset<p.k*p.n) (reads : Reads p input s)
    (he : evalIndex (geometry p) t s index=some (offset : Int)) :
    evalExpr ops (layout p) (geometry p) t (.load .global 1 index) s=
      some (input 1 offset,record s t (globalCell 1 offset) false) := by
  simp only [evalExpr,he,location_global_b p t offset hi,reads.2 offset hi,bind,pure,Option.bind]

def bLoaded (p : Shape) (tile t chunk e : Nat) (s : State α) : State α :=
  record s t (globalCell 1 (bSourceOffset p tile t chunk e)) false

def bStored (p : Shape) (input : Nat → Nat → α) (tile t chunk e : Nat) (s : State α) : State α :=
  written (bLoaded p tile t chunk e s) t (bCell p t chunk e)
    (input 1 (bSourceOffset p tile t chunk e)) (firstBarrier p+19)

theorem b_store_site (p : Shape) : (program p)[firstBarrier p+18]?=
    some (.scalar (.store .shared 1 (bStageIndex p) (.load .global 1 (bGlobalIndex p)))) := by
  rw [show firstBarrier p+18=16+4*banks p+17 by unfold firstBarrier; omega,staging_site p 17 (by decide)]
  rfl

theorem b_store_execute (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile t chunk e : Nat) (s : State α) (hk : tile<p.k/32) (hc : chunk<banks p) (he : e<8)
    (h : BIndices p tile t chunk e s) (reads : Reads p input s) (hp : s.pc t=firstBarrier p+18) :
    execute ops (layout p) (geometry p) t
      (.store .shared 1 (bStageIndex p) (.load .global 1 (bGlobalIndex p))) s=some (bStored p input tile t chunk e s) := by
  have bound := b_global_bound p (columnTileId p t) tile (laneId t) chunk e
    (column_tile_bound p t) hk (lane_bound t) hc he
  exact execute_store_of ops p t 1 (firstBarrier p+19) .shared (bStageIndex p) (.load .global 1 (bGlobalIndex p))
    s (bLoaded p tile t chunk e s) ((bStoreAddress p (laneId t) chunk e : Nat) : Int)
    (bCell p t chunk e) (input 1 (bSourceOffset p tile t chunk e))
    (eval_b_stage p tile t chunk e s hc he h)
    (location_shared_b p t _ true (b_store_bound p (laneId t) chunk e (lane_bound t) hc he))
    (load_global_b ops p t (bSourceOffset p tile t chunk e) s input (bGlobalIndex p) bound reads
      (eval_b_global p tile t chunk e s hk hc he h)) (by omega)

theorem b_store_run (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile t chunk e extra : Nat) (s : State α) (hk : tile<p.k/32) (hc : chunk<banks p) (he : e<8)
    (h : BIndices p tile t chunk e s) (reads : Reads p input s) (hp : s.pc t=firstBarrier p+18) :
    LarkMFMA.runLane ops (layout p) (geometry p) (program p) t (extra+1) s=
      LarkMFMA.runLane ops (layout p) (geometry p) (program p) t extra (bStored p input tile t chunk e s) :=
  scalar_step p ops t (firstBarrier p+18) extra _ s _ (b_store_site p) hp
    (b_store_execute p ops input tile t chunk e s hk hc he h reads hp)

theorem b_stored_value (p : Shape) (input : Nat → Nat → α) (tile t chunk e : Nat) (s : State α) :
    (bStored p input tile t chunk e s).memory (bCell p t chunk e)=some (input 1 (bSourceOffset p tile t chunk e)) := by
  simp [bStored,written,advance]

theorem b_stored_other (p : Shape) (input : Nat → Nat → α) (tile t chunk e : Nat) (s : State α)
    (loc : Location) (hl : loc≠bCell p t chunk e) : (bStored p input tile t chunk e s).memory loc=s.memory loc := by
  simp [bStored,bLoaded,written,advance,record,hl]

theorem b_stored_trace (p : Shape) (input : Nat → Nat → α) (tile t chunk e : Nat) (s : State α) :
    (bStored p input tile t chunk e s).trace=
      ⟨t,bCell p t chunk e,true,s.epochs t⟩::
        ⟨t,globalCell 1 (bSourceOffset p tile t chunk e),false,s.epochs t⟩::s.trace := rfl

theorem b_stored_indices (p : Shape) (input : Nat → Nat → α) (tile t chunk e : Nat) (s : State α)
    (h : BIndices p tile t chunk e s) : BIndices p tile t chunk e (bStored p input tile t chunk e s) :=
  b_indices_of_indices p tile t chunk e s _ h rfl

theorem b_stored_reads (p : Shape) (input : Nat → Nat → α) (tile t chunk e : Nat) (s : State α)
    (h : Reads p input s) : Reads p input (bStored p input tile t chunk e s) :=
  written_shared_reads p input (bLoaded p tile t chunk e s) t (firstBarrier p+19)
    (bCell p t chunk e) _ rfl (record_reads p input s t (globalCell 1 (bSourceOffset p tile t chunk e)) false h)

theorem b_stored_frames (p : Shape) (input : Nat → Nat → α) (tile t chunk e : Nat) (s : State α) :
    (bStored p input tile t chunk e s).indices=s.indices ∧ (bStored p input tile t chunk e s).regs=s.regs ∧
      (bStored p input tile t chunk e s).epochs=s.epochs := ⟨rfl,rfl,rfl⟩

#print axioms location_global_b
#print axioms location_shared_b
#print axioms load_global_b
#print axioms b_store_site
#print axioms b_store_execute
#print axioms b_store_run
#print axioms b_stored_value
#print axioms b_stored_other
#print axioms b_stored_trace
#print axioms b_stored_indices
#print axioms b_stored_reads
#print axioms b_stored_frames
end LarkNativeAwqGemm
