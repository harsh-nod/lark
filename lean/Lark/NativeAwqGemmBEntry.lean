import Lark.NativeAwqGemmBLoop

/-! The actual outer chunk guard and the three B element-loop assignments. -/
namespace LarkNativeAwqGemm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option autoImplicit false
variable {α : Type}

def bChunkPC (p : Shape) : Nat := firstBarrier p+13

theorem b_chunk_test_site (p : Shape) : (program p)[bChunkPC p]?=
    some (.scalar (.branch (.lt (v 15) (c (banks p))) (middleBarrier p))) := by
  rw [show bChunkPC p=16+4*banks p+12 by unfold bChunkPC firstBarrier; omega,staging_site p 12 (by decide)]
  rfl

theorem b_row_init_site (p : Shape) : (program p)[firstBarrier p+14]?=some (ix 16 (bRowIndex p)) := by
  rw [show firstBarrier p+14=16+4*banks p+13 by unfold firstBarrier; omega,staging_site p 13 (by decide)]
  rfl

theorem b_col_init_site (p : Shape) : (program p)[firstBarrier p+15]?=some (ix 17 (bColIndex p)) := by
  rw [show firstBarrier p+15=16+4*banks p+14 by unfold firstBarrier; omega,staging_site p 14 (by decide)]
  rfl

theorem b_element_init_site (p : Shape) : (program p)[firstBarrier p+16]?=some (ix 18 (c 0)) := by
  rw [show firstBarrier p+16=16+4*banks p+15 by unfold firstBarrier; omega,staging_site p 15 (by decide)]
  rfl

def bEntryRow (p : Shape) (t chunk : Nat) (s : State α) : State α :=
  setIndex (advance s t (firstBarrier p+14)) t 16 ((bStoreRow p (laneId t) chunk : Nat) : Int) (firstBarrier p+15)

def bEntryCol (p : Shape) (t chunk : Nat) (s : State α) : State α :=
  setIndex (bEntryRow p t chunk s) t 17 ((bStoreCol p (laneId t) 0 : Nat) : Int) (firstBarrier p+16)

def bEntryState (p : Shape) (t chunk : Nat) (s : State α) : State α :=
  setIndex (bEntryCol p t chunk s) t 18 0 (bLoopPC p)

theorem b_entry_indices (p : Shape) (tile t chunk : Nat) (s : State α)
    (h : BOuterIndices p tile t chunk s) : BIndices p tile t chunk 0 (bEntryState p t chunk s) := by
  have entered := b_outer_of_indices p tile t chunk s (advance s t (firstBarrier p+14)) h rfl
  have row : BOuterIndices p tile t chunk (bEntryRow p t chunk s) :=
    b_outer_set_high p tile t chunk 16 (firstBarrier p+15) _ _ entered (by decide)
  have col : BOuterIndices p tile t chunk (bEntryCol p t chunk s) :=
    b_outer_set_high p tile t chunk 17 (firstBarrier p+16) _ _ row (by decide)
  exact {outer := b_outer_set_high p tile t chunk 18 (bLoopPC p) 0 _ col (by decide)
         row := by simp [bEntryState,bEntryCol,bEntryRow,setIndex,advance]
         col := by simp [bEntryState,bEntryCol,setIndex,advance]
         element := by simp [bEntryState,setIndex,advance]}

theorem b_entry_eq (p : Shape) (ops : Ops α) (tile t chunk extra : Nat) (s : State α)
    (hc : chunk<banks p) (h : BOuterIndices p tile t chunk s) (hp : s.pc t=bChunkPC p) :
    LarkMFMA.runLane ops (layout p) (geometry p) (program p) t (extra+4) s=
      LarkMFMA.runLane ops (layout p) (geometry p) (program p) t extra (bEntryState p t chunk s) := by
  let entered := advance s t (firstBarrier p+14)
  let row := bEntryRow p t chunk s
  let col := bEntryCol p t chunk s
  have hb : banks p<2147483648 := by rcases banks_cases p with hb | hb <;> omega
  have pred := eval_int_lt_true (geometry p) t s (v 15) (c (banks p)) (chunk : Int) (banks p : Int)
    h.chunkIndex (eval_nat_const _ _ _ _ hb) (by omega)
  have branchStep : execute ops (layout p) (geometry p) t (.branch (.lt (v 15) (c (banks p))) (middleBarrier p)) s=
      some entered := by
    have step := execute_branch_true ops p t (middleBarrier p) (.lt (v 15) (c (banks p))) s pred
    rw [hp] at step
    exact step
  have enteredIndices : BOuterIndices p tile t chunk entered := b_outer_of_indices p tile t chunk s entered h rfl
  have rowStep := execute_index_of ops p t 16 (firstBarrier p+15) (bRowIndex p) entered _
    (eval_b_row p tile t chunk entered hc enteredIndices) (by simp [entered,advance])
  have rowIndices : BOuterIndices p tile t chunk row :=
    b_outer_set_high p tile t chunk 16 (firstBarrier p+15) _ entered enteredIndices (by decide)
  have colStep := execute_index_of ops p t 17 (firstBarrier p+16) (bColIndex p) row _
    (eval_b_col p t row rowIndices.setup.header) (by simp [row,bEntryRow,setIndex,advance])
  have zeroStep := execute_index_of ops p t 18 (bLoopPC p) (c 0) col 0
    (eval_nat_const _ _ _ _ (by decide)) (by simp [col,bEntryCol,bLoopPC,setIndex,advance])
  rewrite [show extra+4=(extra+3)+1 by omega,
    scalar_step p ops t (bChunkPC p) (extra+3) _ s entered (b_chunk_test_site p) hp branchStep]
  rewrite [show extra+3=(extra+2)+1 by omega,
    scalar_step p ops t (firstBarrier p+14) (extra+2) _ entered row (b_row_init_site p)
      (by simp [entered,advance]) rowStep]
  rewrite [show extra+2=(extra+1)+1 by omega,
    scalar_step p ops t (firstBarrier p+15) (extra+1) _ row col (b_col_init_site p)
      (by simp [row,bEntryRow,setIndex,advance]) colStep]
  exact scalar_step p ops t (firstBarrier p+16) extra _ col _ (b_element_init_site p)
    (by simp [col,bEntryCol,setIndex,advance]) zeroStep

theorem b_entry_pc (p : Shape) (t chunk : Nat) (s : State α) :
    (bEntryState p t chunk s).pc t=bLoopPC p := by simp [bEntryState,setIndex,advance]

theorem b_entry_frames (p : Shape) (t chunk : Nat) (s : State α) :
    (bEntryState p t chunk s).memory=s.memory ∧ (bEntryState p t chunk s).trace=s.trace ∧
      (bEntryState p t chunk s).regs=s.regs ∧ (bEntryState p t chunk s).epochs=s.epochs := ⟨rfl,rfl,rfl,rfl⟩

#print axioms b_chunk_test_site
#print axioms b_row_init_site
#print axioms b_col_init_site
#print axioms b_element_init_site
#print axioms b_entry_indices
#print axioms b_entry_eq
#print axioms b_entry_pc
#print axioms b_entry_frames
end LarkNativeAwqGemm
