import Lark.NativeAwqGemmOperandBlock

/-! The actual native instruction reads its A/B/C operands from the old
register snapshot and computes the source-ordered sixteen-term dot plus C. -/
namespace LarkNativeAwqGemm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option autoImplicit false
variable {α ι : Type}

theorem matrix_mapM_some (xs : List ι) (f : ι → Option α) (value : ι → α)
    (h : ∀ x∈xs, f x=some (value x)) : xs.mapM f=some (xs.map value) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.mapM_cons,h x (by simp),Option.some_bind,
      ih (by intro t ht; exact h t (List.mem_cons_of_mem x ht)),List.map_cons]
    rfl

theorem matrix_a_lane_bound (row k : Nat) (hr : row<16) (hk : k<16) : LarkMFMA.aLane row k<64 := by
  unfold LarkMFMA.aLane
  omega

theorem matrix_b_lane_bound (k col : Nat) (hk : k<16) (hc : col<16) : LarkMFMA.bLane k col<64 := by
  unfold LarkMFMA.bLane
  omega

theorem a_operand_matrix_source (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b half row k : Nat) (hr : row<16) (hk : k<16) :
    aOperand p ops input tile (b*64+LarkMFMA.aLane row k) half (k%4)=
      aTileValue p ops input tile b row (half*16+k) := by
  have coordinates := block_lane_coordinates p b (LarkMFMA.aLane row k) (matrix_a_lane_bound row k hr hk)
  unfold aOperand
  rw [coordinates.1,coordinates.2.1]
  have rowIndex : LarkMFMA.aLane row k%16=row := by unfold LarkMFMA.aLane; omega
  have component : half*16+(LarkMFMA.aLane row k/16)*4+k%4=half*16+k := by unfold LarkMFMA.aLane; omega
  rw [rowIndex,component]

theorem b_operand_matrix_source (p : Shape) (input : Nat → Nat → α)
    (tile b half bank k col : Nat) (hk : k<16) (hc : col<16) :
    bOperand p input tile (b*64+LarkMFMA.bLane k col) half bank (k%4)=
      bTileValue p input tile b (half*16+k) (bank*16+col) := by
  have coordinates := block_lane_coordinates p b (LarkMFMA.bLane k col) (matrix_b_lane_bound k col hk hc)
  unfold bOperand
  rw [coordinates.1,coordinates.2.1]
  have colIndex : LarkMFMA.bLane k col%16=col := by unfold LarkMFMA.bLane; omega
  have component : half*16+(LarkMFMA.bLane k col/16)*4+k%4=half*16+k := by unfold LarkMFMA.bLane; omega
  rw [colIndex,component]

def matrixDot (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (tile b half bank row col : Nat) : α :=
  LarkMFMA.dot ops (fun k => aTileValue p ops input tile b row (half*16+k))
    (fun k => bTileValue p input tile b (half*16+k) (bank*16+col))

def matrixValue (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b half bank : Nat) (acc : Nat → Nat → α) (t e : Nat) : α :=
  ops.add (matrixDot p ops input tile b half bank (LarkMFMA.outputRow (laneId t) e) (LarkMFMA.outputCol (laneId t))) (acc t e)

theorem matrix_element (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b half bank : Nat) (acc : Nat → Nat → α) (s : State α) (t e : Nat)
    (ht : t∈blockThreads (geometry p) b) (he : e<4)
    (ready : ∀ u∈blockThreads (geometry p) b, OperandReady p ops input tile half bank u s)
    (hc : ∀ u∈blockThreads (geometry p) b, ∀ j, j<4 → s.regs u (bank*4+j)=some (acc u j)) :
    LarkMFMA.mfmaElement ops (geometry p) (blockThreads (geometry p) b)
      (bank*4) (leftBase p half) (rightBase p half bank) (bank*4) s (t,e)=
        some ((t,bank*4+e),matrixValue p ops input tile b half bank acc t e) := by
  have hl := lane_bound t
  have hr : LarkMFMA.outputRow (laneId t) e<16 := by unfold LarkMFMA.outputRow; omega
  have hcol : LarkMFMA.outputCol (laneId t)<16 := Nat.mod_lt _ (by decide)
  have block : t/64=b := block_thread_block p b t ht
  have terms :
      (List.range 16).mapM (fun k => do
        let al := b*64+LarkMFMA.aLane (LarkMFMA.outputRow (laneId t) e) k
        let bl := b*64+LarkMFMA.bLane k (LarkMFMA.outputCol (laneId t))
        if !((blockThreads (geometry p) b).contains al) ∨ !((blockThreads (geometry p) b).contains bl) then none else do
          let av ← s.regs al (leftBase p half+k%4)
          let bv ← s.regs bl (rightBase p half bank+k%4)
          pure (ops.mul (ops.fromHalf av) (ops.fromHalf bv)))=
      some ((List.range 16).map fun k =>
        ops.mul (ops.fromHalf (aTileValue p ops input tile b (LarkMFMA.outputRow (laneId t) e) (half*16+k)))
          (ops.fromHalf (bTileValue p input tile b (half*16+k) (bank*16+LarkMFMA.outputCol (laneId t))))) := by
    apply matrix_mapM_some
    intro k hk
    have kBound := List.mem_range.mp hk
    have aMember := (block_lane_coordinates p b (LarkMFMA.aLane (LarkMFMA.outputRow (laneId t) e) k)
      (matrix_a_lane_bound _ k hr kBound)).2.2
    have bMember := (block_lane_coordinates p b (LarkMFMA.bLane k (LarkMFMA.outputCol (laneId t)))
      (matrix_b_lane_bound k _ kBound hcol)).2.2
    have aRead := (ready _ aMember).a (k%4) (Nat.mod_lt _ (by decide))
    have bRead := (ready _ bMember).b (k%4) (Nat.mod_lt _ (by decide))
    rw [a_operand_matrix_source p ops input tile b half _ k hr kBound] at aRead
    rw [b_operand_matrix_source p input tile b half bank k _ kBound hcol] at bRead
    simp only [List.contains_iff_mem.mpr aMember,List.contains_iff_mem.mpr bMember,Bool.not_true,
      Bool.false_eq_true,or_self,ite_false,aRead,bRead,bind,pure,Option.bind]
  unfold LarkMFMA.mfmaElement
  simp only [geometry,Nat.mod_mod,Nat.div_eq_of_lt (Nat.mod_lt t (by decide : 0<64)),Nat.zero_mul,Nat.add_zero,block]
  simp only [geometry,laneId] at terms
  rw [terms]
  simp only [bind,pure,Option.bind,hc t ht e he]
  rfl

#print axioms matrix_mapM_some
#print axioms matrix_a_lane_bound
#print axioms matrix_b_lane_bound
#print axioms a_operand_matrix_source
#print axioms b_operand_matrix_source
#print axioms matrix_element
end LarkNativeAwqGemm
