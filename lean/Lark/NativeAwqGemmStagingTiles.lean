import Lark.NativeAwqGemmStagingMemory

/-! Every dense A/B tile cell after the actual middle-barrier resumption.
Writer inverses cover both upstream padded shared layouts and A row tails. -/
namespace LarkNativeAwqGemm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option autoImplicit false
variable {α : Type}
attribute [local irreducible] aLoopState aRoundState aBodyState bChunksState bChunkState bChunkBody bLoopState bRoundState bBodyState stagingState stagingFold

def tileCell (b buffer offset : Nat) : Location := ⟨.shared,b,buffer,offset⟩

theorem block_lane_coordinates (p : Shape) (b lane : Nat) (hl : lane<64) :
    laneId (b*64+lane)=lane ∧ blockId (b*64+lane)=b ∧ b*64+lane∈blockThreads (geometry p) b := by
  refine ⟨?_,?_,?_⟩
  · unfold laneId; omega
  · unfold blockId; omega
  · exact List.mem_map.mpr ⟨lane,by change lane∈List.range 64; exact List.mem_range.mpr hl,rfl⟩

theorem b_owner_coordinates (p : Shape) (row col : Nat) (hr : row<32) (hc : col<tileN p) :
    bOwner p row col<64 ∧ bChunk p row<banks p ∧
      bStoreRow p (bOwner p row col) (bChunk p row)=row ∧ bStoreCol p (bOwner p row col) (col%8)=col := by
  rcases tile_cases p with hn | hn
  all_goals simp only [bOwner,bChunk,bStoreRow,bStoreCol,banks,hn] at *
  all_goals omega

theorem after_middle_a_tile (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b row col : Nat) (s : State α) (hr : row<16) (hc : col<32) :
    (afterMiddleBarrier p ops input tile b s).memory (tileCell b 0 (row*40+col))=
      some (if (b/columnTiles p)*16+row<p.m then
        input 0 (((b/columnTiles p)*16+row)*p.k+tile*32+col) else ops.toHalf (ops.literal 0 1)) := by
  let t := b*64+aOwner row col
  have coordinates := block_lane_coordinates p b (aOwner row col) (a_owner_bound row col hr hc)
  have lane : laneId t=aOwner row col := coordinates.1
  have block : t/64=b := coordinates.2.1
  have owner := a_owner_coordinates row col hc
  have cell : aCell t (col%8)=tileCell b 0 (row*40+col) := by
    change (⟨.shared,t/64,0,aStoreRow (laneId t)*40+aStoreCol (laneId t) (col%8)⟩ : Location)=_
    rw [block,lane,owner.1,owner.2]
    rfl
  have sourceRow : inputRow p t=(b/columnTiles p)*16+row := by
    simp only [inputRow,rowTileId,show blockId t=b from block,lane,owner.1]
  have sourceCol : inputCol t+col%8=col := by rw [input_col_component,lane,owner.2]
  have source : aSourceOffset p tile t (col%8)=((b/columnTiles p)*16+row)*p.k+tile*32+col := by
    simp only [aSourceOffset,aGlobal,sourceRow,sourceCol]
  have value := after_middle_a_value p ops input tile b t (col%8) s coordinates.2.2 (Nat.mod_lt _ (by decide))
  rw [cell,sourceRow,source] at value
  exact value

theorem after_middle_b_tile (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b row col : Nat) (s : State α) (hr : row<32) (hc : col<tileN p) :
    (afterMiddleBarrier p ops input tile b s).memory (tileCell b 1 (row*(tileN p+8)+col))=
      some (input 1 ((tile*32+row)*p.n+(b%columnTiles p)*tileN p+col)) := by
  let t := b*64+bOwner p row col
  have owner := b_owner_coordinates p row col hr hc
  have coordinates := block_lane_coordinates p b (bOwner p row col) owner.1
  have lane : laneId t=bOwner p row col := coordinates.1
  have block : t/64=b := coordinates.2.1
  have cell : bCell p t (bChunk p row) (col%8)=tileCell b 1 (row*(tileN p+8)+col) := by
    change (⟨.shared,t/64,1,bStoreRow p (laneId t) (bChunk p row)*(tileN p+8)+bStoreCol p (laneId t) (col%8)⟩ : Location)=_
    rw [block,lane,owner.2.2.1,owner.2.2.2]
    rfl
  have source : bSourceOffset p tile t (bChunk p row) (col%8)=(tile*32+row)*p.n+(b%columnTiles p)*tileN p+col := by
    simp only [bSourceOffset,bGlobal,columnTileId,show blockId t=b from block,lane,owner.2.2.1,owner.2.2.2]
  have value := after_middle_b_value p ops input tile b t (bChunk p row) (col%8) s coordinates.2.2
    owner.2.1 (Nat.mod_lt _ (by decide))
  rw [cell,source] at value
  exact value

theorem after_middle_a_fragment (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b lane half e : Nat) (s : State α) (hl : lane<64) (hh : half<2) (he : e<4) :
    (afterMiddleBarrier p ops input tile b s).memory (tileCell b 0 (aFragment lane half e))=
      some (if (b/columnTiles p)*16+lane%16<p.m then
        input 0 (((b/columnTiles p)*16+lane%16)*p.k+tile*32+half*16+(lane/16)*4+e)
        else ops.toHalf (ops.literal 0 1)) := by
  have bound : half*16+(lane/16)*4+e<32 := by omega
  have value := after_middle_a_tile p ops input tile b (lane%16) (half*16+(lane/16)*4+e) s
    (Nat.mod_lt _ (by decide)) bound
  simpa only [aFragment,Nat.add_assoc] using value

theorem after_middle_b_fragment (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b lane half bank e : Nat) (s : State α) (hl : lane<64) (hh : half<2) (hb : bank<banks p) (he : e<4) :
    (afterMiddleBarrier p ops input tile b s).memory (tileCell b 1 (bFragment p lane half bank e))=
      some (input 1 ((tile*32+(half*16+(lane/16)*4+e))*p.n+(b%columnTiles p)*tileN p+bank*16+lane%16)) := by
  have row : half*16+(lane/16)*4+e<32 := by omega
  have col : bank*16+lane%16<tileN p := by
    rcases tile_cases p with hn | hn <;> simp only [banks,hn] at hb <;> omega
  have value := after_middle_b_tile p ops input tile b (half*16+(lane/16)*4+e) (bank*16+lane%16) s row col
  simpa only [bFragment,Nat.add_assoc] using value

#print axioms block_lane_coordinates
#print axioms b_owner_coordinates
#print axioms after_middle_a_tile
#print axioms after_middle_b_tile
#print axioms after_middle_a_fragment
#print axioms after_middle_b_fragment
end LarkNativeAwqGemm
