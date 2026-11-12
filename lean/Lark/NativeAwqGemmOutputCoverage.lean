import Lark.NativeAwqGemmOutputBlock

/-! Inverse mapping from every dense output cell to its actual source lane
and accumulator register. The original row-tail guards remain in force. -/
namespace LarkNativeAwqGemm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option autoImplicit false

def outputSlot (p : Shape) (offset : Nat) : Nat :=
  ((offset%p.n)%tileN p)/16*4+(offset/p.n)%4

theorem output_column_tile_bound (p : Shape) (col : Nat) (hc : col<p.n) : col/tileN p<columnTiles p := by
  have positive : 0<tileN p := by rcases tile_cases p with h | h <;> omega
  apply (Nat.div_lt_iff_lt_mul positive).mpr
  rw [columns_exact]
  exact hc

theorem writer_coordinates (p : Shape) (offset : Nat) :
    rowTileId p (writer p offset)=(offset/p.n)/16 ∧
      columnTileId p (writer p offset)=(offset%p.n)/tileN p ∧
      laneId (writer p offset)=outputOwner ((offset/p.n)%16) ((offset%p.n)%tileN p) := by
  have hc : offset%p.n<p.n := Nat.mod_lt _ p.n_pos
  have tileBound := output_column_tile_bound p (offset%p.n) hc
  have laneBound : outputOwner ((offset/p.n)%16) ((offset%p.n)%tileN p)<64 := by
    have row : (offset/p.n)%16<16 := Nat.mod_lt _ (by decide)
    have col : ((offset%p.n)%tileN p)%16<16 := Nat.mod_lt _ (by decide)
    unfold outputOwner
    omega
  have block : blockId (writer p offset)=(offset/p.n/16)*columnTiles p+(offset%p.n)/tileN p :=
    dense_row 64 _ _ laneBound
  have lane : laneId (writer p offset)=outputOwner ((offset/p.n)%16) ((offset%p.n)%tileN p) :=
    dense_col 64 _ _ laneBound
  refine ⟨?_,?_,lane⟩
  · unfold rowTileId
    rw [block]
    exact dense_row (columnTiles p) _ _ tileBound
  · unfold columnTileId
    rw [block]
    exact dense_col (columnTiles p) _ _ tileBound

theorem output_slot_bound (p : Shape) (offset : Nat) : outputSlot p offset<4*banks p := by
  have row : (offset/p.n)%4<4 := Nat.mod_lt _ (by decide)
  rcases tile_cases p with hn | hn
  all_goals have col : (offset%p.n)%tileN p<tileN p := Nat.mod_lt _ (by omega)
  all_goals simp only [outputSlot,banks,hn] at *
  all_goals omega

theorem writer_output_row (p : Shape) (offset : Nat) :
    globalOutputRow p (writer p offset) (outputSlot p offset%4)=offset/p.n := by
  have coordinates := writer_coordinates p offset
  have row : (offset/p.n)%16<16 := Nat.mod_lt _ (by decide)
  unfold globalOutputRow
  rw [coordinates.1,coordinates.2.2]
  unfold LarkMFMA.outputRow outputOwner outputSlot
  omega

theorem writer_output_column (p : Shape) (offset : Nat) :
    columnTileId p (writer p offset)*tileN p+
      outputLocalCol (laneId (writer p offset)) (outputSlot p offset/4)=offset%p.n := by
  have coordinates := writer_coordinates p offset
  have row : (offset/p.n)%4<4 := Nat.mod_lt _ (by decide)
  rw [coordinates.2.1,coordinates.2.2]
  unfold outputLocalCol outputOwner outputSlot
  rcases tile_cases p with hn | hn <;> rw [hn] at * <;> omega

theorem writer_output_offset (p : Shape) (offset : Nat) :
    outOffset p (writer p offset) (outputSlot p offset)=offset := by
  have rowIndex := writer_output_row p offset
  have columnIndex := writer_output_column p offset
  change globalOutputRow p (writer p offset) (outputSlot p offset%4)*p.n+
    (columnTileId p (writer p offset)*tileN p+outputLocalCol (laneId (writer p offset)) (outputSlot p offset/4))=offset
  rw [rowIndex,columnIndex]
  simpa only [Nat.mul_comm] using Nat.div_add_mod offset p.n

theorem writer_output_guard (p : Shape) (offset : Nat) (hi : offset<p.m*p.n) :
    globalOutputRow p (writer p offset) (outputSlot p offset%4)<p.m := by
  rw [writer_output_row]
  exact (Nat.div_lt_iff_lt_mul p.n_pos).mpr hi

theorem writer_block_bound (p : Shape) (offset : Nat) (hi : offset<p.m*p.n) :
    blockId (writer p offset)<(geometry p).grid := by
  have row : offset/p.n<p.m := (Nat.div_lt_iff_lt_mul p.n_pos).mpr hi
  have rowTile : offset/p.n/16<rowTiles p := by unfold rowTiles; omega
  have colTile := output_column_tile_bound p (offset%p.n) (Nat.mod_lt _ p.n_pos)
  have lane := writer_coordinates p offset
  have columnPositive := column_tiles_positive p
  have block : blockId (writer p offset)=(offset/p.n/16)*columnTiles p+(offset%p.n)/tileN p := by
    have remainder : columnTileId p (writer p offset)<columnTiles p := column_tile_bound p (writer p offset)
    have reconstruct : rowTileId p (writer p offset)*columnTiles p+columnTileId p (writer p offset)=blockId (writer p offset) := by
      simpa only [rowTileId,columnTileId,Nat.mul_comm] using
        Nat.div_add_mod (blockId (writer p offset)) (columnTiles p)
    rw [lane.1,lane.2.1] at reconstruct
    exact reconstruct.symm
  rw [block]
  exact dense_bound (rowTiles p) (columnTiles p) _ _ rowTile colTile

#print axioms output_column_tile_bound
#print axioms writer_coordinates
#print axioms output_slot_bound
#print axioms writer_output_row
#print axioms writer_output_column
#print axioms writer_output_offset
#print axioms writer_output_guard
#print axioms writer_block_bound
end LarkNativeAwqGemm
