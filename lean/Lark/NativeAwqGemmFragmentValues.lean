import Lark.NativeAwqGemmFragmentIndex

/-! Dense shared values persist through register loads and native MFMA.
Both operands retain the exact source half-cell coordinates and padding. -/
namespace LarkNativeAwqGemm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option autoImplicit false
variable {α : Type}

def aTileValue (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (tile b row col : Nat) : α :=
  if (b/columnTiles p)*16+row<p.m then input 0 (((b/columnTiles p)*16+row)*p.k+tile*32+col)
  else ops.toHalf (ops.literal 0 1)

def bTileValue (p : Shape) (input : Nat → Nat → α) (tile b row col : Nat) : α :=
  input 1 ((tile*32+row)*p.n+(b%columnTiles p)*tileN p+col)

def aOperand (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (tile t half e : Nat) : α :=
  aTileValue p ops input tile (blockId t) (laneId t%16) (half*16+(laneId t/16)*4+e)

def bOperand (p : Shape) (input : Nat → Nat → α) (tile t half bank e : Nat) : α :=
  bTileValue p input tile (blockId t) (half*16+(laneId t/16)*4+e) (bank*16+laneId t%16)

structure TileReads (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (tile b : Nat) (s : State α) : Prop where
  a : ∀ row, row<16 → ∀ col, col<32 → s.memory (tileCell b 0 (row*40+col))=some (aTileValue p ops input tile b row col)
  b : ∀ row, row<32 → ∀ col, col<tileN p → s.memory (tileCell b 1 (row*(tileN p+8)+col))=some (bTileValue p input tile b row col)

theorem after_middle_tiles (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (tile b : Nat) (s : State α) :
    TileReads p ops input tile b (afterMiddleBarrier p ops input tile b s) :=
  ⟨fun row hr col hc => after_middle_a_tile p ops input tile b row col s hr hc,
    fun row hr col hc => after_middle_b_tile p ops input tile b row col s hr hc⟩

theorem tile_reads_of_memory (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (tile b : Nat) (s next : State α)
    (h : TileReads p ops input tile b s) (hm : next.memory=s.memory) : TileReads p ops input tile b next := by
  constructor
  · intro row hr col hc; rw [hm]; exact h.a row hr col hc
  · intro row hr col hc; rw [hm]; exact h.b row hr col hc

theorem block_thread_block (p : Shape) (b t : Nat) (ht : t∈blockThreads (geometry p) b) : blockId t=b := by
  rcases List.mem_map.mp ht with ⟨lane,member,rfl⟩
  exact (block_lane_coordinates p b lane (by change lane∈List.range 64 at member; exact List.mem_range.mp member)).2.1

theorem a_operand_read (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b t half e : Nat) (s : State α) (hb : blockId t=b) (hh : half<2) (he : e<4)
    (reads : TileReads p ops input tile b s) :
    s.memory (sharedCell t 0 (aFragment (laneId t) half e))=some (aOperand p ops input tile t half e) := by
  have hl := lane_bound t
  have row : laneId t%16<16 := Nat.mod_lt _ (by decide)
  have col : half*16+(laneId t/16)*4+e<32 := by omega
  have value := reads.a (laneId t%16) row (half*16+(laneId t/16)*4+e) col
  have block : t/64=b := hb
  simpa only [sharedCell,tileCell,aFragment,aOperand,hb,block,Nat.add_assoc] using value

theorem b_operand_read (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b t half bank e : Nat) (s : State α) (hb : blockId t=b) (hh : half<2) (hbank : bank<banks p) (he : e<4)
    (reads : TileReads p ops input tile b s) :
    s.memory (sharedCell t 1 (bFragment p (laneId t) half bank e))=some (bOperand p input tile t half bank e) := by
  have hl := lane_bound t
  have row : half*16+(laneId t/16)*4+e<32 := by omega
  have col : bank*16+laneId t%16<tileN p := by
    rcases tile_cases p with hn | hn <;> simp only [banks,hn] at hbank <;> omega
  have value := reads.b (half*16+(laneId t/16)*4+e) row (bank*16+laneId t%16) col
  have block : t/64=b := hb
  simpa only [sharedCell,tileCell,bFragment,bOperand,hb,block,Nat.add_assoc] using value

#print axioms after_middle_tiles
#print axioms tile_reads_of_memory
#print axioms block_thread_block
#print axioms a_operand_read
#print axioms b_operand_read
end LarkNativeAwqGemm
