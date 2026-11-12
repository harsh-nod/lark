import Lark.NativeAwqGemmPrefix

/-! Exact scalar index evaluation for the complete source's initial decode.
All intermediate operations retain the existing signed-int32 checks. -/
namespace LarkNativeAwqGemm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option autoImplicit false
variable {α : Type}

def laneId (t : Nat) : Nat := t%64
def blockId (t : Nat) : Nat := t/64
def rowTileId (p : Shape) (t : Nat) : Nat := blockId t/columnTiles p
def columnTileId (p : Shape) (t : Nat) : Nat := blockId t%columnTiles p
def inputRow (p : Shape) (t : Nat) : Nat := rowTileId p t*16+aStoreRow (laneId t)
def inputCol (t : Nat) : Nat := aStoreCol (laneId t) 0
def sharedABase (t : Nat) : Nat := aStoreAddress (laneId t) 0
def globalOutputRow (p : Shape) (t e : Nat) : Nat := rowTileId p t*16+LarkMFMA.outputRow (laneId t) e

structure HeaderIndices (p : Shape) (t : Nat) (s : State α) : Prop where
  lane : s.indices t 0=some ((laneId t : Nat) : Int)
  logicalLane : s.indices t 1=some ((laneId t%32 : Nat) : Int)
  logicalWarp : s.indices t 2=some ((laneId t/32 : Nat) : Int)
  block : s.indices t 3=some ((blockId t : Nat) : Int)
  row : s.indices t 4=some ((rowTileId p t : Nat) : Int)
  column : s.indices t 5=some ((columnTileId p t : Nat) : Int)

theorem header_indices (p : Shape) (t : Nat) (s : State α) : HeaderIndices p t (headerState p t s) := by
  constructor <;> simp [headerState,setIndex,advance,laneId,blockId,rowTileId,columnTileId]

theorem setIndex_header (p : Shape) (t r pc : Nat) (value : Int) (s : State α)
    (h : HeaderIndices p t s) (hr : 6≤r) : HeaderIndices p t (setIndex s t r value pc) := by
  have h0 : (0 : Nat)≠r := by omega
  have h1 : (1 : Nat)≠r := by omega
  have h2 : (2 : Nat)≠r := by omega
  have h3 : (3 : Nat)≠r := by omega
  have h4 : (4 : Nat)≠r := by omega
  have h5 : (5 : Nat)≠r := by omega
  exact {
    lane := by simpa [setIndex,advance,h0] using h.lane
    logicalLane := by simpa [setIndex,advance,h1] using h.logicalLane
    logicalWarp := by simpa [setIndex,advance,h2] using h.logicalWarp
    block := by simpa [setIndex,advance,h3] using h.block
    row := by simpa [setIndex,advance,h4] using h.row
    column := by simpa [setIndex,advance,h5] using h.column }

theorem lane_bound (t : Nat) : laneId t<64 := Nat.mod_lt _ (by decide)

theorem block_bound (p : Shape) (t : Nat) (ht : t<(geometry p).grid*64) :
    blockId t<(geometry p).grid := (Nat.div_lt_iff_lt_mul (by decide : 0<64)).mpr ht

theorem input_row_bound (p : Shape) (t : Nat) (ht : t<(geometry p).grid*64) :
    inputRow p t<2147483648 :=
  prefix_input_row_bound p (blockId t) (laneId t) (block_bound p t ht) (lane_bound t)

theorem global_output_row_bound (p : Shape) (t e : Nat)
    (ht : t<(geometry p).grid*64) (he : e<4) : globalOutputRow p t e<2147483648 :=
  prefix_output_row_bound p (blockId t) (laneId t) e (block_bound p t ht) (lane_bound t) he

theorem eval_input_row (p : Shape) (t : Nat) (s : State α)
    (ht : t<(geometry p).grid*64) (h : HeaderIndices p t s) :
    evalIndex (geometry p) t s
      (.add (.add (.mul (v 4) (c 16)) (.mul (v 2) (c 8))) (.div (v 1) (c 4)))=
        some ((inputRow p t : Nat) : Int) := by
  have bound : rowTileId p t*16+(laneId t/32)*8+(laneId t%32)/4<2147483648 := by
    simpa only [inputRow,aStoreRow,Nat.add_assoc] using input_row_bound p t ht
  have a := eval_nat_mul (geometry p) t (rowTileId p t) 16 s (v 4) (c 16)
    h.row (eval_nat_const _ _ _ _ (by decide)) (by omega)
  have b := eval_nat_mul (geometry p) t (laneId t/32) 8 s (v 2) (c 8)
    h.logicalWarp (eval_nat_const _ _ _ _ (by decide)) (by omega)
  have ab := eval_nat_add (geometry p) t (rowTileId p t*16) ((laneId t/32)*8) s _ _ a b (by omega)
  have d := eval_nat_div (geometry p) t (laneId t%32) 4 s (v 1)
    h.logicalLane (by decide) (by decide)
  have result := eval_nat_add (geometry p) t (rowTileId p t*16+(laneId t/32)*8)
    ((laneId t%32)/4) s _ _ ab d bound
  simpa only [inputRow,aStoreRow,Nat.add_assoc] using result

theorem eval_input_col (p : Shape) (t : Nat) (s : State α) (h : HeaderIndices p t s) :
    evalIndex (geometry p) t s (.mul (.mod (v 1) (c 4)) (c 8))=some ((inputCol t : Nat) : Int) := by
  have hl := lane_bound t
  have a := eval_nat_mod (geometry p) t (laneId t%32) 4 s (v 1)
    h.logicalLane (by decide) (by decide)
  have result := eval_nat_mul (geometry p) t (laneId t%32%4) 8 s _ (c 8) a
    (eval_nat_const _ _ _ _ (by decide)) (by omega)
  simpa only [inputCol,aStoreCol,Nat.add_zero] using result

theorem eval_shared_a_base (p : Shape) (t : Nat) (s : State α)
    (h : HeaderIndices p t s) (hc : s.indices t 7=some ((inputCol t : Nat) : Int)) :
    evalIndex (geometry p) t s
      (.add (.mul (.add (.mul (v 2) (c 8)) (.div (v 1) (c 4))) (c 40)) (v 7))=
        some ((sharedABase t : Nat) : Int) := by
  have hl := lane_bound t
  have row := (a_store_coordinates (laneId t) 0 hl (by decide)).1
  have bound := a_store_bound (laneId t) 0 hl (by decide)
  have a := eval_nat_mul (geometry p) t (laneId t/32) 8 s (v 2) (c 8)
    h.logicalWarp (eval_nat_const _ _ _ _ (by decide)) (by omega)
  have b := eval_nat_div (geometry p) t (laneId t%32) 4 s (v 1)
    h.logicalLane (by decide) (by decide)
  have ab : evalIndex (geometry p) t s (.add (.mul (v 2) (c 8)) (.div (v 1) (c 4)))=
      some ((aStoreRow (laneId t) : Nat) : Int) := by
    exact eval_nat_add (geometry p) t ((laneId t/32)*8) ((laneId t%32)/4) s _ _ a b
      (by unfold aStoreRow at row; omega)
  have times := eval_nat_mul (geometry p) t (aStoreRow (laneId t)) 40 s _ (c 40) ab
    (eval_nat_const _ _ _ _ (by decide)) (by omega)
  have result := eval_nat_add (geometry p) t (aStoreRow (laneId t)*40) (inputCol t) s _ (v 7)
    times hc (by change aStoreRow (laneId t)*40+aStoreCol (laneId t) 0<2147483648
                 unfold aStoreAddress at bound; omega)
  exact result

theorem eval_output_row (p : Shape) (t e : Nat) (s : State α)
    (ht : t<(geometry p).grid*64) (he : e<4) (h : HeaderIndices p t s) :
    evalIndex (geometry p) t s
      (.add (.add (.mul (v 4) (c 16)) (.mul (.div (v 0) (c 16)) (c 4))) (c e))=
        some ((globalOutputRow p t e : Nat) : Int) := by
  have bound : rowTileId p t*16+(laneId t/16)*4+e<2147483648 := by
    simpa only [globalOutputRow,LarkMFMA.outputRow,Nat.mul_comm,Nat.add_assoc] using
      global_output_row_bound p t e ht he
  have a := eval_nat_mul (geometry p) t (rowTileId p t) 16 s (v 4) (c 16)
    h.row (eval_nat_const _ _ _ _ (by decide)) (by omega)
  have b := eval_nat_div (geometry p) t (laneId t) 16 s (v 0) h.lane (by decide) (by decide)
  have b4 := eval_nat_mul (geometry p) t (laneId t/16) 4 s _ (c 4) b
    (eval_nat_const _ _ _ _ (by decide)) (by omega)
  have ab := eval_nat_add (geometry p) t (rowTileId p t*16) ((laneId t/16)*4) s _ _ a b4 (by omega)
  have result := eval_nat_add (geometry p) t (rowTileId p t*16+(laneId t/16)*4) e s _ (c e)
    ab (eval_nat_const _ _ _ _ (by omega)) bound
  simpa only [globalOutputRow,LarkMFMA.outputRow,Nat.mul_comm,Nat.add_assoc] using result

#print axioms header_indices
#print axioms setIndex_header
#print axioms lane_bound
#print axioms block_bound
#print axioms input_row_bound
#print axioms global_output_row_bound
#print axioms eval_input_row
#print axioms eval_input_col
#print axioms eval_shared_a_base
#print axioms eval_output_row
end LarkNativeAwqGemm
