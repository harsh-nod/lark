import Lark.NativeAwqGemmKControl

/-! Signed output addresses retain the original row guards, native output
ownership and source register coordinates for every scalar output pair. -/
namespace LarkNativeAwqGemm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option autoImplicit false
variable {α : Type}

def outOffset (p : Shape) (t q : Nat) : Nat :=
  outputGlobal p (rowTileId p t) (columnTileId p t) (laneId t) (q/4) (q%4)
def outCell (p : Shape) (t q : Nat) : Location := globalCell 2 (outOffset p t q)

theorem out_offset_bound (p : Shape) (t q : Nat) (hq : q<4*banks p) (guard : globalOutputRow p t (q%4)<p.m) :
    outOffset p t q<p.m*p.n :=
  output_global_bound p (rowTileId p t) (columnTileId p t) (laneId t) (q/4) (q%4)
    (column_tile_bound p t) (lane_bound t) (by change q/4<banks p; omega) (Nat.mod_lt _ (by decide)) guard

theorem out_offset_signed (p : Shape) (t q : Nat) (hq : q<4*banks p) (guard : globalOutputRow p t (q%4)<p.m) :
    outOffset p t q<2147483648 := Nat.lt_of_lt_of_le (out_offset_bound p t q hq guard) p.out_bound

theorem eval_output_address (p : Shape) (t q : Nat) (s : State α) (hq : q<4*banks p)
    (h : SetupIndices p t s) (guard : globalOutputRow p t (q%4)<p.m) :
    evalIndex (geometry p) t s (outputIndex p (q/4) (q%4))=some ((outOffset p t q : Nat) : Int) := by
  have signed := out_offset_signed p t q hq guard
  have bound : globalOutputRow p t (q%4)*p.n+columnTileId p t*tileN p+(q/4)*16+laneId t%16<2147483648 := by
    simpa only [outOffset,outputGlobal,denseAddress,outputLocalCol,globalOutputRow,Nat.add_assoc] using signed
  have nBound : p.n<2147483648 := by have h := (scalar_parameter_bounds p).2.2; omega
  have tileBound : tileN p<2147483648 := by rcases tile_cases p with hn | hn <;> omega
  have row := eval_nat_mul (geometry p) t (globalOutputRow p t (q%4)) p.n s (v (9+q%4)) (c p.n)
    (h.outputRows (q%4) (Nat.mod_lt _ (by decide))) (eval_nat_const _ _ _ _ nBound) (by omega)
  have col := eval_nat_mul (geometry p) t (columnTileId p t) (tileN p) s (v 5) (c (tileN p))
    h.header.column (eval_nat_const _ _ _ _ tileBound) (by omega)
  have rowCol := eval_nat_add (geometry p) t (globalOutputRow p t (q%4)*p.n) (columnTileId p t*tileN p)
    s _ _ row col (by omega)
  have bank := eval_nat_const (geometry p) t ((q/4)*16) s (by omega)
  have base := eval_nat_add (geometry p) t (globalOutputRow p t (q%4)*p.n+columnTileId p t*tileN p)
    ((q/4)*16) s _ _ rowCol bank (by omega)
  have lane := eval_nat_mod (geometry p) t (laneId t) 16 s (v 0) h.header.lane (by decide) (by decide)
  have result := eval_nat_add (geometry p) t
    (globalOutputRow p t (q%4)*p.n+columnTileId p t*tileN p+(q/4)*16) (laneId t%16) s _ _ base lane bound
  simpa only [outputIndex,outOffset,outputGlobal,denseAddress,outputLocalCol,globalOutputRow,Nat.add_assoc] using result

theorem out_offset_writer (p : Shape) (t q : Nat) (hq : q<4*banks p) : writer p (outOffset p t q)=t := by
  have base : rowTileId p t*columnTiles p+columnTileId p t=blockId t := by
    simpa only [rowTileId,columnTileId,Nat.mul_comm,Nat.add_comm] using Nat.mod_add_div (blockId t) (columnTiles p)
  unfold outOffset
  rw [output_global_writer p (rowTileId p t) (columnTileId p t) (laneId t) (q/4) (q%4)
    (column_tile_bound p t) (lane_bound t) (by change q/4<banks p; omega) (Nat.mod_lt _ (by decide)),base]
  unfold blockId laneId
  omega

theorem out_offset_injective (p : Shape) (t q r : Nat) (hq : q<4*banks p) (hr : r<4*banks p)
    (same : outOffset p t q=outOffset p t r) : q=r := by
  have cq := column_address_bound p (columnTileId p t) (outputLocalCol (laneId t) (q/4))
    (column_tile_bound p t) (output_coordinates p (laneId t) (q/4) (q%4) (lane_bound t)
      (by change q/4<banks p; omega) (Nat.mod_lt _ (by decide))).2
  have cr := column_address_bound p (columnTileId p t) (outputLocalCol (laneId t) (r/4))
    (column_tile_bound p t) (output_coordinates p (laneId t) (r/4) (r%4) (lane_bound t)
      (by change r/4<banks p; omega) (Nat.mod_lt _ (by decide))).2
  have rows := congrArg (fun offset => offset/p.n) same
  have cols := congrArg (fun offset => offset%p.n) same
  simp only [outOffset,outputGlobal,dense_row p.n _ _ cq,dense_row p.n _ _ cr] at rows
  simp only [outOffset,outputGlobal,dense_col p.n _ _ cq,dense_col p.n _ _ cr] at cols
  unfold LarkMFMA.outputRow at rows
  unfold outputLocalCol at cols
  omega

theorem out_cell_injective (p : Shape) (t q r : Nat) (hq : q<4*banks p) (hr : r<4*banks p)
    (same : outCell p t q=outCell p t r) : q=r :=
  out_offset_injective p t q r hq hr (congrArg Location.offset same)

theorem out_cell_different_threads (p : Shape) (t u q r : Nat) (hq : q<4*banks p)
    (hr : r<4*banks p) (different : t≠u) : outCell p t q≠outCell p u r := by
  intro same
  have offsets := congrArg Location.offset same
  have owners := congrArg (writer p) offsets
  change writer p (outOffset p t q)=writer p (outOffset p u r) at owners
  rw [out_offset_writer p t q hq,out_offset_writer p u r hr] at owners
  exact different owners

#print axioms out_offset_injective
#print axioms out_cell_injective
#print axioms out_cell_different_threads
#print axioms out_offset_bound
#print axioms out_offset_signed
#print axioms eval_output_address
#print axioms out_offset_writer
end LarkNativeAwqGemm
