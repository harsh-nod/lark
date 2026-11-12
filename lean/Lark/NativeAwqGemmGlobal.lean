import Lark.NativeAwqGemmAddress

/-! Dense input/weight/output bounds and native output-writer inversion for
the FP16 AWQ departure. These components do not assume complete execution.
-/
namespace LarkNativeAwqGemm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option autoImplicit false

def denseAddress (width row col : Nat) : Nat := row*width+col

theorem dense_bound (rows width row col : Nat) (hr : row<rows) (hc : col<width) :
    denseAddress width row col<rows*width := by
  have hlt := Nat.add_lt_add_left hc (row*width)
  have hle := Nat.mul_le_mul_right width (Nat.succ_le_of_lt hr)
  simp only [Nat.succ_mul] at hle
  exact Nat.lt_of_lt_of_le hlt hle

theorem dense_row (width row col : Nat) (hc : col<width) :
    denseAddress width row col/width=row := by
  have hw : 0<width := by omega
  simpa only [denseAddress,Nat.mul_comm,Nat.add_comm,Nat.div_eq_of_lt hc,Nat.zero_add] using
    Nat.add_mul_div_left col row hw

theorem dense_col (width row col : Nat) (hc : col<width) :
    denseAddress width row col%width=col := by
  simp [denseAddress,Nat.add_mod,Nat.mul_mod,Nat.mod_eq_of_lt hc]

theorem k_component_bound (p : Shape) (tile component : Nat)
    (ht : tile<p.k/32) (hc : component<32) : tile*32+component<p.k := by
  have ha := p.k_aligned
  omega

theorem column_address_bound (p : Shape) (tile col : Nat)
    (ht : tile<columnTiles p) (hc : col<tileN p) : tile*tileN p+col<p.n := by
  have h := dense_bound (columnTiles p) (tileN p) tile col ht hc
  simpa only [denseAddress,columns_exact] using h

def aGlobal (p : Shape) (row tile component : Nat) : Nat := row*p.k+tile*32+component
def bGlobal (p : Shape) (columnTile kTile t chunk e : Nat) : Nat :=
  (kTile*32+bStoreRow p t chunk)*p.n+columnTile*tileN p+bStoreCol p t e
def outputGlobal (p : Shape) (rowTile columnTile t bank e : Nat) : Nat :=
  denseAddress p.n (rowTile*16+LarkMFMA.outputRow t e)
    (columnTile*tileN p+outputLocalCol t bank)

theorem a_global_bound (p : Shape) (row tile component : Nat)
    (hr : row<p.m) (ht : tile<p.k/32) (hc : component<32) :
    aGlobal p row tile component<p.m*p.k := by
  have h := dense_bound p.m p.k row (tile*32+component) hr (k_component_bound p tile component ht hc)
  simpa only [denseAddress,aGlobal,Nat.add_assoc] using h

theorem a_global_int32 (p : Shape) (row tile component : Nat)
    (hr : row<p.m) (ht : tile<p.k/32) (hc : component<32) :
    aGlobal p row tile component<2147483648 :=
  Nat.lt_of_lt_of_le (a_global_bound p row tile component hr ht hc) p.a_bound

theorem b_global_bound (p : Shape) (columnTile kTile t chunk e : Nat)
    (hcol : columnTile<columnTiles p) (hk : kTile<p.k/32)
    (ht : t<64) (hc : chunk<tileN p/16) (he : e<8) :
    bGlobal p columnTile kTile t chunk e<p.k*p.n := by
  have h := b_store_coordinates p t chunk e ht hc he
  have row := k_component_bound p kTile (bStoreRow p t chunk) hk h.1
  have col := column_address_bound p columnTile (bStoreCol p t e) hcol h.2
  have bound := dense_bound p.k p.n (kTile*32+bStoreRow p t chunk)
    (columnTile*tileN p+bStoreCol p t e) row col
  simpa only [denseAddress,bGlobal,Nat.add_assoc] using bound

theorem b_global_int32 (p : Shape) (columnTile kTile t chunk e : Nat)
    (hcol : columnTile<columnTiles p) (hk : kTile<p.k/32)
    (ht : t<64) (hc : chunk<tileN p/16) (he : e<8) :
    bGlobal p columnTile kTile t chunk e<2147483648 :=
  Nat.lt_of_lt_of_le (b_global_bound p columnTile kTile t chunk e hcol hk ht hc he) p.b_bound

theorem output_global_bound (p : Shape) (rowTile columnTile t bank e : Nat)
    (hcol : columnTile<columnTiles p) (ht : t<64) (hb : bank<tileN p/16) (he : e<4)
    (guard : rowTile*16+LarkMFMA.outputRow t e<p.m) :
    outputGlobal p rowTile columnTile t bank e<p.m*p.n := by
  have coordinates := output_coordinates p t bank e ht hb he
  exact dense_bound p.m p.n _ _ guard
    (column_address_bound p columnTile (outputLocalCol t bank) hcol coordinates.2)

theorem output_global_int32 (p : Shape) (rowTile columnTile t bank e : Nat)
    (hcol : columnTile<columnTiles p) (ht : t<64) (hb : bank<tileN p/16) (he : e<4)
    (guard : rowTile*16+LarkMFMA.outputRow t e<p.m) :
    outputGlobal p rowTile columnTile t bank e<2147483648 :=
  Nat.lt_of_lt_of_le (output_global_bound p rowTile columnTile t bank e hcol ht hb he guard) p.out_bound

def writer (p : Shape) (offset : Nat) : Nat :=
  ((offset/p.n/16)*columnTiles p+(offset%p.n)/tileN p)*64+
    outputOwner ((offset/p.n)%16) ((offset%p.n)%tileN p)

theorem output_global_writer (p : Shape) (rowTile columnTile t bank e : Nat)
    (hcol : columnTile<columnTiles p) (ht : t<64) (hb : bank<tileN p/16) (he : e<4) :
    writer p (outputGlobal p rowTile columnTile t bank e)=
      (rowTile*columnTiles p+columnTile)*64+t := by
  have coord := output_coordinates p t bank e ht hb he
  have col := column_address_bound p columnTile (outputLocalCol t bank) hcol coord.2
  have hr : (rowTile*16+LarkMFMA.outputRow t e)/16=rowTile := dense_row 16 rowTile _ coord.1
  have hm : (rowTile*16+LarkMFMA.outputRow t e)%16=LarkMFMA.outputRow t e := dense_col 16 rowTile _ coord.1
  have hc : (columnTile*tileN p+outputLocalCol t bank)/tileN p=columnTile :=
    dense_row (tileN p) columnTile _ coord.2
  have hn : (columnTile*tileN p+outputLocalCol t bank)%tileN p=outputLocalCol t bank :=
    dense_col (tileN p) columnTile _ coord.2
  unfold writer outputGlobal
  rw [dense_row p.n _ _ col,dense_col p.n _ _ col,hr,hm,hc,hn]
  rw [(output_owner t bank e he).1]

#print axioms dense_bound
#print axioms dense_row
#print axioms dense_col
#print axioms k_component_bound
#print axioms column_address_bound
#print axioms a_global_bound
#print axioms a_global_int32
#print axioms b_global_bound
#print axioms b_global_int32
#print axioms output_global_bound
#print axioms output_global_int32
#print axioms output_global_writer
end LarkNativeAwqGemm
