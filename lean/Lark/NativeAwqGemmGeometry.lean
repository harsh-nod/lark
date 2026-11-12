import Lark.NativeAwqGemmProgram

/-! Universal launch and signed scalar-prefix bounds derived from Shape.
No additional shape restriction or larger machine fuel is introduced. -/
namespace LarkNativeAwqGemm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option autoImplicit false

theorem k_minimum (p : Shape) : 32≤p.k := by
  have hp := p.k_pos
  have ha := p.k_aligned
  omega

theorem n_minimum (p : Shape) : 64≤p.n := by
  have hp := p.n_pos
  have ha := p.n_aligned
  omega

theorem scalar_parameter_bounds (p : Shape) :
    p.m+15<2147483648 ∧ p.k<2147483648 ∧ p.n+8<2147483648 := by
  have hm := Nat.le_trans (Nat.mul_le_mul_left p.m (k_minimum p)) p.a_bound
  have hk := Nat.le_trans (Nat.mul_le_mul_left p.k (n_minimum p)) p.b_bound
  have hn := Nat.le_trans (Nat.mul_le_mul_right p.n (k_minimum p)) p.b_bound
  omega

theorem row_tiles_le_rows (p : Shape) : rowTiles p≤p.m := by
  have hp := p.m_pos
  unfold rowTiles
  omega

theorem column_threads_bound (p : Shape) : columnTiles p*64≤p.n := by
  have ht : 64≤tileN p := by rcases tile_cases p with h | h <;> omega
  exact Nat.le_trans (Nat.mul_le_mul_left (columnTiles p) ht) (Nat.le_of_eq (columns_exact p))

theorem grid_threads_bound (p : Shape) : (geometry p).grid*64≤p.m*p.n := by
  change (rowTiles p*columnTiles p)*64≤p.m*p.n
  rw [Nat.mul_assoc]
  exact Nat.le_trans (Nat.mul_le_mul_left (rowTiles p) (column_threads_bound p))
    (Nat.mul_le_mul_right p.n (row_tiles_le_rows p))

theorem thread_int32 (p : Shape) (t : Nat) (ht : t<(geometry p).grid*64) :
    t<2147483648 :=
  Nat.lt_of_lt_of_le ht (Nat.le_trans (grid_threads_bound p) p.out_bound)

theorem block_coordinates (p : Shape) (block : Nat) (hb : block<(geometry p).grid) :
    block/columnTiles p<rowTiles p ∧ block%columnTiles p<columnTiles p := by
  have positive := column_tiles_positive p
  change block<rowTiles p*columnTiles p at hb
  constructor
  · exact (Nat.div_lt_iff_lt_mul positive).mpr hb
  · exact Nat.mod_lt _ positive

theorem padded_row_bound (p : Shape) (rowTile row : Nat)
    (hb : rowTile<rowTiles p) (hr : row<16) : rowTile*16+row<p.m+15 := by
  unfold rowTiles at hb
  omega

theorem prefix_input_row_bound (p : Shape) (block t : Nat)
    (hb : block<(geometry p).grid) (ht : t<64) :
    (block/columnTiles p)*16+aStoreRow t<2147483648 := by
  have hc := (a_store_coordinates t 0 ht (by decide)).1
  exact Nat.lt_trans (padded_row_bound p _ _ (block_coordinates p block hb).1 hc)
    (scalar_parameter_bounds p).1

theorem prefix_output_row_bound (p : Shape) (block t e : Nat)
    (hb : block<(geometry p).grid) (ht : t<64) (he : e<4) :
    (block/columnTiles p)*16+LarkMFMA.outputRow t e<2147483648 := by
  have hr : LarkMFMA.outputRow t e<16 := by unfold LarkMFMA.outputRow; omega
  exact Nat.lt_trans (padded_row_bound p _ _ (block_coordinates p block hb).1 hr)
    (scalar_parameter_bounds p).1

#print axioms k_minimum
#print axioms n_minimum
#print axioms scalar_parameter_bounds
#print axioms row_tiles_le_rows
#print axioms column_threads_bound
#print axioms grid_threads_bound
#print axioms thread_int32
#print axioms block_coordinates
#print axioms padded_row_bound
#print axioms prefix_input_row_bound
#print axioms prefix_output_row_bound
end LarkNativeAwqGemm
