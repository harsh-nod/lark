import Lark.NativeAwqGemmAValues

/-! Signed scalar indices for both original N64/N128 B-staging paths. -/
namespace LarkNativeAwqGemm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option autoImplicit false
variable {α : Type}

structure BOuterIndices (p : Shape) (tile t chunk : Nat) (s : State α) : Prop where
  setup : SetupIndices p t s
  k : s.indices t 13=some (tile : Int)
  chunkIndex : s.indices t 15=some (chunk : Int)

structure BIndices (p : Shape) (tile t chunk e : Nat) (s : State α) : Prop where
  outer : BOuterIndices p tile t chunk s
  row : s.indices t 16=some ((bStoreRow p (laneId t) chunk : Nat) : Int)
  col : s.indices t 17=some ((bStoreCol p (laneId t) 0 : Nat) : Int)
  element : s.indices t 18=some (e : Int)

theorem b_outer_of_indices (p : Shape) (tile t chunk : Nat) (s next : State α)
    (h : BOuterIndices p tile t chunk s) (hi : next.indices=s.indices) : BOuterIndices p tile t chunk next := by
  exact {setup := setup_of_indices p t s next h.setup hi
         k := by rw [hi]; exact h.k
         chunkIndex := by rw [hi]; exact h.chunkIndex}

theorem b_outer_set_chunk (p : Shape) (tile t chunk next pc : Nat) (s : State α)
    (h : BOuterIndices p tile t chunk s) :
    BOuterIndices p tile t next (setIndex s t 15 (next : Int) pc) := by
  exact {setup := setIndex_setup p t 15 pc (next : Int) s h.setup (by decide)
         k := by simpa [setIndex,advance] using h.k
         chunkIndex := by simp [setIndex,advance]}

theorem b_outer_set_high (p : Shape) (tile t chunk r pc : Nat) (value : Int) (s : State α)
    (h : BOuterIndices p tile t chunk s) (hr : 16≤r) :
    BOuterIndices p tile t chunk (setIndex s t r value pc) := by
  have kDifferent : (13 : Nat)≠r := by omega
  have chunkDifferent : (15 : Nat)≠r := by omega
  exact {setup := setIndex_setup p t r pc value s h.setup (by omega)
         k := by simpa [setIndex,advance,kDifferent] using h.k
         chunkIndex := by simpa [setIndex,advance,chunkDifferent] using h.chunkIndex}

theorem b_indices_of_indices (p : Shape) (tile t chunk e : Nat) (s next : State α)
    (h : BIndices p tile t chunk e s) (hi : next.indices=s.indices) : BIndices p tile t chunk e next := by
  exact {outer := b_outer_of_indices p tile t chunk s next h.outer hi
         row := by rw [hi]; exact h.row
         col := by rw [hi]; exact h.col
         element := by rw [hi]; exact h.element}

theorem b_indices_set_element (p : Shape) (tile t chunk e next pc : Nat) (s : State α)
    (h : BIndices p tile t chunk e s) :
    BIndices p tile t chunk next (setIndex s t 18 (next : Int) pc) := by
  exact {outer := b_outer_set_high p tile t chunk 18 pc (next : Int) s h.outer (by decide)
         row := by simpa [setIndex,advance] using h.row
         col := by simpa [setIndex,advance] using h.col
         element := by simp [setIndex,advance]}

theorem b_divisor_bounds (p : Shape) : 0<tileN p/8 ∧ tileN p/8<2147483648 := by
  rcases tile_cases p with h | h <;> omega

theorem column_tile_bound (p : Shape) (t : Nat) : columnTileId p t<columnTiles p :=
  Nat.mod_lt _ (column_tiles_positive p)

theorem eval_b_row (p : Shape) (tile t chunk : Nat) (s : State α)
    (hc : chunk<banks p) (h : BOuterIndices p tile t chunk s) :
    evalIndex (geometry p) t s (bRowIndex p)=some ((bStoreRow p (laneId t) chunk : Nat) : Int) := by
  have coordinates := (b_store_coordinates p (laneId t) chunk 0 (lane_bound t) hc (by decide)).1
  have bound : (laneId t/32)*(256/tileN p)+(laneId t%32)/(tileN p/8)+chunk*(512/tileN p)<2147483648 := by
    unfold bStoreRow at coordinates
    omega
  have a := eval_nat_mul (geometry p) t (laneId t/32) (256/tileN p) s (v 2) (c (256/tileN p))
    h.setup.header.logicalWarp
    (eval_nat_const _ _ _ _ (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by decide)))
    (Nat.lt_of_le_of_lt (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)) bound)
  have b := eval_nat_div (geometry p) t (laneId t%32) (tileN p/8) s (v 1)
    h.setup.header.logicalLane (b_divisor_bounds p).1 (b_divisor_bounds p).2
  have ab := eval_nat_add (geometry p) t ((laneId t/32)*(256/tileN p)) ((laneId t%32)/(tileN p/8))
    s _ _ a b (Nat.lt_of_le_of_lt (Nat.le_add_right _ _) bound)
  have d := eval_nat_mul (geometry p) t chunk (512/tileN p) s (v 15) (c (512/tileN p)) h.chunkIndex
    (eval_nat_const _ _ _ _ (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by decide)))
    (Nat.lt_of_le_of_lt (Nat.le_add_left _ _) bound)
  exact eval_nat_add (geometry p) t
    ((laneId t/32)*(256/tileN p)+(laneId t%32)/(tileN p/8)) (chunk*(512/tileN p)) s _ _ ab d bound

theorem eval_b_col (p : Shape) (t : Nat) (s : State α) (h : HeaderIndices p t s) :
    evalIndex (geometry p) t s (bColIndex p)=some ((bStoreCol p (laneId t) 0 : Nat) : Int) := by
  have a := eval_nat_mod (geometry p) t (laneId t%32) (tileN p/8) s (v 1)
    h.logicalLane (b_divisor_bounds p).1 (b_divisor_bounds p).2
  have bound : (laneId t%32%(tileN p/8))*8<2147483648 := by
    rcases tile_cases p with h | h <;> rw [h] <;> omega
  have result := eval_nat_mul (geometry p) t (laneId t%32%(tileN p/8)) 8 s _ (c 8) a
    (eval_nat_const _ _ _ _ (by decide)) bound
  simpa only [bColIndex,bStoreCol,Nat.add_zero] using result

theorem b_col_component (p : Shape) (t e : Nat) :
    bStoreCol p (laneId t) 0+e=bStoreCol p (laneId t) e := by simp [bStoreCol]

theorem eval_b_stage (p : Shape) (tile t chunk e : Nat) (s : State α)
    (hc : chunk<banks p) (he : e<8) (h : BIndices p tile t chunk e s) :
    evalIndex (geometry p) t s (bStageIndex p)=some ((bStoreAddress p (laneId t) chunk e : Nat) : Int) := by
  have stored := b_store_bound p (laneId t) chunk e (lane_bound t) hc he
  have bound : bStoreRow p (laneId t) chunk*(tileN p+8)+bStoreCol p (laneId t) 0+e<2147483648 := by
    rw [Nat.add_assoc,b_col_component]
    change bStoreAddress p (laneId t) chunk e<2147483648
    rcases tile_cases p with hn | hn <;> rw [hn] at stored <;> omega
  have stride : tileN p+8<2147483648 := by rcases tile_cases p with hn | hn <;> omega
  have row := eval_nat_mul (geometry p) t (bStoreRow p (laneId t) chunk) (tileN p+8) s (v 16) (c (tileN p+8))
    h.row (eval_nat_const _ _ _ _ stride) (by omega)
  have col := eval_nat_add (geometry p) t (bStoreRow p (laneId t) chunk*(tileN p+8)) (bStoreCol p (laneId t) 0)
    s _ (v 17) row h.col (by omega)
  have result := eval_nat_add (geometry p) t
    (bStoreRow p (laneId t) chunk*(tileN p+8)+bStoreCol p (laneId t) 0) e s _ (v 18) col h.element bound
  simpa only [bStageIndex,bStoreAddress,Nat.add_assoc,b_col_component] using result

theorem eval_b_global (p : Shape) (tile t chunk e : Nat) (s : State α)
    (hk : tile<p.k/32) (hc : chunk<banks p) (he : e<8) (h : BIndices p tile t chunk e s) :
    evalIndex (geometry p) t s (bGlobalIndex p)=
      some ((bGlobal p (columnTileId p t) tile (laneId t) chunk e : Nat) : Int) := by
  have signed := b_global_int32 p (columnTileId p t) tile (laneId t) chunk e
    (column_tile_bound p t) hk (lane_bound t) hc he
  have bound : (tile*32+bStoreRow p (laneId t) chunk)*p.n+columnTileId p t*tileN p+
      bStoreCol p (laneId t) 0+e<2147483648 := by
    simpa only [bGlobal,Nat.add_assoc,b_col_component] using signed
  have coords := (b_store_coordinates p (laneId t) chunk e (lane_bound t) hc he).1
  have rowBound := k_component_bound p tile (bStoreRow p (laneId t) chunk) hk coords
  have kBound := (scalar_parameter_bounds p).2.1
  have nBound : p.n<2147483648 := by have hn := (scalar_parameter_bounds p).2.2; omega
  have tileBound : tileN p<2147483648 := by rcases tile_cases p with hn | hn <;> omega
  have a := eval_nat_mul (geometry p) t tile 32 s (v 13) (c 32) h.outer.k
    (eval_nat_const _ _ _ _ (by decide)) (by omega)
  have ab := eval_nat_add (geometry p) t (tile*32) (bStoreRow p (laneId t) chunk) s _ (v 16) a h.row (by omega)
  have row := eval_nat_mul (geometry p) t (tile*32+bStoreRow p (laneId t) chunk) p.n s _ (c p.n) ab
    (eval_nat_const _ _ _ _ nBound) (by omega)
  have ccol := eval_nat_mul (geometry p) t (columnTileId p t) (tileN p) s (v 5) (c (tileN p)) h.outer.setup.header.column
    (eval_nat_const _ _ _ _ tileBound) (by omega)
  have firstCols := eval_nat_add (geometry p) t ((tile*32+bStoreRow p (laneId t) chunk)*p.n)
    (columnTileId p t*tileN p) s _ _ row ccol (by omega)
  have col := eval_nat_add (geometry p) t
    ((tile*32+bStoreRow p (laneId t) chunk)*p.n+columnTileId p t*tileN p) (bStoreCol p (laneId t) 0)
    s _ (v 17) firstCols h.col (by omega)
  have result := eval_nat_add (geometry p) t
    ((tile*32+bStoreRow p (laneId t) chunk)*p.n+columnTileId p t*tileN p+bStoreCol p (laneId t) 0)
    e s _ (v 18) col h.element bound
  simpa only [bGlobalIndex,bGlobal,Nat.add_assoc,b_col_component] using result

theorem eval_b_increment (p : Shape) (tile t chunk e : Nat) (s : State α)
    (he : e<8) (h : BIndices p tile t chunk e s) :
    evalIndex (geometry p) t s (.add (v 18) (c 1))=some ((e+1 : Nat) : Int) :=
  eval_nat_add (geometry p) t e 1 s (v 18) (c 1) h.element (eval_nat_const _ _ _ _ (by decide)) (by omega)

theorem eval_chunk_increment (p : Shape) (tile t chunk : Nat) (s : State α)
    (hc : chunk<banks p) (h : BOuterIndices p tile t chunk s) :
    evalIndex (geometry p) t s (.add (v 15) (c 1))=some ((chunk+1 : Nat) : Int) := by
  have hb := banks_cases p
  exact eval_nat_add (geometry p) t chunk 1 s (v 15) (c 1) h.chunkIndex
    (eval_nat_const _ _ _ _ (by decide)) (by omega)

#print axioms b_outer_of_indices
#print axioms b_outer_set_chunk
#print axioms b_outer_set_high
#print axioms b_indices_of_indices
#print axioms b_indices_set_element
#print axioms b_divisor_bounds
#print axioms column_tile_bound
#print axioms eval_b_row
#print axioms eval_b_col
#print axioms b_col_component
#print axioms eval_b_stage
#print axioms eval_b_global
#print axioms eval_b_increment
#print axioms eval_chunk_increment
end LarkNativeAwqGemm
