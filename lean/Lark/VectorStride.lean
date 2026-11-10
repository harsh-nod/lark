import Lark.Reduction
import Lark.ScalarLaunch

/-!
Coverage and unique writers for the aligned vector traversal used by RMSNorm.
These are arithmetic lemmas, not a complete source or launch certificate.
-/
namespace LarkVectorStride
set_option maxRecDepth 10000
set_option maxHeartbeats 20000000

structure Shape where
  rows : Nat
  width : Nat
  block : Nat
  vec : Nat
  rowsPos : 0 < rows
  widthPos : 0 < width
  blockPos : 0 < block
  vecPos : 0 < vec
  widthDiv : vec ∣ width
  dataBound : rows * width < 2147483648

def vectors (p : Shape) : Nat := p.width / p.vec
def column (p : Shape) (lane iteration component : Nat) : Nat :=
  (lane + iteration * p.block) * p.vec + component
def address (p : Shape) (row col : Nat) : Nat := row * p.width + col
def owner (p : Shape) (row col : Nat) : Nat :=
  row * p.block + (col / p.vec) % p.block
def writer (p : Shape) (offset : Nat) : Nat :=
  owner p (offset / p.width) (offset % p.width)

theorem vectors_width (p : Shape) : vectors p * p.vec = p.width :=
  Nat.div_mul_cancel p.widthDiv

theorem column_div (p : Shape) (lane iteration component : Nat)
    (hc : component < p.vec) :
    column p lane iteration component / p.vec = lane + iteration * p.block := by
  simpa [column, Nat.add_comm, Nat.mul_comm, Nat.div_eq_of_lt hc] using
    Nat.add_mul_div_left component (lane + iteration * p.block) p.vecPos

theorem column_mod (p : Shape) (lane iteration component : Nat)
    (hc : component < p.vec) :
    column p lane iteration component % p.vec = component := by
  simp [column, Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt hc]

theorem column_lane (p : Shape) (lane iteration component : Nat)
    (hl : lane < p.block) (hc : component < p.vec) :
    (column p lane iteration component / p.vec) % p.block = lane := by
  rewrite [column_div p lane iteration component hc]
  simp [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt hl]

theorem column_iteration (p : Shape) (lane iteration component : Nat)
    (hl : lane < p.block) (hc : component < p.vec) :
    (column p lane iteration component / p.vec) / p.block = iteration := by
  rewrite [column_div p lane iteration component hc]
  simpa [Nat.add_comm, Nat.mul_comm, Nat.div_eq_of_lt hl] using
    Nat.add_mul_div_left lane iteration p.blockPos

theorem column_injective (p : Shape) (lane iteration component lane' iteration' component' : Nat)
    (hl : lane < p.block) (hl' : lane' < p.block)
    (hc : component < p.vec) (hc' : component' < p.vec)
    (he : column p lane iteration component = column p lane' iteration' component') :
    lane = lane' ∧ iteration = iteration' ∧ component = component' := by
  have h1 := congrArg (fun col => (col / p.vec) % p.block) he
  have h2 := congrArg (fun col => (col / p.vec) / p.block) he
  have h3 := congrArg (fun col => col % p.vec) he
  simpa only [column_lane p lane iteration component hl hc,
    column_lane p lane' iteration' component' hl' hc',
    column_iteration p lane iteration component hl hc,
    column_iteration p lane' iteration' component' hl' hc',
    column_mod p lane iteration component hc, column_mod p lane' iteration' component' hc'] using
    And.intro h1 (And.intro h2 h3)

theorem reconstruct (p : Shape) (col : Nat) :
    column p ((col / p.vec) % p.block) ((col / p.vec) / p.block) (col % p.vec) = col := by
  have hq := Nat.div_add_mod (col / p.vec) p.block
  have hc := Nat.div_add_mod col p.vec
  unfold column
  rewrite [show (col / p.vec) % p.block + col / p.vec / p.block * p.block =
    col / p.vec by simpa [Nat.add_comm, Nat.mul_comm] using hq]
  simpa [Nat.mul_comm] using hc

theorem vector_bound (p : Shape) (col : Nat) (hc : col < p.width) :
    col / p.vec < vectors p := by
  apply (Nat.div_lt_iff_lt_mul p.vecPos).mpr
  simpa only [vectors_width] using hc

theorem iteration_bound (p : Shape) (col : Nat) (hc : col < p.width) :
    (col / p.vec) / p.block < (vectors p + p.block - 1) / p.block := by
  exact LarkScalarLaunch.warpCount_member _ _ _ p.blockPos (vector_bound p col hc)

/-- Every scalar cell has a unique vector slot, thread and component. -/
theorem coverage (p : Shape) (col : Nat) (hc : col < p.width) :
    ∃ lane < p.block, ∃ iteration < (vectors p + p.block - 1) / p.block,
      ∃ component < p.vec, column p lane iteration component = col := by
  exact ⟨(col / p.vec) % p.block, Nat.mod_lt _ p.blockPos,
    (col / p.vec) / p.block, iteration_bound p col hc,
    col % p.vec, Nat.mod_lt _ p.vecPos, reconstruct p col⟩

theorem column_bound (p : Shape) (lane iteration component : Nat)
    (hv : lane + iteration * p.block < vectors p) (hc : component < p.vec) :
    column p lane iteration component < p.width := by
  have h := LarkReduction.address_bound (vectors p) p.vec
    (lane + iteration * p.block) component hv hc
  simpa only [column, vectors_width] using h

theorem address_row (p : Shape) (row col : Nat) (hc : col < p.width) :
    address p row col / p.width = row := by
  simpa [address, Nat.mul_comm, Nat.add_comm, Nat.div_eq_of_lt hc] using
    Nat.add_mul_div_left col row p.widthPos

theorem address_col (p : Shape) (row col : Nat) (hc : col < p.width) :
    address p row col % p.width = col := by
  simp [address, Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt hc]

theorem address_writer (p : Shape) (row lane iteration component : Nat)
    (hl : lane < p.block) (hv : lane + iteration * p.block < vectors p)
    (hc : component < p.vec) :
    writer p (address p row (column p lane iteration component)) = row * p.block + lane := by
  have hb := column_bound p lane iteration component hv hc
  simp only [writer, address_row p row _ hb, address_col p row _ hb, owner,
    column_lane p lane iteration component hl hc]

theorem address_bound (p : Shape) (row col : Nat) (hr : row < p.rows)
    (hc : col < p.width) : address p row col < p.rows * p.width :=
  LarkReduction.address_bound p.rows p.width row col hr hc

theorem int32_address (p : Shape) (row col : Nat) (hr : row < p.rows)
    (hc : col < p.width) : address p row col < 2147483648 :=
  Nat.lt_trans (address_bound p row col hr hc) p.dataBound

/-- Equal output cells imply equal owning logical threads, across all rows. -/
theorem unique_writer (p : Shape) (offset a b : Nat)
    (ha : writer p offset = a) (hb : writer p offset = b) : a = b := by
  omega

#print axioms coverage
#print axioms address_writer
#print axioms int32_address
end LarkVectorStride
