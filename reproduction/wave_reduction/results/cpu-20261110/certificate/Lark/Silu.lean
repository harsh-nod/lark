import Lark.Matrix
import Lark.ScalarLaunch

/-! Scalar SiLU-and-mul with the upstream row/block/strided-loop organization. -/
namespace LarkSilu
open LarkNonlinear LarkReduction
set_option maxRecDepth 10000
set_option maxHeartbeats 20000000

structure Shape where
  rows : Nat
  width : Nat
  block : Nat
  warp : Nat
  rowsPos : 0 < rows
  widthPos : 0 < width
  blockPos : 0 < block
  warpPos : 0 < warp
  blockLe : block ≤ width
  dataBound : rows * (2 * width) < 2147483648

def layout (p : Shape) : Layout :=
  ⟨[⟨.output, p.rows * p.width⟩, ⟨.input, p.rows * (2 * p.width)⟩], [], []⟩
def geometry (p : Shape) : Geometry := ⟨p.rows, p.block, p.warp⟩
def fuel (p : Shape) : Fuel := LarkScalarLaunch.fuel (7 * p.width + 4)
def cell (b i : Nat) : Location := ⟨.global, 0, b, i⟩
def aAddress (p : Shape) (row col : Nat) : Nat := (row * 2) * p.width + col
def bAddress (p : Shape) (row col : Nat) : Nat := aAddress p row col + p.width
def oAddress (p : Shape) (row col : Nat) : Nat := row * p.width + col
def owner (p : Shape) (row col : Nat) : Nat := row * p.block + col % p.block
def aIndex (p : Shape) : Index :=
  .add (.mul (.mul (.ivar 0) (.const 2)) (.const (p.width : Int))) (.ivar 1)
def bIndex (p : Shape) : Index := .add (aIndex p) (.const (p.width : Int))
def oIndex (p : Shape) : Index :=
  .add (.mul (.ivar 0) (.const (p.width : Int))) (.ivar 1)
def activationExpr : Expr :=
  .un .fromHalf (.un .toHalf (.bin .div (.reg 0)
    (.bin .add (.lit 1 1) (.un .exp (.bin .mul
      (.bin .sub (.lit 0 1) (.reg 0)) (.lit 1 1))))))
def outputExpr : Expr := .un .toHalf (.bin .mul (.reg 2) (.bin .add (.reg 1) (.lit 0 1)))
def program (p : Shape) : List Instr :=
  [.index 0 .bid, .index 1 .tid,
   .branch (.lt (.ivar 1) (.const (p.width : Int))) 9,
   .assign 0 (.un .fromHalf (.load .global 1 (aIndex p))),
   .assign 1 (.un .fromHalf (.load .global 1 (bIndex p))),
   .assign 2 activationExpr,
   .store .global 0 (oIndex p) outputExpr,
   .index 1 (.add (.ivar 1) .bdim), .jump 2, .halt]

def activation (ops : Ops α) (x : α) : α :=
  ops.fromHalf (ops.toHalf (ops.div x (ops.add (ops.literal 1 1)
    (ops.exp (ops.mul (ops.sub (ops.literal 0 1) x) (ops.literal 1 1))))))
def result (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row col : Nat) : α :=
  ops.toHalf (ops.mul (activation ops (ops.fromHalf (input 1 (aAddress p row col))))
    (ops.add (ops.fromHalf (input 1 (bAddress p row col))) (ops.literal 0 1)))
def Reads (p : Shape) (input : Nat → Nat → α) (s : State α) : Prop :=
  ∀ i, i < p.rows * (2 * p.width) → s.memory (cell 1 i) = some (input 1 i)

def initialized (p : Shape) (t : Nat) (s : State α) : State α :=
  setIndex (setIndex s t 0 ((t / p.block : Nat) : Int) 1)
    t 1 ((t % p.block : Nat) : Int) 2
def cycleState (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t row col : Nat) (s : State α) : State α :=
  let s := advance s t 3
  let s := setReg (record s t (cell 1 (aAddress p row col)) false) t 0
    (ops.fromHalf (input 1 (aAddress p row col))) 4
  let s := setReg (record s t (cell 1 (bAddress p row col)) false) t 1
    (ops.fromHalf (input 1 (bAddress p row col))) 5
  let s := setReg s t 2 (activation ops (ops.fromHalf (input 1 (aAddress p row col)))) 6
  let s := advance { record s t (cell 0 (oAddress p row col)) true with
    memory := fun l => if l = cell 0 (oAddress p row col)
      then some (result p ops input row col) else s.memory l } t 7
  advance (setIndex s t 1 (((col + p.block : Nat)) : Int) 8) t 2

def iterate (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (t row : Nat) :
    Nat → Nat → State α → State α
  | 0, _, s => advance s t 9
  | k + 1, col, s => if col < p.width
      then iterate p ops input t row k (col + p.block) (cycleState p ops input t row col s)
      else advance s t 9
def finished (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (t : Nat)
    (s : State α) : State α :=
  iterate p ops input t (t / p.block) p.width (t % p.block) (initialized p t s)
def post (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (s : State α) (t : Nat) : State α :=
  if s.pc t = 9 then s else finished p ops input t s

theorem width_bound (p : Shape) : 2 * p.width < 2147483648 := by
  have hh := Nat.mul_le_mul_right (2 * p.width) (show 1 ≤ p.rows by have := p.rowsPos; omega)
  simp only [Nat.one_mul] at hh
  have := p.dataBound
  omega
theorem rows_bound (p : Shape) : p.rows < 2147483648 := by
  have hh := Nat.mul_le_mul_left p.rows (show 1 ≤ 2 * p.width by have := p.widthPos; omega)
  simp only [Nat.mul_one] at hh
  have := p.dataBound
  omega
theorem addresses_bound (p : Shape) (row col : Nat) (hr : row < p.rows) (hc : col < p.width) :
    aAddress p row col < p.rows * (2 * p.width) ∧
    bAddress p row col < p.rows * (2 * p.width) ∧ oAddress p row col < p.rows * p.width := by
  have ha := address_bound p.rows (2 * p.width) row col hr (by omega)
  have hb := address_bound p.rows (2 * p.width) row (col + p.width) hr (by omega)
  have ho := address_bound p.rows p.width row col hr hc
  simpa [aAddress, bAddress, oAddress, Nat.mul_assoc, Nat.add_assoc] using ⟨ha, hb, ho⟩

theorem stride_gap (j col block : Nat) (hb : 0 < block) (hj : j < col)
    (hm : j % block = col % block) : j + block ≤ col := by
  have hd : j / block ≤ col / block :=
    (Nat.le_div_iff_mul_le hb).mpr (Nat.le_trans (Nat.div_mul_le_self j block) (by omega))
  have hne : j / block ≠ col / block := by
    intro he
    have h1 := Nat.mod_add_div j block
    have h2 := Nat.mod_add_div col block
    rw [hm, he] at h1
    omega
  have hq : j / block + 1 ≤ col / block := by omega
  have hmul := Nat.mul_le_mul_left block hq
  simp only [Nat.mul_add, Nat.mul_one] at hmul
  have h1 := Nat.mod_add_div j block
  have h2 := Nat.mod_add_div col block
  rw [hm] at h1
  omega

theorem owner_row (p : Shape) (row col : Nat) : owner p row col / p.block = row := by
  have hm := Nat.mod_lt col p.blockPos
  simpa [owner, Nat.mul_comm, Nat.add_comm, Nat.div_eq_of_lt hm] using
    Nat.add_mul_div_left (col % p.block) row p.blockPos
theorem owner_lane (p : Shape) (row col : Nat) : owner p row col % p.block = col % p.block := by
  simp [owner, Nat.add_mod, Nat.mul_mod]
theorem owner_bound (p : Shape) (row col : Nat) (hr : row < p.rows) :
    owner p row col < p.rows * p.block := by
  exact address_bound p.rows p.block row (col % p.block) hr (Nat.mod_lt col p.blockPos)

theorem output_row (p : Shape) (row col : Nat) (hc : col < p.width) :
    oAddress p row col / p.width = row := by
  simpa [oAddress, Nat.mul_comm, Nat.add_comm, Nat.div_eq_of_lt hc] using
    Nat.add_mul_div_left col row p.widthPos
theorem output_col (p : Shape) (row col : Nat) (hc : col < p.width) :
    oAddress p row col % p.width = col := by simp [oAddress, Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt hc]
theorem output_injective (p : Shape) (r c r' c' : Nat) (hc : c < p.width) (hc' : c' < p.width)
    (he : oAddress p r c = oAddress p r' c') : r = r' ∧ c = c' := by
  have hr := congrArg (fun n => n / p.width) he
  have hh := congrArg (fun n => n % p.width) he
  simpa only [output_row p r c hc, output_row p r' c' hc', output_col p r c hc,
    output_col p r' c' hc'] using And.intro hr hh

theorem a_index_eval (p : Shape) (g : Geometry) (t row col : Nat) (s : State α)
    (hr : row < p.rows) (hc : col < p.width)
    (hi : s.indices t 0 = some (row : Int)) (hj : s.indices t 1 = some (col : Int)) :
    evalIndex g t s (aIndex p) = some ((aAddress p row col : Nat) : Int) := by
  have ha := (addresses_bound p row col hr hc).1
  have hbound := p.dataBound
  have hw := p.widthPos
  have hmul : (row * 2) * p.width < 2147483648 := by unfold aAddress at ha; omega
  have hrow2 : row * 2 < 2147483648 := by
    have he := Nat.mul_le_mul_left (row * 2) (show 1 ≤ p.width by omega)
    simp only [Nat.mul_one] at he
    omega
  have hd := width_bound p
  have h1 := LarkMatrix.eval_mul_nat g t s (.ivar 0) (.const 2) row 2 hi (by rfl) hrow2
  have h2 := LarkMatrix.eval_mul_nat g t s (.mul (.ivar 0) (.const 2))
    (.const (p.width : Int)) (row * 2) p.width h1 (int32_cast _ (by omega)) hmul
  exact LarkMatrix.eval_add_nat g t s _ _ ((row * 2) * p.width) col h2 hj (by
    unfold aAddress at ha
    omega)

theorem b_index_eval (p : Shape) (g : Geometry) (t row col : Nat) (s : State α)
    (hr : row < p.rows) (hc : col < p.width)
    (hi : s.indices t 0 = some (row : Int)) (hj : s.indices t 1 = some (col : Int)) :
    evalIndex g t s (bIndex p) = some ((bAddress p row col : Nat) : Int) := by
  have hb := (addresses_bound p row col hr hc).2.1
  have hbound := p.dataBound
  have hd := width_bound p
  exact LarkMatrix.eval_add_nat g t s _ _ (aAddress p row col) p.width
    (a_index_eval p g t row col s hr hc hi hj) (int32_cast _ (by omega)) (by
      unfold bAddress at hb
      omega)

theorem o_index_eval (p : Shape) (g : Geometry) (t row col : Nat) (s : State α)
    (hr : row < p.rows) (hc : col < p.width)
    (hi : s.indices t 0 = some (row : Int)) (hj : s.indices t 1 = some (col : Int)) :
    evalIndex g t s (oIndex p) = some ((oAddress p row col : Nat) : Int) := by
  have ho := (addresses_bound p row col hr hc).2.2
  have hspan : p.rows * p.width ≤ p.rows * (2 * p.width) :=
    Nat.mul_le_mul_left p.rows (by omega)
  have hbound := p.dataBound
  have hd := width_bound p
  have h1 := LarkMatrix.eval_mul_nat g t s (.ivar 0) (.const (p.width : Int)) row p.width
    hi (int32_cast _ (by omega)) (by unfold oAddress at ho; omega)
  exact LarkMatrix.eval_add_nat g t s _ _ (row * p.width) col h1 hj (by
    unfold oAddress at ho
    omega)

theorem load_of (p : Shape) (ops : Ops α) (g : Geometry) (t i : Nat) (ix : Index)
    (s : State α) (input : Nat → Nat → α) (hr : Reads p input s)
    (hb : i < p.rows * (2 * p.width)) (he : evalIndex g t s ix = some (i : Int)) :
    evalExpr ops (layout p) g t (.un .fromHalf (.load .global 1 ix)) s =
      some (ops.fromHalf (input 1 i), record s t (cell 1 i) false) := by
  have hneg : ¬ (i : Int) < 0 := by omega
  have hl : location (layout p) g t .global 1 (i : Int) false = some (cell 1 i) := by
    simp [location, layout, cell, hneg, hb]
  simp only [evalExpr, he, bind, pure, Option.bind, hl, hr i hb]
  rfl

theorem cycle (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t row col f : Nat) (s : State α) (reads : Reads p input s)
    (hr : row < p.rows) (hc : col < p.width)
    (hi : s.indices t 0 = some (row : Int)) (hj : s.indices t 1 = some (col : Int))
    (hp : s.pc t = 2) :
    runLane ops (layout p) (geometry p) (program p) t (f + 7) s =
      runLane ops (layout p) (geometry p) (program p) t f (cycleState p ops input t row col s) := by
  let s1 := advance s t 3
  let s2 := setReg (record s1 t (cell 1 (aAddress p row col)) false) t 0
    (ops.fromHalf (input 1 (aAddress p row col))) 4
  let s3 := setReg (record s2 t (cell 1 (bAddress p row col)) false) t 1
    (ops.fromHalf (input 1 (bAddress p row col))) 5
  let s4 := setReg s3 t 2 (activation ops (ops.fromHalf (input 1 (aAddress p row col)))) 6
  let s5 := advance { record s4 t (cell 0 (oAddress p row col)) true with
    memory := fun l => if l = cell 0 (oAddress p row col)
      then some (result p ops input row col) else s4.memory l } t 7
  let s6 := setIndex s5 t 1 (((col + p.block : Nat)) : Int) 8
  have hd := width_bound p
  have hblock := p.blockLe
  have hg := predicate_lt_of (geometry p) t s (.ivar 1) (.const (p.width : Int))
    (col : Int) (p.width : Int) hj (int32_cast _ (by omega)) (by omega)
  have h1 : execute ops (layout p) (geometry p) t
      (.branch (.lt (.ivar 1) (.const (p.width : Int))) 9) s = some s1 := by
    simp only [execute, hg, hp, bind, pure, Option.bind]
    rfl
  have bounds := addresses_bound p row col hr hc
  have he2 := load_of p ops (geometry p) t (aAddress p row col) (aIndex p) s1 input
    reads bounds.1 (a_index_eval p _ t row col s1 hr hc hi hj)
  have h2 : execute ops (layout p) (geometry p) t
      (.assign 0 (.un .fromHalf (.load .global 1 (aIndex p)))) s1 = some s2 := by
    simp only [execute, he2, bind, pure, Option.bind]
    simp [s2, s1, setReg, advance]
  have he3 := load_of p ops (geometry p) t (bAddress p row col) (bIndex p) s2 input
    reads bounds.2.1 (b_index_eval p _ t row col s2 hr hc hi hj)
  have h3 : execute ops (layout p) (geometry p) t
      (.assign 1 (.un .fromHalf (.load .global 1 (bIndex p)))) s2 = some s3 := by
    simp only [execute, he3, bind, pure, Option.bind]
    simp [s3, s2, setReg, advance]
  have ha : evalExpr ops (layout p) (geometry p) t activationExpr s3 =
      some (activation ops (ops.fromHalf (input 1 (aAddress p row col))), s3) := by
    simp [activationExpr, evalExpr, s3, s2, setReg, advance, record, activation, applyUnary, applyBinary]
  have h4 : execute ops (layout p) (geometry p) t (.assign 2 activationExpr) s3 = some s4 :=
    execute_pure_of ops _ _ t 2 6 _ s3 _ ha (by simp [s3, setReg, advance])
  have he5 : evalExpr ops (layout p) (geometry p) t outputExpr s4 =
      some (result p ops input row col, s4) := by
    simp [outputExpr, evalExpr, s4, s3, setReg, advance, result, applyUnary, applyBinary]
  have hix := o_index_eval p (geometry p) t row col s4 hr hc hi hj
  have hlo : location (layout p) (geometry p) t .global 0 (oAddress p row col : Int) true =
      some (cell 0 (oAddress p row col)) := by
    have hn : ¬ (oAddress p row col : Int) < 0 := by omega
    have hrole : (Role.output == Role.input) = false := by decide
    simp [location, layout, cell, hn, bounds.2.2, hrole]
  have h5 : execute ops (layout p) (geometry p) t (.store .global 0 (oIndex p) outputExpr) s4 =
      some s5 := by
    simp only [execute, hix, hlo, he5, bind, pure, Option.bind]
    simp [s5, s4, setReg, advance, record]
  have hbd : evalIndex (geometry p) t s5 .bdim = some (p.block : Int) := by
    change int32 (p.block : Int) = some (p.block : Int)
    exact int32_cast p.block (by omega)
  have he6 := LarkMatrix.eval_add_nat (geometry p) t s5 (.ivar 1) .bdim col p.block
    hj hbd (by omega)
  have h6 : execute ops (layout p) (geometry p) t (.index 1 (.add (.ivar 1) .bdim)) s5 =
      some s6 := execute_index_of ops _ _ t 1 8 _ s5 _ he6 (by simp [s5, advance])
  have h7 : execute ops (layout p) (geometry p) t (.jump 2) s6 =
      some (cycleState p ops input t row col s) := by rfl
  rewrite [LarkPointwise.lane_step ops _ _ _ _ _ _ _ _
    (by simp [parked, program, hp]) (by simp [program, hp]) h1]
  rewrite [LarkPointwise.lane_step ops _ _ _ _ _ _ _ _
    (by simp [parked, program, s1, advance]) (by simp [program, s1, advance]) h2]
  rewrite [LarkPointwise.lane_step ops _ _ _ _ _ _ _ _
    (by simp [parked, program, s2, setReg, advance]) (by simp [program, s2, setReg, advance]) h3]
  rewrite [LarkPointwise.lane_step ops _ _ _ _ _ _ _ _
    (by simp [parked, program, s3, setReg, advance]) (by simp [program, s3, setReg, advance]) h4]
  rewrite [LarkPointwise.lane_step ops _ _ _ _ _ _ _ _
    (by simp [parked, program, s4, setReg, advance]) (by simp [program, s4, setReg, advance]) h5]
  rewrite [LarkPointwise.lane_step ops _ _ _ _ _ _ _ _
    (by simp [parked, program, s5, advance]) (by simp [program, s5, advance]) h6]
  rewrite [LarkPointwise.lane_step ops _ _ _ _ _ _ _ _
    (by simp [parked, program, s6, setIndex, advance]) (by simp [program, s6, setIndex, advance]) h7]
  rfl

theorem cycle_memory (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t row col : Nat) (s : State α) (l : Location) :
    (cycleState p ops input t row col s).memory l =
      if l = cell 0 (oAddress p row col) then some (result p ops input row col) else s.memory l := by rfl

theorem cycle_pc (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t row col u : Nat) (s : State α) :
    (cycleState p ops input t row col s).pc u = if u = t then 2 else s.pc u := by
  by_cases h : u = t <;> simp [cycleState, advance, setReg, setIndex, record, h]

theorem cycle_row_index (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t row col : Nat) (s : State α) :
    (cycleState p ops input t row col s).indices t 0 = s.indices t 0 := by
  simp [cycleState, advance, setReg, setIndex, record]
theorem cycle_col_index (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t row col : Nat) (s : State α) :
    (cycleState p ops input t row col s).indices t 1 = some ((col + p.block : Nat) : Int) := by
  simp [cycleState, advance, setReg, setIndex, record]
theorem cycle_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t row col : Nat) (s : State α) (hr : Reads p input s) :
    Reads p input (cycleState p ops input t row col s) := by
  intro i hi
  rw [cycle_memory]
  simpa [cell] using hr i hi

theorem iterate_pc (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t row k col u : Nat) (s : State α) :
    (iterate p ops input t row k col s).pc u = if u = t then 9 else s.pc u := by
  induction k generalizing col s with
  | zero => simp [iterate, advance]
  | succ k ih =>
    simp only [iterate]
    split
    · rw [ih, cycle_pc]
      by_cases h : u = t <;> simp [h]
    · simp [advance]

theorem iterate_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t row k col : Nat) (s : State α) (hr : Reads p input s) :
    Reads p input (iterate p ops input t row k col s) := by
  induction k generalizing col s with
  | zero => exact hr
  | succ k ih =>
    simp only [iterate]
    split
    · exact ih _ _ (cycle_reads p ops input t row col s hr)
    · exact hr

theorem iterate_memory_preserved (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t row k col : Nat) (s : State α) (l : Location)
    (away : ∀ j, col ≤ j → j < p.width → j % p.block = col % p.block →
      l ≠ cell 0 (oAddress p row j)) :
    (iterate p ops input t row k col s).memory l = s.memory l := by
  induction k generalizing col s with
  | zero => rfl
  | succ k ih =>
    simp only [iterate]
    split
    next hc =>
      have hnext := ih (col + p.block) (cycleState p ops input t row col s) (by
        intro j hj hb hm
        apply away j (by omega) hb
        simpa [Nat.add_mod] using hm)
      rw [hnext, cycle_memory, if_neg (away col (by omega) hc rfl)]
    next => rfl

theorem iterate_writes (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t row k col target : Nat) (s : State α)
    (budget : p.width ≤ col + k) (ht : target < p.width) (hge : col ≤ target)
    (hm : target % p.block = col % p.block) :
    (iterate p ops input t row k col s).memory (cell 0 (oAddress p row target)) =
      some (result p ops input row target) := by
  induction k generalizing col s with
  | zero => omega
  | succ k ih =>
    have hc : col < p.width := by omega
    simp only [iterate, if_pos hc]
    by_cases he : target = col
    · subst target
      have hh := iterate_memory_preserved p ops input t row k (col + p.block)
        (cycleState p ops input t row col s) (cell 0 (oAddress p row col)) (by
          intro j hj _ _ he
          have ho := congrArg Location.offset he
          simp only [cell, oAddress] at ho
          have := p.blockPos
          omega)
      rw [hh, cycle_memory]
      simp
    · have gap := stride_gap col target p.block p.blockPos (by omega) hm.symm
      apply ih (col + p.block) (cycleState p ops input t row col s)
      · have := p.blockPos
        omega
      · exact gap
      · simpa [Nat.add_mod] using hm

theorem halted_lane (p : Shape) (ops : Ops α) (t f : Nat) (s : State α)
    (hp : s.pc t = 9) (hf : 0 < f) :
    runLane ops (layout p) (geometry p) (program p) t f s = some s := by
  cases f with
  | zero => omega
  | succ f => simp [runLane, parked, program, hp]

theorem exit_loop (p : Shape) (ops : Ops α) (t col f : Nat) (s : State α)
    (hj : s.indices t 1 = some (col : Int)) (hp : s.pc t = 2) (hc : p.width ≤ col)
    (hf : 0 < f) :
    runLane ops (layout p) (geometry p) (program p) t (f + 1) s = some (advance s t 9) := by
  have hd := width_bound p
  have hg := predicate_nlt_of (geometry p) t s (.ivar 1) (.const (p.width : Int))
    (col : Int) (p.width : Int) hj (int32_cast _ (by omega)) (by omega)
  have he : execute ops (layout p) (geometry p) t
      (.branch (.lt (.ivar 1) (.const (p.width : Int))) 9) s = some (advance s t 9) := by
    simp only [execute, hg, bind, pure, Option.bind]
    rfl
  rewrite [LarkPointwise.lane_step ops _ _ _ _ _ _ _ _
    (by simp [parked, program, hp]) (by simp [program, hp]) he]
  exact halted_lane p ops t f _ (by simp [advance]) hf

theorem loop_eq (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t row k col : Nat) (s : State α) (reads : Reads p input s)
    (hr : row < p.rows) (hi : s.indices t 0 = some (row : Int))
    (hj : s.indices t 1 = some (col : Int)) (hp : s.pc t = 2)
    (budget : p.width ≤ col + k) :
    runLane ops (layout p) (geometry p) (program p) t (7 * k + 2) s =
      some (iterate p ops input t row k col s) := by
  induction k generalizing col s with
  | zero => simpa [iterate] using exit_loop p ops t col 1 s hj hp (by omega) (by decide)
  | succ k ih =>
    by_cases hc : col < p.width
    · have hf : 7 * (k + 1) + 2 = (7 * k + 2) + 7 := by omega
      rewrite [hf, cycle p ops input t row col (7 * k + 2) s reads hr hc hi hj hp]
      simp only [iterate, if_pos hc]
      apply ih (col + p.block) (cycleState p ops input t row col s)
      · exact cycle_reads p ops input t row col s reads
      · simpa only [cycle_row_index] using hi
      · exact cycle_col_index p ops input t row col s
      · simp [cycle_pc]
      · have := p.blockPos
        omega
    · have hf : 7 * (k + 1) + 2 = (7 * (k + 1) + 1) + 1 := by omega
      rewrite [hf]
      simpa [iterate, hc] using exit_loop p ops t col (7 * (k + 1) + 1) s hj hp
        (by omega) (by omega)

theorem header_eq (p : Shape) (ops : Ops α)
    (t f : Nat) (s : State α) (ht : t < p.rows * p.block) (hp : s.pc t = 0) :
    runLane ops (layout p) (geometry p) (program p) t (f + 2) s =
      runLane ops (layout p) (geometry p) (program p) t f (initialized p t s) := by
  let s1 := setIndex s t 0 ((t / p.block : Nat) : Int) 1
  have hr : t / p.block < p.rows := (Nat.div_lt_iff_lt_mul p.blockPos).mpr ht
  have hrow := rows_bound p
  have hcol := Nat.mod_lt t p.blockPos
  have hblock := p.blockLe
  have hd := width_bound p
  have he1 : evalIndex (geometry p) t s .bid = some ((t / p.block : Nat) : Int) := by
    change int32 ((t / p.block : Nat) : Int) = _
    exact int32_cast _ (by omega)
  have h1 : execute ops (layout p) (geometry p) t (.index 0 .bid) s = some s1 :=
    execute_index_of ops _ _ t 0 1 .bid s _ he1 (by omega)
  have he2 : evalIndex (geometry p) t s1 .tid = some ((t % p.block : Nat) : Int) := by
    change int32 ((t % p.block : Nat) : Int) = _
    exact int32_cast _ (by omega)
  have h2 : execute ops (layout p) (geometry p) t (.index 1 .tid) s1 =
      some (initialized p t s) := execute_index_of ops _ _ t 1 2 .tid s1 _ he2
        (by simp [s1, setIndex, advance])
  rewrite [LarkPointwise.lane_step ops _ _ _ _ _ _ _ _
    (by simp [parked, program, hp]) (by simp [program, hp]) h1]
  rewrite [LarkPointwise.lane_step ops _ _ _ _ _ _ _ _
    (by simp [parked, program, s1, setIndex, advance])
    (by simp [program, s1, setIndex, advance]) h2]
  rfl

theorem lane_eq (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t : Nat) (s : State α) (reads : Reads p input s) (ht : t < p.rows * p.block)
    (hp : s.pc t = 0) :
    runLane ops (layout p) (geometry p) (program p) t (fuel p).lane s =
      some (finished p ops input t s) := by
  have hf : (fuel p).lane = (7 * p.width + 2) + 2 := by rfl
  rewrite [hf, header_eq p ops t (7 * p.width + 2) s ht hp]
  exact loop_eq p ops input t (t / p.block) p.width (t % p.block) (initialized p t s)
    reads ((Nat.div_lt_iff_lt_mul p.blockPos).mpr ht)
    (by simp [initialized, setIndex, advance]) (by simp [initialized, setIndex, advance])
    (by simp [initialized, setIndex, advance]) (by omega)

def Owned (p : Shape) (trace : List Access) : Prop :=
  ∀ a ∈ trace, if a.write then
    ∃ row col, row < p.rows ∧ col < p.width ∧
      a.location = cell 0 (oAddress p row col) ∧ owner p row col = a.thread
  else ∃ i, a.location = cell 1 i

theorem cycle_owned (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t row col : Nat) (s : State α) (hr : row < p.rows) (hc : col < p.width)
    (ho : owner p row col = t) (hs : Owned p s.trace) :
    Owned p (cycleState p ops input t row col s).trace := by
  intro a ha
  simp only [cycleState, advance, setReg, setIndex, record, List.mem_cons] at ha
  rcases ha with rfl | rfl | rfl | ha
  · exact ⟨row, col, hr, hc, rfl, ho⟩
  · exact ⟨bAddress p row col, rfl⟩
  · exact ⟨aAddress p row col, rfl⟩
  · exact hs a ha

theorem iterate_owned (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t row k col : Nat) (s : State α) (hr : row < p.rows)
    (ho : owner p row col = t) (hs : Owned p s.trace) :
    Owned p (iterate p ops input t row k col s).trace := by
  induction k generalizing col s with
  | zero => exact hs
  | succ k ih =>
    simp only [iterate]
    split
    next hc =>
      exact ih (col + p.block) (cycleState p ops input t row col s)
        (by simpa [owner, Nat.add_mod] using ho) (cycle_owned p ops input t row col s hr hc ho hs)
    next => exact hs

theorem owned_raceFree (p : Shape) (g : Geometry) (trace : List Access) (hs : Owned p trace) :
    raceFree g trace = true := by
  apply List.all_eq_true.mpr
  intro a ha
  apply List.all_eq_true.mpr
  intro b hb
  have hla := hs a ha
  have hlb := hs b hb
  by_cases same : a.thread = b.thread
  · simp [conflict, same]
  · cases aw : a.write <;> cases bw : b.write
    · simp [conflict, aw, bw]
    · simp only [aw, Bool.false_eq_true, ↓reduceIte] at hla
      simp only [bw, ↓reduceIte] at hlb
      obtain ⟨i, hi⟩ := hla
      obtain ⟨r, c, _, _, hl, _⟩ := hlb
      simp [conflict, sameLocation, hi, hl, cell]
    · simp only [aw, ↓reduceIte] at hla
      simp only [bw, Bool.false_eq_true, ↓reduceIte] at hlb
      obtain ⟨r, c, _, _, hl, _⟩ := hla
      obtain ⟨i, hi⟩ := hlb
      simp [conflict, sameLocation, hi, hl, cell]
    · simp only [aw, ↓reduceIte] at hla
      simp only [bw, ↓reduceIte] at hlb
      obtain ⟨r, c, _, hc, hloc, howner⟩ := hla
      obtain ⟨r', c', _, hc', hloc', howner'⟩ := hlb
      have hoff : oAddress p r c ≠ oAddress p r' c' := by
        intro he
        obtain ⟨hr, hh⟩ := output_injective p r c r' c' hc hc' he
        have heo : owner p r c = owner p r' c' := by rw [hr, hh]
        exact same (howner.symm.trans (heo.trans howner'))
      simp [conflict, sameLocation, hloc, hloc', cell, hoff]

theorem thread_owner (p : Shape) (t : Nat) : owner p (t / p.block) (t % p.block) = t := by
  simpa [owner, Nat.mul_comm] using Nat.div_add_mod t p.block

theorem finished_pc (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t u : Nat) (s : State α) :
    (finished p ops input t s).pc u = if u = t then 9 else s.pc u := by
  rw [finished, iterate_pc]
  by_cases h : u = t <;> simp [h, initialized, setIndex, advance]

theorem finished_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t : Nat) (s : State α) (hr : Reads p input s) : Reads p input (finished p ops input t s) :=
  iterate_reads p ops input t (t / p.block) p.width (t % p.block) (initialized p t s) hr

theorem finished_owned (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t : Nat) (s : State α) (ht : t < p.rows * p.block) (hs : Owned p s.trace) :
    Owned p (finished p ops input t s).trace := by
  exact iterate_owned p ops input t (t / p.block) p.width (t % p.block) (initialized p t s)
    ((Nat.div_lt_iff_lt_mul p.blockPos).mpr ht) (thread_owner p t) hs

theorem finished_writes (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t row col : Nat) (s : State α) (hc : col < p.width) (ho : owner p row col = t) :
    (finished p ops input t s).memory (cell 0 (oAddress p row col)) =
      some (result p ops input row col) := by
  have hr : row = t / p.block := by
    calc
      row = owner p row col / p.block := (owner_row p row col).symm
      _ = t / p.block := congrArg (fun n => n / p.block) ho
  have hm : col % p.block = t % p.block := by
    calc
      col % p.block = owner p row col % p.block := (owner_lane p row col).symm
      _ = t % p.block := congrArg (fun n => n % p.block) ho
  subst row
  unfold finished
  apply iterate_writes p ops input t (t / p.block) p.width (t % p.block) col
  · omega
  · exact hc
  · rw [← hm]
    exact Nat.mod_le col p.block
  · simpa using hm

theorem finished_other_output (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t row col : Nat) (s : State α) (hc : col < p.width) (ho : owner p row col ≠ t) :
    (finished p ops input t s).memory (cell 0 (oAddress p row col)) =
      s.memory (cell 0 (oAddress p row col)) := by
  unfold finished
  apply iterate_memory_preserved p ops input t (t / p.block) p.width (t % p.block)
    (initialized p t s) (cell 0 (oAddress p row col))
  intro j _ hj hm he
  have ha := congrArg Location.offset he
  have hi := output_injective p row col (t / p.block) j hc hj ha
  have hsame : owner p (t / p.block) j = t := by
    have hh : j % p.block = t % p.block := by simpa using hm
    simpa [owner, hh] using thread_owner p t
  apply ho
  simpa [hi.1, hi.2] using hsame

def Invariant (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (s : State α) : Prop :=
  Reads p input s ∧ Owned p s.trace ∧
  (∀ t, t < p.rows * p.block → s.pc t = 0 ∨ s.pc t = 9) ∧
  (∀ row col, row < p.rows → col < p.width → s.pc (owner p row col) = 9 →
    s.memory (cell 0 (oAddress p row col)) = some (result p ops input row col))

theorem invariant_initial (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) : Invariant p ops input (initial (layout p) input outside) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi
    simp [initial, layout, cell, hi]
  · intro a ha
    simp [initial] at ha
  · intro t _
    exact Or.inl rfl
  · intro row col _ _ hdone
    simp [initial] at hdone

theorem finished_invariant (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t : Nat) (s : State α) (hs : Invariant p ops input s) (ht : t < p.rows * p.block) :
    Invariant p ops input (finished p ops input t s) := by
  refine ⟨finished_reads p ops input t s hs.1, finished_owned p ops input t s ht hs.2.1, ?_, ?_⟩
  · intro u hu
    rw [finished_pc]
    by_cases he : u = t
    · simp [he]
    · simpa [he] using hs.2.2.1 u hu
  · intro row col hr hc hdone
    by_cases he : owner p row col = t
    · exact finished_writes p ops input t row col s hc he
    · rw [finished_other_output p ops input t row col s hc he]
      apply hs.2.2.2 row col hr hc
      simpa [finished_pc, he] using hdone

theorem lane_contract (p : Shape) (ops : Ops α) (input : Nat → Nat → α) :
    LarkScalarLaunch.LaneContract ops (layout p) (geometry p) (fuel p).lane 9 (program p)
      (post p ops input) (Invariant p ops input) := by
  intro s hs t ht
  change t < p.rows * p.block at ht
  by_cases he : s.pc t = 9
  · simp only [post, if_pos he]
    exact ⟨halted_lane p ops t (fuel p).lane s he (by simp [fuel, LarkScalarLaunch.fuel]),
      hs, he, by intro u hu; exact hu⟩
  · simp only [post, if_neg he]
    have hp : s.pc t = 0 := by
      rcases hs.2.2.1 t ht with h0 | h9
      · exact h0
      · contradiction
    refine ⟨lane_eq p ops input t s hs.1 ht hp, finished_invariant p ops input t s hs ht, ?_, ?_⟩
    · simp [finished_pc]
    · intro u hu
      by_cases hh : u = t <;> simp [finished_pc, hh, hu]

def finalState (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) : State α :=
  LarkScalarLaunch.launchPost (geometry p) (post p ops input) (initial (layout p) input outside)

theorem launch_eq (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) :
    runLaunch ops (layout p) (geometry p) (fuel p) (program p) (initial (layout p) input outside) =
      some (finalState p ops input outside) ∧ Invariant p ops input (finalState p ops input outside) ∧
      (∀ t, t < p.rows * p.block → (finalState p ops input outside).pc t = 9) := by
  exact LarkScalarLaunch.launch_simulation ops (layout p) (geometry p) (fuel p).lane 9
    (program p) (post p ops input) (Invariant p ops input) (by rfl) (lane_contract p ops input)
    p.rowsPos p.blockPos p.warpPos (initial (layout p) input outside) (invariant_initial p ops input outside)

def spec (p : Shape) (ops : Ops α) (input : Nat → Nat → α) : List α :=
  (List.range (p.rows * p.width)).map fun i => result p ops input (i / p.width) (i % p.width)

theorem final_output (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (i : Nat) (hi : i < p.rows * p.width) :
    (finalState p ops input outside).memory (cell 0 i) =
      some (result p ops input (i / p.width) (i % p.width)) := by
  have hr : i / p.width < p.rows := (Nat.div_lt_iff_lt_mul p.widthPos).mpr hi
  have hc := Nat.mod_lt i p.widthPos
  have info := launch_eq p ops input outside
  have ho := info.2.1.2.2.2 (i / p.width) (i % p.width) hr hc
    (info.2.2 _ (owner_bound p (i / p.width) (i % p.width) hr))
  have he : oAddress p (i / p.width) (i % p.width) = i := by
    simpa [oAddress, Nat.mul_comm] using Nat.div_add_mod i p.width
  simpa only [he] using ho

theorem extract_final (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) :
    extract (layout p) (finalState p ops input outside) = some (spec p ops input) := by
  simp only [extract, layout, List.zipIdx_cons, List.zipIdx_nil, List.flatMap_cons,
    List.flatMap_nil, List.nil_append]
  simp only [List.map_cons, List.map_nil, show Role.input ≠ Role.output by decide,
    ↓reduceIte, List.nil_append, List.append_nil]
  change (((List.range (p.rows * p.width)).map (fun i => (0, i))).mapM
    (fun bi => (finalState p ops input outside).memory ⟨.global, 0, bi.1, bi.2⟩) : Option (List α)) = _
  rw [LarkPointwise.mapM_map]
  exact LarkPointwise.mapM_some (List.range (p.rows * p.width)) _ _ (by
    intro i hi
    exact final_output p ops input outside i (List.mem_range.mp hi))

theorem correct (p : Shape) (ops : Ops α) :
    Correct ops (layout p) (geometry p) (fuel p) (program p) (spec p ops) := by
  intro input outside
  have info := launch_eq p ops input outside
  exact ⟨finalState p ops input outside, info.1,
    owned_raceFree p (geometry p) _ info.2.1.2.1, extract_final p ops input outside⟩

#print axioms lane_eq
#print axioms owned_raceFree
#print axioms correct
end LarkSilu
