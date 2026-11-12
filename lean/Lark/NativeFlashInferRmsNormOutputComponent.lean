import Lark.NativeFlashInferRmsNormOutputValue

/-! Actual eleven-instruction output component cycle of the pinned source. -/
namespace LarkNativeFlashInferRmsNorm
open LarkNonlinear
open LarkReduction (setReg setIndex execute_index_of execute_pure_of)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem eval_output_column (p : Shape) (t tid iteration component : Nat) (s : State α)
    (ht : tid < 1024) (hi : iteration < 2) (hc : component < 8)
    (h1 : s.indices t 1 = some (tid : Int))
    (h8 : s.indices t 8 = some (iteration : Int)) (h9 : s.indices t 9 = some (component : Int)) :
    evalIndex (geometry p) t s (columnIndex 8 9) = some ((column tid iteration component : Nat) : Int) := by
  have hmul := eval_nat_mul (geometry p) t iteration 1024 s (.ivar 8) h8 (by decide) (by omega)
  have hadd := eval_nat_sum (geometry p) t (iteration * 1024) tid s _ (.ivar 1) hmul h1 (by omega)
  have hvec := eval_nat_mul (geometry p) t (iteration * 1024 + tid) 8 s _ hadd (by decide) (by omega)
  exact eval_nat_sum (geometry p) t ((iteration * 1024 + tid) * 8) component s _ _ hvec h9 (by omega)

theorem eval_output_address (p : Shape) (t row col : Nat) (s : State α)
    (hr : row < p.rows) (hc : col < 16384)
    (h0 : s.indices t 0 = some (row : Int)) (h10 : s.indices t 10 = some (col : Int)) :
    evalIndex (geometry p) t s (.add (.mul (.ivar 0) (.const 16384)) (.ivar 10)) =
      some ((address row col : Nat) : Int) := by
  have hb := p.bound
  have hmul := eval_nat_mul (geometry p) t row 16384 s (.ivar 0) h0 (by decide) (by omega)
  exact eval_nat_sum (geometry p) t (row * 16384) col s _ _ hmul h10 (by omega)

theorem output_component_cycle (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component t extra : Nat) (inverse : α) (s : State α)
    (hr : row < p.rows) (ht : tid < 1024) (hi : iteration < 2) (hc : component < 8)
    (he : t = row * 1024 + tid) (reads : OutputReads ops input row s)
    (h0 : s.indices t 0 = some (row : Int)) (h1 : s.indices t 1 = some (tid : Int))
    (h8 : s.indices t 8 = some (iteration : Int)) (h9 : s.indices t 9 = some (component : Int))
    (hx : s.regs t 7 = some inverse) (hp : s.pc t = 54) :
    LarkCollective.runLane ops (layout p) (geometry p) program t (extra + 11) s =
      LarkCollective.runLane ops (layout p) (geometry p) program t extra
        (outputComponent ops input row tid iteration component t inverse s) := by
  let col := column tid iteration component
  let offset := address row col
  let x := rowInput ops input row col
  let w := ops.fromHalf (input 2 col)
  let s1 := advance s t 55
  let s2 := setIndex s1 t 10 (col : Int) 56
  let s3 := setIndex s2 t 11 (offset : Int) 57
  let s4 := setReg (record s3 t (globalCell 1 offset) false) t 8 x 58
  let s5 := setReg (record s4 t (globalCell 2 col) false) t 9 w 59
  let s6 := setReg s5 t 10 (ops.add (ops.literal 0 1) w) 60
  let s7 := setReg s6 t 11 (ops.mul x inverse) 61
  let s8 := setReg s7 t 12 (outputWeighted ops input row col inverse) 62
  let s9 := written t 63 (globalCell 0 offset) (ops.toHalf (outputWeighted ops input row col inverse)) s8
  let s10 := setIndex s9 t 9 ((component + 1 : Nat) : Int) 64
  have hb := address_bound p row tid iteration component hr ht hi hc
  have hcol := column_bound tid iteration component ht hi hc
  have hrow : t / 1024 = row := by omega
  have pred := LarkReduction.predicate_lt_of (geometry p) t s (.ivar 9) (.const 8)
    (component : Int) 8 h9 rfl (by omega)
  have e1 : execute ops (layout p) (geometry p) t (.branch (.lt (.ivar 9) (.const 8)) 65) s = some s1 := by
    simp [execute, pred, hp, s1]
  have he2 := eval_output_column p t tid iteration component s1 ht hi hc h1 h8 h9
  have e2 := execute_index_of ops (layout p) (geometry p) t 10 56 (columnIndex 8 9) s1 _ he2
    (by simp [s1, advance])
  change execute _ _ _ _ _ s1 = some s2 at e2
  have he3 := eval_output_address p t row col s2 hr hcol
    (by simpa [s2, s1, setIndex, advance] using h0) (by simp [s2, setIndex, advance])
  have e3 := execute_index_of ops (layout p) (geometry p) t 11 57
    (.add (.mul (.ivar 0) (.const 16384)) (.ivar 10)) s2 _ he3 (by simp [s2, setIndex, advance])
  change execute _ _ _ _ _ s2 = some s3 at e3
  have idx3 : s3.indices t 10 = some (col : Int) := by simp [s3, s2, setIndex, advance]
  have addr3 : s3.indices t 11 = some (offset : Int) := by simp [s3, setIndex, advance]
  have inputValue : s3.memory (globalCell 1 offset) = some (input 1 offset) := (reads col hcol).1
  have he4 : evalExpr ops (layout p) (geometry p) t (.un .fromHalf (.load .global 1 (.ivar 11))) s3 =
      some (x, record s3 t (globalCell 1 offset) false) := by
    simp only [evalExpr, evalIndex, addr3, input_location p t offset hb, inputValue,
      applyUnary, bind, pure, Option.bind, x, rowInput, offset]
  have e4 : execute ops (layout p) (geometry p) t (.assign 8 (.un .fromHalf (.load .global 1 (.ivar 11)))) s3 = some s4 := by
    simp only [execute, he4, bind, pure, Option.bind]
    rewrite [show s3.pc t + 1 = 58 by simp [s3, setIndex, advance]]
    rfl
  have idx4 : s4.indices t 10 = some (col : Int) := idx3
  have weight : s4.memory (globalCell 2 col) = some (input 2 col) := (reads col hcol).2
  have he5 : evalExpr ops (layout p) (geometry p) t (.un .fromHalf (.load .global 2 (.ivar 10))) s4 =
      some (w, record s4 t (globalCell 2 col) false) := by
    simp only [evalExpr, evalIndex, idx4, weight_location p t col hcol, weight, applyUnary, bind, pure, Option.bind, w]
  have e5 : execute ops (layout p) (geometry p) t
      (.assign 9 (.un .fromHalf (.load .global 2 (.ivar 10)))) s4 = some s5 := by
    simp only [execute, he5, bind, pure, Option.bind]
    rewrite [show s4.pc t + 1 = 59 by simp [s4, setReg, advance]]
    rfl
  have e6 := execute_pure_of ops (layout p) (geometry p) t 10 60
    (.bin .add (.lit 0 1) (.reg 9)) s5 (ops.add (ops.literal 0 1) w)
    (by simp [evalExpr, applyBinary, s5, setReg, record, advance]) (by simp [s5, setReg, advance])
  change execute _ _ _ _ _ s5 = some s6 at e6
  have hscale : s6.regs t 7 = some inverse := by
    simp [s6, s5, s4, s3, s2, s1, setReg, setIndex, record, advance, hx]
  have hvalue : s6.regs t 8 = some x := by
    simp [s6, s5, s4, setReg, record, advance]
  have e7 := execute_pure_of ops (layout p) (geometry p) t 11 61
    (.bin .mul (.reg 8) (.reg 7)) s6 (ops.mul x inverse)
    (by simp only [evalExpr, hvalue, hscale, applyBinary, bind, pure, Option.bind])
    (by simp [s6, setReg, advance])
  change execute _ _ _ _ _ s6 = some s7 at e7
  have e8 := execute_pure_of ops (layout p) (geometry p) t 12 62
    (.bin .mul (.reg 11) (.reg 10)) s7 (outputWeighted ops input row col inverse)
    (by simp [evalExpr, applyBinary, s7, s6, setReg, advance, outputWeighted, x, w])
    (by simp [s7, setReg, advance])
  change execute _ _ _ _ _ s7 = some s8 at e8
  have idx8 : s8.indices t 11 = some (offset : Int) := by
    simp [s8, s7, s6, s5, s4, s3, setReg, setIndex, record, advance]
  have outExpr : evalExpr ops (layout p) (geometry p) t (.un .toHalf (.reg 12)) s8 =
      some (ops.toHalf (outputWeighted ops input row col inverse), s8) := by
    simp [evalExpr, applyUnary, s8, setReg, advance]
  have e9 : execute ops (layout p) (geometry p) t
      (.store .global 0 (.ivar 11) (.un .toHalf (.reg 12))) s8 = some s9 := by
    simp only [execute, evalIndex, idx8, output_location p t offset true hb,
      outExpr, bind, pure, Option.bind]
    rewrite [show s8.pc t + 1 = 63 by simp [s8, setReg, advance]]
    rfl
  have idx9 : s9.indices t 9 = some (component : Int) := by
    simp [s9, s8, s7, s6, s5, s4, s3, s2, s1, written, record, setReg, setIndex, advance, h9]
  have he10 := eval_nat_sum (geometry p) t component 1 s9 (.ivar 9) (.const 1) idx9 rfl (by omega)
  have e10 := execute_index_of ops (layout p) (geometry p) t 9 64
    (.add (.ivar 9) (.const 1)) s9 _ he10 (by simp [s9, written, advance])
  change execute _ _ _ _ _ s9 = some s10 at e10
  have e11 : execute ops (layout p) (geometry p) t (.jump 54) s10 =
      some (outputComponent ops input row tid iteration component t inverse s) := rfl
  rewrite [scalar_step p ops t 54 _ _ s s1 (by decide) hp e1]
  rewrite [scalar_step p ops t 55 _ _ s1 s2 (by decide) (by simp [s1, advance]) e2]
  rewrite [scalar_step p ops t 56 _ _ s2 s3 (by decide) (by simp [s2, setIndex, advance]) e3]
  rewrite [scalar_step p ops t 57 _ _ s3 s4 (by decide) (by simp [s3, setIndex, advance]) e4]
  rewrite [scalar_step p ops t 58 _ _ s4 s5 (by decide) (by simp [s4, setReg, advance]) e5]
  rewrite [scalar_step p ops t 59 _ _ s5 s6 (by decide) (by simp [s5, setReg, advance]) e6]
  rewrite [scalar_step p ops t 60 _ _ s6 s7 (by decide) (by simp [s6, setReg, advance]) e7]
  rewrite [scalar_step p ops t 61 _ _ s7 s8 (by decide) (by simp [s7, setReg, advance]) e8]
  rewrite [scalar_step p ops t 62 _ _ s8 s9 (by decide) (by simp [s8, setReg, advance]) e9]
  rewrite [scalar_step p ops t 63 _ _ s9 s10 (by decide) (by simp [s9, written, advance]) e10]
  rewrite [scalar_step p ops t 64 _ _ s10 _ (by decide) (by simp [s10, setIndex, advance]) e11]
  rfl

#print axioms eval_output_column
#print axioms eval_output_address
#print axioms output_component_cycle
end LarkNativeFlashInferRmsNorm
