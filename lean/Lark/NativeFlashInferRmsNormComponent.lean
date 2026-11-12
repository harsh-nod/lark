import Lark.NativeFlashInferRmsNormValue

/-! Actual eight-instruction source component cycle, including its input read. -/
namespace LarkNativeFlashInferRmsNorm
open LarkNonlinear
open LarkReduction (setIndex setReg execute_index_of execute_pure_of)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem load_input (p : Shape) (ops : Ops α) (t offset : Nat) (s : State α) (value : α)
    (hi : offset < p.rows * 16384) (hindex : s.indices t 7 = some (offset : Int))
    (hm : s.memory (globalCell 1 offset) = some value) :
    evalExpr ops (layout p) (geometry p) t (.un .fromHalf (.load .global 1 (.ivar 7))) s =
      some (ops.fromHalf value, record s t (globalCell 1 offset) false) := by
  simp only [evalExpr, evalIndex, hindex, input_location p t offset hi,
    hm, applyUnary, bind, pure, Option.bind]

theorem component_cycle (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component t extra : Nat) (acc : α) (s : State α)
    (hr : row < p.rows) (ht : tid < 1024) (hi : iteration < 2) (hc : component < 8)
    (h0 : s.indices t 0 = some (row : Int)) (h1 : s.indices t 1 = some (tid : Int))
    (h4 : s.indices t 4 = some (iteration : Int)) (h5 : s.indices t 5 = some (component : Int))
    (ha : s.regs t 0 = some acc) (hp : s.pc t = 9)
    (hm : s.memory (globalCell 1 (address row (column tid iteration component))) =
      some (input 1 (address row (column tid iteration component)))) :
    LarkCollective.runLane ops (layout p) (geometry p) program t (extra + 8) s =
      LarkCollective.runLane ops (layout p) (geometry p) program t extra
        (componentAfter ops input row tid iteration component t acc s) := by
  let col := column tid iteration component
  let offset := address row col
  let x := loaded ops input row tid iteration component
  let square := ops.mul x x
  let s1 := advance s t 10
  let s2 := setIndex s1 t 6 (col : Int) 11
  let s3 := setIndex s2 t 7 (offset : Int) 12
  let s4 := setReg (record s3 t (globalCell 1 offset) false) t 2 x 13
  let s5 := setReg s4 t 3 square 14
  let s6 := setReg s5 t 0 (ops.add acc square) 15
  let s7 := setIndex s6 t 5 ((component + 1 : Nat) : Int) 16
  have hb := address_bound p row tid iteration component hr ht hi hc
  have hcol := column_bound tid iteration component ht hi hc
  have hpred := LarkReduction.predicate_lt_of (geometry p) t s (.ivar 5) (.const 8)
    (component : Int) 8 h5 rfl (by omega)
  have e1 : execute ops (layout p) (geometry p) t (.branch (.lt (.ivar 5) (.const 8)) 17) s = some s1 := by
    simp only [execute, hpred, hp, bind, pure, Option.bind]
    rfl
  have he2 := eval_column p t tid iteration component s1 ht hi hc h1 h4 h5
  have e2 := execute_index_of ops (layout p) (geometry p) t 6 11 (columnIndex 4 5) s1 _ he2
    (by simp [s1, advance])
  change execute _ _ _ _ _ s1 = some s2 at e2
  have he3 := eval_address p t row col s2 hr hcol
    (by simpa [s2, s1, setIndex, advance] using h0) (by simp [s2, setIndex, advance])
  have e3 := execute_index_of ops (layout p) (geometry p) t 7 12
    (.add (.mul (.ivar 0) (.const 16384)) (.ivar 6)) s2 _ he3 (by simp [s2, setIndex, advance])
  change execute _ _ _ _ _ s2 = some s3 at e3
  have idx3 : s3.indices t 7 = some (offset : Int) := by simp [s3, setIndex, advance]
  have he4 := load_input p ops t offset s3 (input 1 offset) hb idx3 hm
  have e4 : execute ops (layout p) (geometry p) t
      (.assign 2 (.un .fromHalf (.load .global 1 (.ivar 7)))) s3 = some s4 := by
    simp only [execute, he4, bind, pure, Option.bind]
    have hpc : s3.pc t + 1 = 13 := by simp [s3, setIndex, advance]
    rewrite [hpc]
    rfl
  have e5 := execute_pure_of ops (layout p) (geometry p) t 3 14
    (.bin .mul (.reg 2) (.reg 2)) s4 square
    (by simp [evalExpr, applyBinary, s4, setReg, record, advance, x, loaded, square, offset, col])
    (by simp [s4, setReg, advance])
  change execute _ _ _ _ _ s4 = some s5 at e5
  have acc5 : s5.regs t 0 = some acc := by
    simp [s5, s4, s3, s2, s1, setReg, setIndex, record, advance, ha]
  have square5 : s5.regs t 3 = some square := by simp [s5, setReg, advance]
  have e6 := execute_pure_of ops (layout p) (geometry p) t 0 15
    (.bin .add (.reg 0) (.reg 3)) s5 (ops.add acc square)
    (by simp only [evalExpr, applyBinary, acc5, square5, bind, pure, Option.bind])
    (by simp [s5, setReg, advance])
  change execute _ _ _ _ _ s5 = some s6 at e6
  have idx6 : s6.indices t 5 = some (component : Int) := by
    simp [s6, s5, s4, s3, s2, s1, setReg, setIndex, record, advance, h5]
  have he7 := eval_nat_sum (geometry p) t component 1 s6 (.ivar 5) (.const 1) idx6 rfl (by omega)
  have e7 := execute_index_of ops (layout p) (geometry p) t 5 16
    (.add (.ivar 5) (.const 1)) s6 _ he7 (by simp [s6, setReg, advance])
  change execute _ _ _ _ _ s6 = some s7 at e7
  have e8 : execute ops (layout p) (geometry p) t (.jump 9) s7 =
      some (componentAfter ops input row tid iteration component t acc s) := rfl
  rewrite [scalar_step p ops t 9 _ _ s s1 (by decide) hp e1]
  rewrite [scalar_step p ops t 10 _ _ s1 s2 (by decide) (by simp [s1, advance]) e2]
  rewrite [scalar_step p ops t 11 _ _ s2 s3 (by decide) (by simp [s2, setIndex, advance]) e3]
  rewrite [scalar_step p ops t 12 _ _ s3 s4 (by decide) (by simp [s3, setIndex, advance]) e4]
  rewrite [scalar_step p ops t 13 _ _ s4 s5 (by decide) (by simp [s4, setReg, advance]) e5]
  rewrite [scalar_step p ops t 14 _ _ s5 s6 (by decide) (by simp [s5, setReg, advance]) e6]
  rewrite [scalar_step p ops t 15 _ _ s6 s7 (by decide) (by simp [s6, setReg, advance]) e7]
  rewrite [scalar_step p ops t 16 _ _ s7 _ (by decide) (by simp [s7, setIndex, advance]) e8]
  rfl

#print axioms load_input
#print axioms component_cycle
end LarkNativeFlashInferRmsNorm
