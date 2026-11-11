import Lark.NativeFusedRmsNormValue

/-! Actual twelve-instruction load/add/store cycle, including both mutable
residual and unrounded shared writes. No floating-point algebra is assumed.
-/
namespace LarkNativeFusedRmsNorm
open LarkNonlinear
open LarkReduction (setIndex setReg execute_index_of execute_pure_of)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem load_mutable (p : Shape) (ops : Ops α) (t buffer offset : Nat) (s : State α) (value : α)
    (hb : buffer = 0 ∨ buffer = 1) (hi : offset < p.rows * 16384)
    (hindex : s.indices t 7 = some (offset : Int))
    (hm : s.memory (globalCell buffer offset) = some value) :
    evalExpr ops (layout p) (geometry p) t (.un .fromHalf (.load .global buffer (.ivar 7))) s =
      some (ops.fromHalf value, record s t (globalCell buffer offset) false) := by
  simp only [evalExpr, evalIndex, hindex, mutable_location p t buffer offset false hb hi,
    hm, applyUnary, bind, pure, Option.bind]

theorem component_cycle (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component t extra : Nat) (acc : α) (s : State α)
    (hr : row < p.rows) (ht : tid < 1024) (hi : iteration < 2) (hc : component < 8)
    (h0 : s.indices t 0 = some (row : Int)) (h1 : s.indices t 1 = some (tid : Int))
    (h4 : s.indices t 4 = some (iteration : Int)) (h5 : s.indices t 5 = some (component : Int))
    (ha : s.regs t 0 = some acc) (hp : s.pc t = 9)
    (hm0 : s.memory (globalCell 0 (address row (column tid iteration component))) =
      some (input 0 (address row (column tid iteration component))))
    (hm1 : s.memory (globalCell 1 (address row (column tid iteration component))) =
      some (input 1 (address row (column tid iteration component)))) :
    LarkCollective.runLane ops (layout p) (geometry p) program t (extra + 12) s =
      LarkCollective.runLane ops (layout p) (geometry p) program t extra
        (componentAfter ops input row tid iteration component t acc s) := by
  let col := column tid iteration component
  let offset := address row col
  let x0 := ops.fromHalf (input 0 offset)
  let r0 := ops.fromHalf (input 1 offset)
  let x := added ops input row tid iteration component
  let square := ops.mul x x
  let s1 := advance s t 10
  let s2 := setIndex s1 t 6 (col : Int) 11
  let s3 := setIndex s2 t 7 (offset : Int) 12
  let s4 := setReg (record s3 t (globalCell 0 offset) false) t 2 x0 13
  let s5 := setReg (record s4 t (globalCell 1 offset) false) t 3 r0 14
  let s6 := setReg s5 t 2 x 15
  let s7 := setReg s6 t 4 square 16
  let s8 := setReg s7 t 0 (ops.add acc square) 17
  let s9 := written t 18 (globalCell 1 offset) (ops.toHalf x) s8
  let s10 := written t 19 (unroundedCell t col) x s9
  let s11 := setIndex s10 t 5 ((component + 1 : Nat) : Int) 20
  have hb := address_bound p row tid iteration component hr ht hi hc
  have hcol := column_bound tid iteration component ht hi hc
  have hpred := LarkReduction.predicate_lt_of (geometry p) t s (.ivar 5) (.const 8)
    (component : Int) 8 h5 (by rfl) (by omega)
  have e1 : execute ops (layout p) (geometry p) t (.branch (.lt (.ivar 5) (.const 8)) 21) s = some s1 := by
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
  have he4 := load_mutable p ops t 0 offset s3 (input 0 offset) (Or.inl rfl) hb idx3 hm0
  have e4 : execute ops (layout p) (geometry p) t
      (.assign 2 (.un .fromHalf (.load .global 0 (.ivar 7)))) s3 = some s4 := by
    simp only [execute, he4, bind, pure, Option.bind]
    have hpc : s3.pc t + 1 = 13 := by simp [s3, setIndex, advance]
    rewrite [hpc]
    rfl
  have idx4 : s4.indices t 7 = some (offset : Int) := idx3
  have he5 := load_mutable p ops t 1 offset s4 (input 1 offset) (Or.inr rfl) hb idx4 hm1
  have e5 : execute ops (layout p) (geometry p) t
      (.assign 3 (.un .fromHalf (.load .global 1 (.ivar 7)))) s4 = some s5 := by
    simp only [execute, he5, bind, pure, Option.bind]
    have hpc : s4.pc t + 1 = 14 := by simp [s4, setReg, advance]
    rewrite [hpc]
    rfl
  have e6 := execute_pure_of ops (layout p) (geometry p) t 2 15
    (.bin .add (.reg 2) (.reg 3)) s5 x
    (by simp [evalExpr, applyBinary, s5, s4, setReg, record, advance, x, added, x0, r0, offset, col])
    (by simp [s5, setReg, advance])
  change execute _ _ _ _ _ s5 = some s6 at e6
  have e7 := execute_pure_of ops (layout p) (geometry p) t 4 16
    (.bin .mul (.reg 2) (.reg 2)) s6 square
    (by simp [evalExpr, applyBinary, s6, setReg, advance, square])
    (by simp [s6, setReg, advance])
  change execute _ _ _ _ _ s6 = some s7 at e7
  have acc7 : s7.regs t 0 = some acc := by
    simp [s7, s6, s5, s4, s3, s2, s1, setReg, setIndex, record, advance, ha]
  have square7 : s7.regs t 4 = some square := by simp [s7, setReg, advance]
  have e8 := execute_pure_of ops (layout p) (geometry p) t 0 17
    (.bin .add (.reg 0) (.reg 4)) s7 (ops.add acc square)
    (by simp only [evalExpr, applyBinary, acc7, square7, bind, pure, Option.bind])
    (by simp [s7, setReg, advance])
  change execute _ _ _ _ _ s7 = some s8 at e8
  have idx8 : s8.indices t 7 = some (offset : Int) := idx3
  have reg8 : s8.regs t 2 = some x := by simp [s8, s7, s6, setReg, advance]
  have expr9 : evalExpr ops (layout p) (geometry p) t (.un .toHalf (.reg 2)) s8 =
      some (ops.toHalf x, s8) := by simp [evalExpr, applyUnary, reg8]
  have e9 : execute ops (layout p) (geometry p) t
      (.store .global 1 (.ivar 7) (.un .toHalf (.reg 2))) s8 = some s9 := by
    have hpc : s8.pc t + 1 = 18 := by simp [s8, setReg, advance]
    simp only [execute, evalIndex, idx8, mutable_location p t 1 offset true (Or.inr rfl) hb,
      expr9, bind, pure, Option.bind, hpc]
    rfl
  have idx9 : s9.indices t 6 = some (col : Int) := by
    simp [s9, s8, s7, s6, s5, s4, s3, s2, written, record, setReg, setIndex, advance]
  have reg9 : s9.regs t 2 = some x := reg8
  have e10 : execute ops (layout p) (geometry p) t (.store .shared 1 (.ivar 6) (.reg 2)) s9 = some s10 := by
    have hpc : s9.pc t + 1 = 19 := by simp [s9, written, advance]
    simp only [execute, evalIndex, idx9, unrounded_location p t col true hcol,
      evalExpr, reg9, bind, pure, Option.bind, hpc]
    rfl
  have idx10 : s10.indices t 5 = some (component : Int) := by
    simp [s10, s9, s8, s7, s6, s5, s4, s3, s2, s1,
      written, record, setReg, setIndex, advance, h5]
  have he11 := eval_nat_sum (geometry p) t component 1 s10 (.ivar 5) (.const 1) idx10 rfl (by omega)
  have e11 := execute_index_of ops (layout p) (geometry p) t 5 20
    (.add (.ivar 5) (.const 1)) s10 _ he11 (by simp [s10, written, advance])
  change execute _ _ _ _ _ s10 = some s11 at e11
  have e12 : execute ops (layout p) (geometry p) t (.jump 9) s11 =
      some (componentAfter ops input row tid iteration component t acc s) := rfl
  rewrite [scalar_step p ops t 9 _ _ s s1 (by decide) hp e1]
  rewrite [scalar_step p ops t 10 _ _ s1 s2 (by decide) (by simp [s1, advance]) e2]
  rewrite [scalar_step p ops t 11 _ _ s2 s3 (by decide) (by simp [s2, setIndex, advance]) e3]
  rewrite [scalar_step p ops t 12 _ _ s3 s4 (by decide) (by simp [s3, setIndex, advance]) e4]
  rewrite [scalar_step p ops t 13 _ _ s4 s5 (by decide) (by simp [s4, setReg, advance]) e5]
  rewrite [scalar_step p ops t 14 _ _ s5 s6 (by decide) (by simp [s5, setReg, advance]) e6]
  rewrite [scalar_step p ops t 15 _ _ s6 s7 (by decide) (by simp [s6, setReg, advance]) e7]
  rewrite [scalar_step p ops t 16 _ _ s7 s8 (by decide) (by simp [s7, setReg, advance]) e8]
  rewrite [scalar_step p ops t 17 _ _ s8 s9 (by decide) (by simp [s8, setReg, advance]) e9]
  rewrite [scalar_step p ops t 18 _ _ s9 s10 (by decide) (by simp [s9, written, advance]) e10]
  rewrite [scalar_step p ops t 19 _ _ s10 s11 (by decide) (by simp [s10, written, advance]) e11]
  rewrite [scalar_step p ops t 20 _ _ s11 _ (by decide) (by simp [s11, setIndex, advance]) e12]
  rfl

#print axioms load_mutable
#print axioms component_cycle
end LarkNativeFusedRmsNorm
