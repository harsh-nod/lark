import Lark.NativeSoftmaxClamp

/-! Actual first-pass load/max component, retaining both clamp branches and
the source-ordered arithmetic under arbitrary scalar operations. -/
namespace LarkNativeSoftmax
open LarkNonlinear
open LarkReduction (setIndex setReg execute_index_of execute_pure_of)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def maxValue (ops : Ops α) (input : Nat → Nat → α) (row tid iteration component : Nat) : α :=
  ops.fromHalf (input 1 (address row (clamped (column tid iteration component))))

def maxComponentCost (tid iteration component : Nat) : Nat :=
  7 + clampCost (column tid iteration component)

def maxComponentAfter (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component t : Nat) (acc : α) (s : State α) : State α :=
  let col := column tid iteration component
  let offset := address row (clamped col)
  let value := maxValue ops input row tid iteration component
  let s := advance s t 9
  let s := setIndex s t 6 (col : Int) 10
  let s := clampedState t col s
  let s := setIndex s t 7 (offset : Int) 13
  let s := setReg (record s t (globalCell 1 offset) false) t 1 value 14
  let s := setReg s t 0 (ops.max acc value) 15
  let s := setIndex s t 5 ((component + 1 : Nat) : Int) 16
  advance s t 8

theorem eval_max_column (p : Shape) (t tid iteration component : Nat) (s : State α)
    (ht : tid < 1024) (hi : iteration < 7) (hc : component < 8)
    (h4 : s.indices t 4 = some ((base tid iteration : Nat) : Int))
    (h5 : s.indices t 5 = some (component : Int)) :
    evalIndex (geometry p) t s (.add (.ivar 4) (.mul (.ivar 5) (.const 1024))) =
      some ((column tid iteration component : Nat) : Int) := by
  have hm := eval_nat_mul (geometry p) t component 1024 s (.ivar 5) h5 (by decide) (by omega)
  have hb : base tid iteration + component * 1024 < 2147483648 := by unfold base; omega
  simpa only [column_expansion] using
    eval_nat_sum (geometry p) t (base tid iteration) (component * 1024) s
      (.ivar 4) (.mul (.ivar 5) (.const 1024)) h4 hm hb

theorem load_input_of (ops : Ops α) (l : Layout) (g : Geometry)
    (t offset : Nat) (s : State α) (value : α)
    (hl : location l g t .global 1 (offset : Int) false = some (globalCell 1 offset))
    (h7 : s.indices t 7 = some (offset : Int)) (hm : s.memory (globalCell 1 offset) = some value) :
    evalExpr ops l g t (.un .fromHalf (.load .global 1 (.ivar 7))) s =
      some (ops.fromHalf value,record s t (globalCell 1 offset) false) := by
  simp only [evalExpr,evalIndex,h7,hl,hm,applyUnary,bind,pure,Option.bind]

theorem load_input (p : Shape) (ops : Ops α) (t offset : Nat) (s : State α) (value : α)
    (hi : offset < p.rows * 50257) (h7 : s.indices t 7 = some (offset : Int))
    (hm : s.memory (globalCell 1 offset) = some value) :
    evalExpr ops (layout p) (geometry p) t (.un .fromHalf (.load .global 1 (.ivar 7))) s =
      some (ops.fromHalf value,record s t (globalCell 1 offset) false) :=
  load_input_of ops (layout p) (geometry p) t offset s value (input_location p t offset hi) h7 hm

theorem max_component_cycle (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component t extra : Nat) (acc : α) (s : State α)
    (hr : row < p.rows) (ht : tid < 1024) (hi : iteration < 7) (hc : component < 8)
    (h0 : s.indices t 0 = some (row : Int))
    (h4 : s.indices t 4 = some ((base tid iteration : Nat) : Int))
    (h5 : s.indices t 5 = some (component : Int))
    (ha : s.regs t 0 = some acc) (hp : s.pc t = 8) (reads : Reads p input s) :
    LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t
        (extra + maxComponentCost tid iteration component) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t extra
        (maxComponentAfter ops input row tid iteration component t acc s) := by
  let col := column tid iteration component
  let offset := address row (clamped col)
  let value := maxValue ops input row tid iteration component
  let s1 := advance s t 9
  let s2 := setIndex s1 t 6 (col : Int) 10
  let s3 := clampedState t col s2
  let s4 := setIndex s3 t 7 (offset : Int) 13
  let s5 := setReg (record s4 t (globalCell 1 offset) false) t 1 value 14
  let s6 := setReg s5 t 0 (ops.max acc value) 15
  let s7 := setIndex s6 t 5 ((component + 1 : Nat) : Int) 16
  have hb : offset < p.rows * 50257 := address_bound p row (clamped col) hr (clamped_bound col)
  have pred := LarkReduction.predicate_lt_of (geometry p) t s (.ivar 5) (.const 8)
    (component : Int) 8 h5 rfl (by omega)
  have e1 : execute ops (layout p) (geometry p) t
      (.branch (.lt (.ivar 5) (.const 8)) 17) s = some s1 := by
    simp [execute,pred,hp,s1]
  have he2 := eval_max_column p t tid iteration component s1 ht hi hc h4 h5
  have e2 := execute_index_of ops (layout p) (geometry p) t 6 10
    (.add (.ivar 4) (.mul (.ivar 5) (.const 1024))) s1 _ he2 (by simp [s1,advance])
  change execute _ _ _ _ _ s1 = some s2 at e2
  have f3 := clamped_fields t col s2 (by simp [s2,setIndex,advance])
  have h03 : s3.indices t 0 = some (row : Int) := by
    change (clampedState t col s2).indices t 0 = _
    rewrite [clamped_index_other t col 0 s2 (by decide)]
    simpa [s2,s1,setIndex,advance] using h0
  have he4 := eval_address p t row (clamped col) s3 hr (clamped_bound col) h03 f3.2
  have e4 := execute_index_of ops (layout p) (geometry p) t 7 13
    (.add (.mul (.ivar 0) (.const 50257)) (.ivar 6)) s3 _ he4
    (by rewrite [show s3.pc t = 12 from f3.1]; rfl)
  change execute _ _ _ _ _ s3 = some s4 at e4
  have idx4 : s4.indices t 7 = some (offset : Int) := by simp [s4,setIndex,advance]
  have hm4 : s4.memory (globalCell 1 offset) = some (input 1 offset) := by
    change s3.memory _ = _
    rewrite [(clamped_preserves t col s2).1]
    exact reads offset hb
  have he5 := load_input p ops t offset s4 (input 1 offset) hb idx4 hm4
  have e5 : execute ops (layout p) (geometry p) t
      (.assign 1 (.un .fromHalf (.load .global 1 (.ivar 7)))) s4 = some s5 := by
    simp only [execute,he5,bind,pure,Option.bind]
    have hpc : s4.pc t + 1 = 14 := by simp [s4,setIndex,advance]
    rewrite [hpc]
    rfl
  have hacc5 : s5.regs t 0 = some acc := by
    simp only [s5,setReg,advance,record,ite_false,and_true,reduceCtorEq]
    change s3.regs t 0 = some acc
    rewrite [(clamped_preserves t col s2).2.2.2]
    exact ha
  have hv5 : s5.regs t 1 = some value := by simp [s5,setReg,advance]
  have e6 := execute_pure_of ops (layout p) (geometry p) t 0 15
    (.bin .max (.reg 0) (.reg 1)) s5 (ops.max acc value)
    (by simp only [evalExpr,applyBinary,hacc5,hv5,bind,pure,Option.bind])
    (by simp [s5,setReg,advance])
  change execute _ _ _ _ _ s5 = some s6 at e6
  have idx6 : s6.indices t 5 = some (component : Int) := by
    have h53 : s3.indices t 5 = some (component : Int) := by
      change (clampedState t col s2).indices t 5 = _
      rewrite [clamped_index_other t col 5 s2 (by decide)]
      simpa [s2,s1,setIndex,advance] using h5
    simpa [s6,s5,s4,setReg,setIndex,record,advance] using h53
  have he7 := eval_nat_sum (geometry p) t component 1 s6 (.ivar 5) (.const 1) idx6 rfl (by omega)
  have e7 := execute_index_of ops (layout p) (geometry p) t 5 16
    (.add (.ivar 5) (.const 1)) s6 _ he7 (by simp [s6,setReg,advance])
  change execute _ _ _ _ _ s6 = some s7 at e7
  have e8 : execute ops (layout p) (geometry p) t (.jump 8) s7 =
      some (maxComponentAfter ops input row tid iteration component t acc s) := rfl
  rewrite [show extra + maxComponentCost tid iteration component =
      ((extra + 5) + clampCost col) + 2 by simp [maxComponentCost,col]; omega]
  rewrite [show ((extra + 5) + clampCost col) + 2 =
      (((extra + 5) + clampCost col) + 1) + 1 by omega]
  rewrite [scalar_step p guarded ops t 8 _ _ s s1 (by cases guarded <;> decide) hp e1]
  rewrite [scalar_step p guarded ops t 9 _ _ s1 s2 (by cases guarded <;> decide)
    (by simp [s1,advance]) e2]
  rewrite [clamp_eq p guarded ops t col (extra + 5) s2 (by simp [s2,setIndex,advance])
    (by simp [s2,setIndex,advance])]
  rewrite [show extra + 5 = (extra + 4) + 1 by omega,
    scalar_step p guarded ops t 12 _ _ s3 s4 (by cases guarded <;> decide) f3.1 e4]
  rewrite [scalar_step p guarded ops t 13 _ _ s4 s5 (by cases guarded <;> decide)
    (by simp [s4,setIndex,advance]) e5]
  rewrite [scalar_step p guarded ops t 14 _ _ s5 s6 (by cases guarded <;> decide)
    (by simp [s5,setReg,advance]) e6]
  rewrite [scalar_step p guarded ops t 15 _ _ s6 s7 (by cases guarded <;> decide)
    (by simp [s6,setReg,advance]) e7]
  rewrite [scalar_step p guarded ops t 16 _ _ s7 _ (by cases guarded <;> decide)
    (by simp [s7,setIndex,advance]) e8]
  rfl

theorem max_component_fields (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component t : Nat) (acc : α) (s : State α) :
    (maxComponentAfter ops input row tid iteration component t acc s).pc t = 8 ∧
    (maxComponentAfter ops input row tid iteration component t acc s).indices t 5 =
      some ((component + 1 : Nat) : Int) ∧
    (maxComponentAfter ops input row tid iteration component t acc s).regs t 0 =
      some (ops.max acc (maxValue ops input row tid iteration component)) ∧
    (maxComponentAfter ops input row tid iteration component t acc s).memory = s.memory ∧
    (maxComponentAfter ops input row tid iteration component t acc s).epochs = s.epochs ∧
    (maxComponentAfter ops input row tid iteration component t acc s).trace =
      ⟨t,globalCell 1 (address row (clamped (column tid iteration component))),false,s.epochs t⟩ :: s.trace := by
  by_cases hc : 50257 ≤ column tid iteration component <;>
    simp [maxComponentAfter,clampedState,hc,setIndex,setReg,advance,record]

theorem max_component_index_other (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component t r : Nat) (acc : α) (s : State α)
    (h5 : r ≠ 5) (h6 : r ≠ 6) (h7 : r ≠ 7) :
    (maxComponentAfter ops input row tid iteration component t acc s).indices t r = s.indices t r := by
  by_cases hc : 50257 ≤ column tid iteration component <;>
    simp [maxComponentAfter,clampedState,hc,setIndex,setReg,advance,record,h5,h6,h7]

structure MaxReady (p : Shape) (input : Nat → Nat → α)
    (row tid iteration component t : Nat) (acc : α) (s : State α) : Prop where
  pc : s.pc t = 8
  rowIndex : s.indices t 0 = some (row : Int)
  tidIndex : s.indices t 1 = some (tid : Int)
  baseIndex : s.indices t 4 = some ((base tid iteration : Nat) : Int)
  componentIndex : s.indices t 5 = some (component : Int)
  accumulator : s.regs t 0 = some acc
  reads : Reads p input s
  good : ∀ a ∈ s.trace, Good a

theorem max_component_ready (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component t : Nat) (acc : α) (s : State α)
    (ready : MaxReady p input row tid iteration component t acc s) :
    MaxReady p input row tid iteration (component + 1) t
      (ops.max acc (maxValue ops input row tid iteration component))
      (maxComponentAfter ops input row tid iteration component t acc s) := by
  obtain ⟨hpc,h5,ha,hm,he,ht⟩ := max_component_fields ops input row tid iteration component t acc s
  refine ⟨hpc,?_,?_,?_,h5,ha,?_,?_⟩
  · rewrite [max_component_index_other ops input row tid iteration component t 0 acc s
      (by decide) (by decide) (by decide)]
    exact ready.rowIndex
  · rewrite [max_component_index_other ops input row tid iteration component t 1 acc s
      (by decide) (by decide) (by decide)]
    exact ready.tidIndex
  · rewrite [max_component_index_other ops input row tid iteration component t 4 acc s
      (by decide) (by decide) (by decide)]
    exact ready.baseIndex
  · intro offset hb
    rewrite [hm]
    exact ready.reads offset hb
  · intro a ha
    rewrite [ht] at ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact Good.input rfl rfl rfl rfl
    · exact ready.good a ha

#print axioms eval_max_column
#print axioms load_input_of
#print axioms load_input
#print axioms max_component_cycle
#print axioms max_component_fields
#print axioms max_component_index_other
#print axioms max_component_ready
end LarkNativeSoftmax
