import Lark.NativeAttentionScoreDot

/-! The first-score maximum assignment and later maximum updates retain the
source's distinct control paths and exact instruction counts. -/
namespace LarkNativeAttention
open LarkNonlinear
open LarkReduction (setIndex setReg execute_index_of execute_pure_of)
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem predicate_eq_of (g : Geometry) (t : Nat) (s : State α) (a b : Index) (x y : Int)
    (ha : evalIndex g t s a = some x) (hb : evalIndex g t s b = some y) (hxy : x = y) :
    evalPredicate g t s (.eq a b) = some true := by
  simp only [evalPredicate, ha, hb, bind, pure, Option.bind, hxy]
  rfl

theorem predicate_neq_of (g : Geometry) (t : Nat) (s : State α) (a b : Index) (x y : Int)
    (ha : evalIndex g t s a = some x) (hb : evalIndex g t s b = some y) (hxy : x ≠ y) :
    evalPredicate g t s (.eq a b) = some false := by
  simp only [evalPredicate, ha, hb, bind, pure, Option.bind, hxy]
  rfl

def nextMaximum (ops : Ops α) (row : Nat) (score maximum : α) : α :=
  if row = 0 then score else ops.max maximum score
def scoreTailFuel (row : Nat) : Nat := if row = 0 then 5 else 4
def scoreTail (ops : Ops α) (t row : Nat) (score maximum : α) (s : State α) : State α :=
  let s := if row = 0 then advance (setReg (advance s t 43) t 0 score 44) t 46
    else setReg (advance s t 45) t 0 (ops.max maximum score) 46
  advance (setIndex s t 9 ((row + 1 : Nat) : Int) 47) t 30

theorem score_tail_eq (p : Shape) (ops : Ops α) (t row extra : Nat) (score maximum : α) (s : State α)
    (hr : row < 32) (hrow : s.indices t 9 = some (row : Int))
    (hs : s.regs t 1 = some score) (hm : s.regs t 0 = some maximum) (hp : s.pc t = 42) :
    runLane ops (layout p) (geometry p) program t (extra + scoreTailFuel row) s =
      runLane ops (layout p) (geometry p) program t extra (scoreTail ops t row score maximum s) := by
  by_cases hz : row = 0
  · subst row
    let s1 := advance s t 43
    let s2 := setReg s1 t 0 score 44
    let s3 := advance s2 t 46
    let s4 := setIndex s3 t 9 1 47
    have hg := predicate_eq_of (geometry p) t s (.ivar 9) (.const 0) 0 0 hrow (by rfl) rfl
    have h1 := execute_branch_of ops (layout p) (geometry p) t 43 45 _ s true hg (by omega)
    have h2 := execute_pure_of ops (layout p) (geometry p) t 0 44 (.reg 1) s1 score
      (by simp [evalExpr, s1, advance, hs]) (by simp [s1, advance])
    have h3 : execute ops (layout p) (geometry p) t (.jump 46) s2 = some s3 := rfl
    have he4 := eval_counter (geometry p) t 9 0 s3 hrow (by decide)
    have h4 := execute_index_of ops (layout p) (geometry p) t 9 47 (.add (.ivar 9) (.const 1)) s3 1 he4
      (by simp [s3, advance])
    have e1 := source_step p ops t 42 (extra + 4) _ s s1 (by rfl) hp h1
    have e2 := source_step p ops t 43 (extra + 3) _ s1 s2 (by rfl) (by simp [s1, advance]) h2
    have e3 := source_step p ops t 44 (extra + 2) _ s2 s3 (by rfl) (by simp [s2, setReg, advance]) h3
    have e4 := source_step p ops t 46 (extra + 1) _ s3 s4 (by rfl) (by simp [s3, advance]) h4
    have e5 := source_step p ops t 47 extra (.jump 30) s4 (scoreTail ops t 0 score maximum s) (by rfl)
      (by simp [s4, setIndex, advance]) (by rfl)
    exact e1.trans (e2.trans (e3.trans (e4.trans e5)))
  · let s1 := advance s t 45
    let s2 := setReg s1 t 0 (ops.max maximum score) 46
    let s3 := setIndex s2 t 9 ((row + 1 : Nat) : Int) 47
    have hg := predicate_neq_of (geometry p) t s (.ivar 9) (.const 0) (row : Int) 0 hrow (by rfl) (by omega)
    have h1 := execute_branch_of ops (layout p) (geometry p) t 43 45 _ s false hg (by omega)
    have h2 := execute_pure_of ops (layout p) (geometry p) t 0 46 (.bin .max (.reg 0) (.reg 1)) s1
      (ops.max maximum score) (by simp [evalExpr, applyBinary, s1, advance, hs, hm]) (by simp [s1, advance])
    have he3 := eval_counter (geometry p) t 9 row s2 hrow (by omega)
    have h3 := execute_index_of ops (layout p) (geometry p) t 9 47 (.add (.ivar 9) (.const 1)) s2
      ((row + 1 : Nat) : Int) he3 (by simp [s2, setReg, advance])
    have h4 : execute ops (layout p) (geometry p) t (.jump 30) s3 = some (scoreTail ops t row score maximum s) := by
      simp only [scoreTail, if_neg hz]
      rfl
    have e1 := source_step p ops t 42 (extra + 3) _ s s1 (by rfl) hp h1
    have e2 := source_step p ops t 45 (extra + 2) _ s1 s2 (by rfl) (by simp [s1, advance]) h2
    have e3 := source_step p ops t 46 (extra + 1) _ s2 s3 (by rfl) (by simp [s2, setReg, advance]) h3
    have e4 := source_step p ops t 47 extra (.jump 30) s3 (scoreTail ops t row score maximum s) (by rfl)
      (by simp [s3, setIndex, advance]) h4
    simpa only [scoreTailFuel, if_neg hz] using e1.trans (e2.trans (e3.trans e4))

theorem score_tail_fields (ops : Ops α) (t row : Nat) (score maximum : α) (s : State α) :
    (scoreTail ops t row score maximum s).pc t = 30 ∧
    (scoreTail ops t row score maximum s).indices t 9 = some ((row + 1 : Nat) : Int) ∧
    (scoreTail ops t row score maximum s).regs t 0 = some (nextMaximum ops row score maximum) ∧
    (scoreTail ops t row score maximum s).epochs = s.epochs ∧
    (scoreTail ops t row score maximum s).memory = s.memory ∧
    (scoreTail ops t row score maximum s).trace = s.trace := by
  by_cases hz : row = 0 <;> simp [scoreTail, nextMaximum, setIndex, setReg, advance, hz]

theorem score_tail_index (ops : Ops α) (t row r : Nat) (score maximum : α) (s : State α) (hr : r ≠ 9) :
    (scoreTail ops t row score maximum s).indices t r = s.indices t r := by
  by_cases hz : row = 0 <;> simp [scoreTail, setIndex, setReg, advance, hz, hr]

theorem score_tail_native (ops : Ops α) (t row : Nat) (score maximum : α)
    (s : State α) (hn : NativeIndices t s) : NativeIndices t (scoreTail ops t row score maximum s) :=
  ⟨(score_tail_index ops t row 0 score maximum s (by decide)).trans hn.1,
   (score_tail_index ops t row 1 score maximum s (by decide)).trans hn.2.1,
   (score_tail_index ops t row 2 score maximum s (by decide)).trans hn.2.2⟩

theorem score_tail_good (ops : Ops α) (t row : Nat) (score maximum : α)
    (s : State α) (hg : TraceGood s) : TraceGood (scoreTail ops t row score maximum s) := by
  intro a ha
  exact hg a ((score_tail_fields ops t row score maximum s).2.2.2.2.2 ▸ ha)

#print axioms score_tail_eq
#print axioms score_tail_fields
end LarkNativeAttention
