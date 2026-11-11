import Lark.NativeAttentionPVLoad

/-! Seven actual source instructions in one weighted-V dot iteration. -/
namespace LarkNativeAttention
open LarkNonlinear
open LarkReduction (setIndex setReg execute_index_of execute_pure_of)
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def pvTerm (ops : Ops α) (input : Nat → Nat → α) (t key col row : Nat) (weights : Nat → α) : α :=
  ops.mul (weights row) (vValue ops input t key row col)
def pvNext (ops : Ops α) (input : Nat → Nat → α) (t key col row : Nat) (weights : Nat → α) (acc : α) : α :=
  ops.add acc (pvTerm ops input t key col row weights)
def pvCycle (ops : Ops α) (input : Nat → Nat → α) (t key col row : Nat) (weights : Nat → α)
    (acc : α) (s : State α) : State α :=
  let s := advance s t 70
  let s := setReg (record s t (sharedCell t 3 (scoreAddress t row)) false) t 14 (weights row) 71
  let s := setReg (record s t (sharedCell t 2 (row * 256 + col)) false) t 15 (vValue ops input t key row col) 72
  let s := setReg s t 16 (pvTerm ops input t key col row weights) 73
  let s := setReg s t 13 (pvNext ops input t key col row weights acc) 74
  advance (setIndex s t 13 ((row + 1 : Nat) : Int) 75) t 69

theorem pv_cycle_eq (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (t key col row extra : Nat)
    (weights : Nat → α) (acc : α) (s : State α) (hr : row < 32) (hc : col < 256)
    (hw : ScoreRange t weights 0 32 s) (hk : Tiles ops input t key s) (hn : NativeIndices t s)
    (hrow : s.indices t 13 = some (row : Int)) (hcol : s.indices t 12 = some (col : Int))
    (ha : s.regs t 13 = some acc) (hp : s.pc t = 69) :
    runLane ops (layout p) (geometry p) program t (extra + 7) s =
      runLane ops (layout p) (geometry p) program t extra (pvCycle ops input t key col row weights acc s) := by
  let s1 := advance s t 70
  let s2 := setReg (record s1 t (sharedCell t 3 (scoreAddress t row)) false) t 14 (weights row) 71
  let s3 := setReg (record s2 t (sharedCell t 2 (row * 256 + col)) false) t 15 (vValue ops input t key row col) 72
  let s4 := setReg s3 t 16 (pvTerm ops input t key col row weights) 73
  let s5 := setReg s4 t 13 (pvNext ops input t key col row weights acc) 74
  let s6 := setIndex s5 t 13 ((row + 1 : Nat) : Int) 75
  have hg := LarkReduction.predicate_lt_of (geometry p) t s (.ivar 13) (.const 32)
    (row : Int) 32 hrow (by rfl) (by omega)
  have h1 := execute_branch_of ops (layout p) (geometry p) t 70 76 _ s true hg (by omega)
  have h2 := execute_assign_of ops (layout p) (geometry p) t 14 71 (.load .shared 3 (scoreIndex 13)) s1 _ _
    (load_weight p ops t row weights s1 hr hw hn hrow) (by simp [s1, advance])
  have h3 := execute_assign_of ops (layout p) (geometry p) t 15 72 (.load .shared 2 (tileIndex 13 12)) s2 _ _
    (load_value p ops input t key row col s2 hr hc hk hrow hcol) (by simp [s2, setReg, advance])
  have h4 := execute_pure_of ops (layout p) (geometry p) t 16 73 (.bin .mul (.reg 14) (.reg 15)) s3
    (pvTerm ops input t key col row weights)
    (by simp [evalExpr, applyBinary, pvTerm, s3, s2, setReg, advance, record]) (by simp [s3, setReg, advance])
  have h5 := execute_pure_of ops (layout p) (geometry p) t 13 74 (.bin .add (.reg 13) (.reg 16)) s4
    (pvNext ops input t key col row weights acc)
    (by simp [evalExpr, applyBinary, pvNext, s4, s3, s2, s1, setReg, advance, record, ha])
    (by simp [s4, setReg, advance])
  have he6 := eval_counter (geometry p) t 13 row s5 hrow (by omega)
  have h6 := execute_index_of ops (layout p) (geometry p) t 13 75 (.add (.ivar 13) (.const 1)) s5
    ((row + 1 : Nat) : Int) he6 (by simp [s5, setReg, advance])
  have e1 := source_step p ops t 69 (extra + 6) _ s s1 (by rfl) hp h1
  have e2 := source_step p ops t 70 (extra + 5) _ s1 s2 pv_weight_read_code (by simp [s1, advance]) h2
  have e3 := source_step p ops t 71 (extra + 4) _ s2 s3 pv_value_read_code (by simp [s2, setReg, advance]) h3
  have e4 := source_step p ops t 72 (extra + 3) _ s3 s4 (by rfl) (by simp [s3, setReg, advance]) h4
  have e5 := source_step p ops t 73 (extra + 2) _ s4 s5 (by rfl) (by simp [s4, setReg, advance]) h5
  have e6 := source_step p ops t 74 (extra + 1) _ s5 s6 (by rfl) (by simp [s5, setReg, advance]) h6
  have e7 := source_step p ops t 75 extra (.jump 69) s6 (pvCycle ops input t key col row weights acc s) (by rfl)
    (by simp [s6, setIndex, advance]) (by rfl)
  exact e1.trans (e2.trans (e3.trans (e4.trans (e5.trans (e6.trans e7)))))

theorem pv_cycle_fields (ops : Ops α) (input : Nat → Nat → α) (t key col row : Nat)
    (weights : Nat → α) (acc : α) (s : State α) :
    (pvCycle ops input t key col row weights acc s).pc t = 69 ∧
    (pvCycle ops input t key col row weights acc s).indices t 13 = some ((row + 1 : Nat) : Int) ∧
    (pvCycle ops input t key col row weights acc s).regs t 13 = some (pvNext ops input t key col row weights acc) ∧
    (pvCycle ops input t key col row weights acc s).epochs = s.epochs ∧
    (pvCycle ops input t key col row weights acc s).memory = s.memory := by
  simp [pvCycle, setReg, setIndex, advance, record]

theorem pv_cycle_index (ops : Ops α) (input : Nat → Nat → α) (t key col row r : Nat)
    (weights : Nat → α) (acc : α) (s : State α) (hr : r ≠ 13) :
    (pvCycle ops input t key col row weights acc s).indices t r = s.indices t r := by
  simp [pvCycle, setReg, setIndex, advance, record, hr]

theorem pv_cycle_reg (ops : Ops α) (input : Nat → Nat → α) (t key col row r : Nat)
    (weights : Nat → α) (acc : α) (s : State α) (h13 : r ≠ 13) (h14 : r ≠ 14) (h15 : r ≠ 15) (h16 : r ≠ 16) :
    (pvCycle ops input t key col row weights acc s).regs t r = s.regs t r := by
  simp [pvCycle, setReg, setIndex, advance, record, h13, h14, h15, h16]

theorem pv_cycle_native (ops : Ops α) (input : Nat → Nat → α) (t key col row : Nat)
    (weights : Nat → α) (acc : α) (s : State α) (hn : NativeIndices t s) :
    NativeIndices t (pvCycle ops input t key col row weights acc s) :=
  ⟨(pv_cycle_index ops input t key col row 0 weights acc s (by decide)).trans hn.1,
   (pv_cycle_index ops input t key col row 1 weights acc s (by decide)).trans hn.2.1,
   (pv_cycle_index ops input t key col row 2 weights acc s (by decide)).trans hn.2.2⟩

theorem pv_cycle_good (ops : Ops α) (input : Nat → Nat → α) (t key col row : Nat)
    (weights : Nat → α) (acc : α) (s : State α) (hr : row < 32)
    (he : (s.epochs t).block % 2 = 1) (hg : TraceGood s) : TraceGood (pvCycle ops input t key col row weights acc s) := by
  exact record_good _ t (sharedCell t 2 (row * 256 + col)) false
    (record_good (advance s t 70) t (sharedCell t 3 (scoreAddress t row)) false hg
      (score_access_good t row false (s.epochs t) hr)) (value_read_good t row col (s.epochs t) he)

#print axioms pv_cycle_eq
#print axioms pv_cycle_good
end LarkNativeAttention
