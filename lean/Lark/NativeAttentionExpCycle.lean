import Lark.NativeAttentionExpLoad

/-! Six actual source instructions transform one score and accumulate its mass. -/
namespace LarkNativeAttention
open LarkNonlinear
open LarkReduction (setIndex setReg execute_index_of execute_pure_of)
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def expCycle (ops : Ops α) (t col : Nat) (score maximum acc : α) (s : State α) : State α :=
  let weight := normalizedWeight ops score maximum
  let s := advance s t 51
  let s := setReg (record s t (sharedCell t 3 (scoreAddress t col)) false) t 6 weight 52
  let s := storeState s t (sharedCell t 3 (scoreAddress t col)) weight 53
  let s := setReg s t 5 (ops.add acc weight) 54
  advance (setIndex s t 11 ((col + 1 : Nat) : Int) 55) t 50

theorem exp_cycle_eq (p : Shape) (ops : Ops α) (t col extra : Nat) (score maximum acc : α) (s : State α)
    (hc : col < 32) (hn : NativeIndices t s) (hcol : s.indices t 11 = some (col : Int))
    (hm : s.regs t 0 = some maximum) (ha : s.regs t 5 = some acc)
    (hv : s.memory (sharedCell t 3 (scoreAddress t col)) = some score) (hp : s.pc t = 50) :
    runLane ops (layout p) (geometry p) program t (extra + 6) s =
      runLane ops (layout p) (geometry p) program t extra (expCycle ops t col score maximum acc s) := by
  let weight := normalizedWeight ops score maximum
  let s1 := advance s t 51
  let s2 := setReg (record s1 t (sharedCell t 3 (scoreAddress t col)) false) t 6 weight 52
  let s3 := storeState s2 t (sharedCell t 3 (scoreAddress t col)) weight 53
  let s4 := setReg s3 t 5 (ops.add acc weight) 54
  let s5 := setIndex s4 t 11 ((col + 1 : Nat) : Int) 55
  have hg := LarkReduction.predicate_lt_of (geometry p) t s (.ivar 11) (.const 32)
    (col : Int) 32 hcol (by rfl) (by omega)
  have h1 := execute_branch_of ops (layout p) (geometry p) t 51 56 _ s true hg (by omega)
  have h2 := execute_assign_of ops (layout p) (geometry p) t 6 52
    (.un .exp (.bin .sub (.load .shared 3 (scoreIndex 11)) (.reg 0))) s1 _ weight
    (eval_normalized_weight p ops t col score maximum s1 hc hn.2.1 hcol hm hv) (by simp [s1, advance])
  have h3 := execute_store_of ops (layout p) (geometry p) t 53 .shared 3 (scoreIndex 11) (.reg 6) s2 s2
    (scoreAddress t col) _ weight (eval_score_index (geometry p) t 11 col s2 hc hn.2.1 hcol)
    (score_location p t _ true (score_address_bound t col hc))
    (by simp [evalExpr, s2, setReg, advance]) (by simp [s2, setReg, advance])
  have h4 := execute_pure_of ops (layout p) (geometry p) t 5 54 (.bin .add (.reg 5) (.reg 6)) s3 (ops.add acc weight)
    (by simp [evalExpr, applyBinary, s3, s2, s1, storeState, setReg, record, advance, ha])
    (by simp [s3, storeState, advance])
  have he5 := eval_counter (geometry p) t 11 col s4 hcol (by omega)
  have h5 := execute_index_of ops (layout p) (geometry p) t 11 55 (.add (.ivar 11) (.const 1)) s4
    ((col + 1 : Nat) : Int) he5 (by simp [s4, setReg, advance])
  have e1 := source_step p ops t 50 (extra + 5) _ s s1 (by rfl) hp h1
  have e2 := source_step p ops t 51 (extra + 4) _ s1 s2 exp_assign_code (by simp [s1, advance]) h2
  have e3 := source_step p ops t 52 (extra + 3) _ s2 s3 exp_store_code (by simp [s2, setReg, advance]) h3
  have e4 := source_step p ops t 53 (extra + 2) _ s3 s4 (by rfl) (by simp [s3, storeState, advance]) h4
  have e5 := source_step p ops t 54 (extra + 1) _ s4 s5 (by rfl) (by simp [s4, setReg, advance]) h5
  have e6 := source_step p ops t 55 extra (.jump 50) s5 (expCycle ops t col score maximum acc s) (by rfl)
    (by simp [s5, setIndex, advance]) (by rfl)
  exact e1.trans (e2.trans (e3.trans (e4.trans (e5.trans e6))))

theorem exp_cycle_fields (ops : Ops α) (t col : Nat) (score maximum acc : α) (s : State α) :
    (expCycle ops t col score maximum acc s).pc t = 50 ∧
    (expCycle ops t col score maximum acc s).indices t 11 = some ((col + 1 : Nat) : Int) ∧
    (expCycle ops t col score maximum acc s).regs t 5 = some (ops.add acc (normalizedWeight ops score maximum)) ∧
    (expCycle ops t col score maximum acc s).regs t 0 = s.regs t 0 ∧
    (expCycle ops t col score maximum acc s).epochs = s.epochs := by
  simp [expCycle, storeState, setReg, setIndex, record, advance]

theorem exp_cycle_index (ops : Ops α) (t col r : Nat) (score maximum acc : α) (s : State α) (hr : r ≠ 11) :
    (expCycle ops t col score maximum acc s).indices t r = s.indices t r := by
  simp [expCycle, storeState, setReg, setIndex, record, advance, hr]

theorem exp_cycle_native (ops : Ops α) (t col : Nat) (score maximum acc : α)
    (s : State α) (hn : NativeIndices t s) : NativeIndices t (expCycle ops t col score maximum acc s) :=
  ⟨(exp_cycle_index ops t col 0 score maximum acc s (by decide)).trans hn.1,
   (exp_cycle_index ops t col 1 score maximum acc s (by decide)).trans hn.2.1,
   (exp_cycle_index ops t col 2 score maximum acc s (by decide)).trans hn.2.2⟩

theorem exp_cycle_memory (ops : Ops α) (t col : Nat) (score maximum acc : α) (s : State α) (l : Location) :
    (expCycle ops t col score maximum acc s).memory l = if l = sharedCell t 3 (scoreAddress t col)
      then some (normalizedWeight ops score maximum) else s.memory l := rfl

theorem exp_cycle_range (ops : Ops α) (t col : Nat) (values : Nat → α) (maximum acc : α) (s : State α)
    (hs : ScoreRange t values col 32 s) : ScoreRange t values (col + 1) 32 (expCycle ops t col (values col) maximum acc s) := by
  intro row hr hb
  rw [exp_cycle_memory, if_neg (score_cell_ne t row col (by omega))]
  exact hs row (by omega) hb

theorem exp_cycle_good (ops : Ops α) (t col : Nat) (score maximum acc : α)
    (s : State α) (hc : col < 32) (hg : TraceGood s) : TraceGood (expCycle ops t col score maximum acc s) := by
  exact store_good _ t (sharedCell t 3 (scoreAddress t col)) (normalizedWeight ops score maximum) 53
    (record_good (advance s t 51) t (sharedCell t 3 (scoreAddress t col)) false hg
      (score_access_good t col false (s.epochs t) hc))
    (score_access_good t col true (s.epochs t) hc)

#print axioms exp_cycle_eq
#print axioms exp_cycle_range
#print axioms exp_cycle_good
end LarkNativeAttention
