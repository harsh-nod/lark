import Lark.NativeAttentionDotLoad

/-! Seven actual source instructions of one Q/K dot-product iteration. -/
namespace LarkNativeAttention
open LarkNonlinear
open LarkReduction (setIndex setReg execute_index_of execute_pure_of)
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def dotTerm (ops : Ops α) (input : Nat → Nat → α) (t qi kj row col : Nat) : α :=
  ops.mul (qValue ops input t qi col) (kValue ops input t kj row col)
def dotNext (ops : Ops α) (input : Nat → Nat → α) (t qi kj row col : Nat) (acc : α) : α :=
  ops.add acc (dotTerm ops input t qi kj row col)

def dotCycle (ops : Ops α) (input : Nat → Nat → α) (t qi kj row col : Nat) (acc : α) (s : State α) : State α :=
  let s := advance s t 34
  let s := setReg (record s t (sharedCell t 0 (sharedAddress t col)) false) t 2 (qValue ops input t qi col) 35
  let s := setReg (record s t (sharedCell t 1 (row * 256 + col)) false) t 3 (kValue ops input t kj row col) 36
  let s := setReg s t 4 (dotTerm ops input t qi kj row col) 37
  let s := setReg s t 1 (dotNext ops input t qi kj row col acc) 38
  let s := setIndex s t 10 ((col + 1 : Nat) : Int) 39
  advance s t 33

theorem dot_cycle_eq (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t qi kj row col extra : Nat) (acc : α) (s : State α) (hr : row < 32) (hc : col < 256)
    (hq : QiReady ops input t qi s) (hk : Tiles ops input t kj s) (hn : NativeIndices t s)
    (hrow : s.indices t 9 = some (row : Int)) (hcol : s.indices t 10 = some (col : Int))
    (hacc : s.regs t 1 = some acc) (hp : s.pc t = 33) :
    runLane ops (layout p) (geometry p) program t (extra + 7) s =
      runLane ops (layout p) (geometry p) program t extra (dotCycle ops input t qi kj row col acc s) := by
  let s1 := advance s t 34
  let s2 := setReg (record s1 t (sharedCell t 0 (sharedAddress t col)) false) t 2 (qValue ops input t qi col) 35
  let s3 := setReg (record s2 t (sharedCell t 1 (row * 256 + col)) false) t 3 (kValue ops input t kj row col) 36
  let s4 := setReg s3 t 4 (dotTerm ops input t qi kj row col) 37
  let s5 := setReg s4 t 1 (dotNext ops input t qi kj row col acc) 38
  let s6 := setIndex s5 t 10 ((col + 1 : Nat) : Int) 39
  have hg := LarkReduction.predicate_lt_of (geometry p) t s (.ivar 10) (.const 256)
    (col : Int) 256 hcol (by rfl) (by omega)
  have h1 := execute_branch_of ops (layout p) (geometry p) t 34 40 _ s true hg (by omega)
  have h2 := execute_assign_of ops (layout p) (geometry p) t 2 35 (.load .shared 0 (sharedIndex 10)) s1 _ _
    (load_query p ops input t qi col s1 hc hq hn.2.1 hcol) (by simp [s1, advance])
  have h3 := execute_assign_of ops (layout p) (geometry p) t 3 36 (.load .shared 1 (tileIndex 9 10)) s2 _ _
    (load_key p ops input t kj row col s2 hr hc hk hrow hcol) (by simp [s2, setReg, advance])
  have h4 := execute_pure_of ops (layout p) (geometry p) t 4 37 (.bin .mul (.reg 2) (.reg 3)) s3
    (dotTerm ops input t qi kj row col)
    (by simp [evalExpr, applyBinary, dotTerm, s3, s2, setReg, advance, record])
    (by simp [s3, setReg, advance])
  have h5 := execute_pure_of ops (layout p) (geometry p) t 1 38 (.bin .add (.reg 1) (.reg 4)) s4
    (dotNext ops input t qi kj row col acc)
    (by simp [evalExpr, applyBinary, dotNext, s4, s3, s2, s1, setReg, advance, record, hacc])
    (by simp [s4, setReg, advance])
  have he6 := eval_counter (geometry p) t 10 col s5 hcol (by omega)
  have h6 := execute_index_of ops (layout p) (geometry p) t 10 39 (.add (.ivar 10) (.const 1)) s5
    ((col + 1 : Nat) : Int) he6 (by simp [s5, setReg, advance])
  have e1 := source_step p ops t 33 (extra + 6) _ s s1 (by rfl) hp h1
  have e2 := source_step p ops t 34 (extra + 5) _ s1 s2 query_read_code (by simp [s1, advance]) h2
  have e3 := source_step p ops t 35 (extra + 4) _ s2 s3 key_read_code (by simp [s2, setReg, advance]) h3
  have e4 := source_step p ops t 36 (extra + 3) _ s3 s4 (by rfl) (by simp [s3, setReg, advance]) h4
  have e5 := source_step p ops t 37 (extra + 2) _ s4 s5 (by rfl) (by simp [s4, setReg, advance]) h5
  have e6 := source_step p ops t 38 (extra + 1) _ s5 s6 (by rfl) (by simp [s5, setReg, advance]) h6
  have e7 := source_step p ops t 39 extra (.jump 33) s6 (dotCycle ops input t qi kj row col acc s)
    (by rfl) (by simp [s6, setIndex, advance]) (by rfl)
  exact e1.trans (e2.trans (e3.trans (e4.trans (e5.trans (e6.trans e7)))))

theorem dot_cycle_fields (ops : Ops α) (input : Nat → Nat → α) (t qi kj row col : Nat)
    (acc : α) (s : State α) :
    (dotCycle ops input t qi kj row col acc s).pc t = 33 ∧
    (dotCycle ops input t qi kj row col acc s).indices t 10 = some ((col + 1 : Nat) : Int) ∧
    (dotCycle ops input t qi kj row col acc s).regs t 1 = some (dotNext ops input t qi kj row col acc) ∧
    (dotCycle ops input t qi kj row col acc s).epochs = s.epochs ∧
    (dotCycle ops input t qi kj row col acc s).memory = s.memory := by
  simp [dotCycle, setReg, setIndex, advance, record]

theorem dot_cycle_index (ops : Ops α) (input : Nat → Nat → α) (t qi kj row col r : Nat)
    (acc : α) (s : State α) (hr : r ≠ 10) :
    (dotCycle ops input t qi kj row col acc s).indices t r = s.indices t r := by
  simp [dotCycle, setReg, setIndex, advance, record, hr]

theorem dot_cycle_native (ops : Ops α) (input : Nat → Nat → α) (t qi kj row col : Nat)
    (acc : α) (s : State α) (hn : NativeIndices t s) : NativeIndices t (dotCycle ops input t qi kj row col acc s) :=
  ⟨(dot_cycle_index ops input t qi kj row col 0 acc s (by decide)).trans hn.1,
   (dot_cycle_index ops input t qi kj row col 1 acc s (by decide)).trans hn.2.1,
   (dot_cycle_index ops input t qi kj row col 2 acc s (by decide)).trans hn.2.2⟩

theorem dot_cycle_reg (ops : Ops α) (input : Nat → Nat → α) (t qi kj row col r : Nat)
    (acc : α) (s : State α) (h1 : r ≠ 1) (h2 : r ≠ 2) (h3 : r ≠ 3) (h4 : r ≠ 4) :
    (dotCycle ops input t qi kj row col acc s).regs t r = s.regs t r := by
  simp [dotCycle, setReg, setIndex, advance, record, h1, h2, h3, h4]

theorem dot_cycle_good (ops : Ops α) (input : Nat → Nat → α) (t qi kj row col : Nat)
    (acc : α) (s : State α) (hc : col < 256) (he : (s.epochs t).block % 2 = 1) (hg : TraceGood s) :
    TraceGood (dotCycle ops input t qi kj row col acc s) := by
  exact record_good _ t (sharedCell t 1 (row * 256 + col)) false
    (record_good (advance s t 34) t (sharedCell t 0 (sharedAddress t col)) false hg
      (qi_access_good t col false (s.epochs t) hc)) (key_read_good t row col (s.epochs t) he)

theorem dot_cycle_other (ops : Ops α) (input : Nat → Nat → α) (t u qi kj row col : Nat)
    (acc : α) (s : State α) (hne : u ≠ t) :
    (dotCycle ops input t qi kj row col acc s).pc u = s.pc u ∧
    (dotCycle ops input t qi kj row col acc s).indices u = s.indices u ∧
    (dotCycle ops input t qi kj row col acc s).regs u = s.regs u := by
  simp [dotCycle, setReg, setIndex, advance, record, hne]

#print axioms dot_cycle_eq
#print axioms dot_cycle_good
end LarkNativeAttention
