import Lark.NativeAttentionDotColumns

/-! The source's scaled score and its lane-owned shared-memory store. -/
namespace LarkNativeAttention
open LarkNonlinear
open LarkReduction (setReg execute_pure_of)
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def scoreIndex (row : Nat) : Index := .add (.mul (.ivar 1) (.const 32)) (.ivar row)
def rawDotValue (ops : Ops α) (input : Nat → Nat → α) (t qi kj row : Nat) : α :=
  dotFold ops input t qi kj row 0 256 (ops.literal 0 1)
def scoreValue (ops : Ops α) (input : Nat → Nat → α) (t qi kj row : Nat) : α :=
  ops.mul (rawDotValue ops input t qi kj row) (ops.literal 1 16)

theorem score_store_code : program[41]? = some (.store .shared 3 (scoreIndex 9) (.reg 1)) := rfl

theorem eval_score_index (g : Geometry) (t reg row : Nat) (s : State α) (hr : row < 32)
    (hl : s.indices t 1 = some ((t % 32 : Nat) : Int)) (hrow : s.indices t reg = some (row : Int)) :
    evalIndex g t s (scoreIndex reg) = some ((scoreAddress t row : Nat) : Int) := by
  have hm := LarkMatrix.eval_mul_nat g t s (.ivar 1) (.const 32) (t % 32) 32 hl (by rfl) (by omega)
  exact LarkMatrix.eval_add_nat g t s (.mul (.ivar 1) (.const 32)) (.ivar reg)
    (t % 32 * 32) row hm hrow (by omega)

theorem score_store_eq (p : Shape) (ops : Ops α) (t row : Nat) (value : α) (s : State α)
    (hr : row < 32) (hn : NativeIndices t s) (hrow : s.indices t 9 = some (row : Int))
    (hv : s.regs t 1 = some value) (hp : s.pc t = 41) :
    execute ops (layout p) (geometry p) t (.store .shared 3 (scoreIndex 9) (.reg 1)) s =
      some (storeState s t (sharedCell t 3 (scoreAddress t row)) value 42) :=
  execute_store_of ops (layout p) (geometry p) t 42 .shared 3 (scoreIndex 9) (.reg 1) s s
    (scoreAddress t row) _ value (eval_score_index (geometry p) t 9 row s hr hn.2.1 hrow)
    (score_location p t _ true (score_address_bound t row hr))
    (by simp [evalExpr, hv]) (by omega)

def scoreDotFinish (t row : Nat) (value : α) (s : State α) : State α :=
  storeState (setReg s t 1 value 41) t (sharedCell t 3 (scoreAddress t row)) value 42

theorem score_scale_store_eq (p : Shape) (ops : Ops α) (t row extra : Nat) (dot : α) (s : State α)
    (hr : row < 32) (hn : NativeIndices t s) (hrow : s.indices t 9 = some (row : Int))
    (hv : s.regs t 1 = some dot) (hp : s.pc t = 40) :
    runLane ops (layout p) (geometry p) program t (extra + 2) s =
      runLane ops (layout p) (geometry p) program t extra
        (scoreDotFinish t row (ops.mul dot (ops.literal 1 16)) s) := by
  let value := ops.mul dot (ops.literal 1 16)
  let s1 := setReg s t 1 value 41
  have h1 := execute_pure_of ops (layout p) (geometry p) t 1 41 (.bin .mul (.reg 1) (.lit 1 16)) s value
    (by simp [evalExpr, applyBinary, hv, value]) (by omega)
  have h2 := score_store_eq p ops t row value s1 hr hn hrow
    (by simp [s1, setReg, advance]) (by simp [s1, setReg, advance])
  have e1 := source_step p ops t 40 (extra + 1) _ s s1 (by rfl) hp h1
  have e2 := source_step p ops t 41 extra _ s1 (scoreDotFinish t row value s) score_store_code
    (by simp [s1, setReg, advance]) h2
  exact e1.trans e2

theorem score_dot_finish_fields (t row : Nat) (value : α) (s : State α) :
    (scoreDotFinish t row value s).pc t = 42 ∧
    (scoreDotFinish t row value s).indices = s.indices ∧
    (scoreDotFinish t row value s).regs t 1 = some value ∧
    (scoreDotFinish t row value s).epochs = s.epochs := by
  simp [scoreDotFinish, storeState, setReg, record, advance]

theorem score_dot_finish_reg (t row r : Nat) (value : α) (s : State α) (hr : r ≠ 1) :
    (scoreDotFinish t row value s).regs t r = s.regs t r := by
  simp [scoreDotFinish, storeState, setReg, record, advance, hr]

theorem score_dot_finish_memory (t row : Nat) (value : α) (s : State α) (l : Location) :
    (scoreDotFinish t row value s).memory l =
      if l = sharedCell t 3 (scoreAddress t row) then some value else s.memory l := rfl

theorem score_dot_finish_good (t row : Nat) (value : α) (s : State α)
    (hr : row < 32) (hg : TraceGood s) : TraceGood (scoreDotFinish t row value s) :=
  store_good (setReg s t 1 value 41) t _ value 42 hg (score_access_good t row true (s.epochs t) hr)

theorem score_dot_finish_other (t u row : Nat) (value : α) (s : State α) (hne : u ≠ t) :
    (scoreDotFinish t row value s).pc u = s.pc u ∧
    (scoreDotFinish t row value s).indices u = s.indices u ∧
    (scoreDotFinish t row value s).regs u = s.regs u := by
  simp [scoreDotFinish, storeState, setReg, record, advance, hne]

#print axioms score_store_eq
#print axioms score_scale_store_eq
#print axioms score_dot_finish_good
end LarkNativeAttention
