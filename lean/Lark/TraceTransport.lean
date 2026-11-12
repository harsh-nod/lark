import Lark.Collective

/-! Existing scalar machine execution transports an arbitrary prior trace.
Only the derived relation on states is new; instructions and runner are unchanged.
-/
namespace LarkTraceTransport
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def appendTrace (s : State α) (tail : List Access) : State α := { s with trace := s.trace ++ tail }

theorem append_empty_trace (s : State α) : appendTrace {s with trace := []} s.trace = s := by
  cases s
  rfl

theorem record_append (s : State α) (tail : List Access) (t : Nat) (l : Location) (write : Bool) :
    record (appendTrace s tail) t l write = appendTrace (record s t l write) tail := rfl

theorem advance_append (s : State α) (tail : List Access) (t pc : Nat) :
    advance (appendTrace s tail) t pc = appendTrace (advance s t pc) tail := rfl

theorem eval_index_append (g : Geometry) (t : Nat) (s : State α) (tail : List Access) (ix : Index) :
    evalIndex g t (appendTrace s tail) ix = evalIndex g t s ix := by
  induction ix <;> simp_all [evalIndex,appendTrace]

theorem eval_predicate_append (g : Geometry) (t : Nat) (s : State α) (tail : List Access) (pred : Predicate) :
    evalPredicate g t (appendTrace s tail) pred = evalPredicate g t s pred := by
  cases pred <;> simp only [evalPredicate,eval_index_append]

theorem eval_expr_append (ops : Ops α) (l : Layout) (g : Geometry) (t : Nat)
    (e : Expr) (s : State α) (tail : List Access) :
    evalExpr ops l g t e (appendTrace s tail) =
      (evalExpr ops l g t e s).map (fun value => (value.1,appendTrace value.2 tail)) := by
  induction e generalizing s with
  | lit n d =>
      by_cases hd : d = 0 <;> simp [evalExpr,hd]
  | reg r =>
      cases hv : s.regs t r <;> simp [evalExpr,appendTrace,hv]
  | load space buffer ix =>
      simp only [evalExpr,eval_index_append]
      cases hi : evalIndex g t s ix with
      | none => simp [hi]
      | some i =>
          cases hl : location l g t space buffer i false with
          | none => simp [hi,hl]
          | some cell =>
              cases hm : s.memory cell <;> simp [hi,hl,appendTrace,hm,record]
  | bin op a b iha ihb =>
      simp only [evalExpr,iha]
      cases ha : evalExpr ops l g t a s with
      | none => simp [ha]
      | some value =>
          rcases value with ⟨x,s1⟩
          simp only [ha,Option.map,bind,Option.bind]
          rw [ihb]
          cases hb : evalExpr ops l g t b s1 <;> simp [hb]
  | un op a ih =>
      simp only [evalExpr,ih]
      cases ha : evalExpr ops l g t a s <;> simp [ha]

theorem execute_append (ops : Ops α) (l : Layout) (g : Geometry) (t : Nat)
    (i : Instr) (s : State α) (tail : List Access) :
    execute ops l g t i (appendTrace s tail) = (execute ops l g t i s).map (fun next => appendTrace next tail) := by
  cases i with
  | index r ix =>
      simp only [execute,eval_index_append]
      cases h : evalIndex g t s ix <;> simp [h,appendTrace,advance]
  | assign r e =>
      simp only [execute,eval_expr_append]
      cases h : evalExpr ops l g t e s <;> simp [h,appendTrace,advance]
  | store space buffer ix e =>
      simp only [execute,eval_index_append]
      cases hi : evalIndex g t s ix with
      | none => simp [hi]
      | some index =>
          cases hl : location l g t space buffer index true with
          | none => simp [hi,hl]
          | some cell =>
              simp only [hi,hl,bind,Option.some_bind,eval_expr_append]
              cases he : evalExpr ops l g t e s <;> simp [he,appendTrace,record,advance]
  | branch pred target =>
      simp only [execute,eval_predicate_append]
      cases h : evalPredicate g t s pred <;> simp [h,appendTrace,advance]
  | jump target => rfl
  | barrier cut => rfl
  | halt => rfl

theorem parked_append (p : List LarkCollective.Instr) (s : State α) (tail : List Access) (t : Nat) :
    LarkCollective.parked p (appendTrace s tail) t = LarkCollective.parked p s t := rfl

theorem run_lane_append (ops : Ops α) (l : Layout) (g : Geometry)
    (p : List LarkCollective.Instr) (t fuel : Nat) (s : State α) (tail : List Access) :
    LarkCollective.runLane ops l g p t fuel (appendTrace s tail) =
      (LarkCollective.runLane ops l g p t fuel s).map (fun next => appendTrace next tail) := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih =>
      simp only [LarkCollective.runLane,parked_append]
      cases hp : LarkCollective.parked p s t with
      | some cut => simp [hp]
      | none =>
          simp only [hp]
          have hpc : (appendTrace s tail).pc t = s.pc t := rfl
          simp only [hpc]
          cases hi : p[s.pc t]? with
          | none => simp [hi]
          | some i =>
              cases i with
              | shuffle kind dest src selector width => simp [hi]
              | scalar instruction =>
                  simp only [hi,bind,Option.some_bind,execute_append]
                  cases he : execute ops l g t instruction s with
                  | none => simp [he]
                  | some next => simpa [he] using ih next

#print axioms append_empty_trace
#print axioms record_append
#print axioms advance_append
#print axioms eval_index_append
#print axioms eval_predicate_append
#print axioms eval_expr_append
#print axioms execute_append
#print axioms parked_append
#print axioms run_lane_append
end LarkTraceTransport
