import Lark.NativeAttentionFirstOutput

/-! The actual private-state stores and query-counter increment at PC 83–86. -/
namespace LarkNativeAttention
open LarkNonlinear
open LarkReduction (setIndex execute_index_of)
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def queryTail (t qi : Nat) (scales : ScaleValues α) (s : State α) : State α :=
  let s := storeState s t (privateCell t 0 qi) scales.maximum 84
  let s := storeState s t (privateCell t 1 qi) scales.mass 85
  advance (setIndex s t 7 ((qi + 1 : Nat) : Int) 86) t 22

theorem query_tail_eq (p : Shape) (ops : Ops α) (t qi extra : Nat) (scales : ScaleValues α) (oldMass : α)
    (s : State α) (hi : qi < 4) (hq : s.indices t 7 = some (qi : Int))
    (hr : ScaleReady t scales oldMass s) (hp : s.pc t = 83) :
    runLane ops (layout p) (geometry p) program t (extra + 4) s =
      runLane ops (layout p) (geometry p) program t extra (queryTail t qi scales s) := by
  let s1 := storeState s t (privateCell t 0 qi) scales.maximum 84
  let s2 := storeState s1 t (privateCell t 1 qi) scales.mass 85
  let s3 := setIndex s2 t 7 ((qi + 1 : Nat) : Int) 86
  have h1 := execute_store_of ops (layout p) (geometry p) t 84 .local 0 (.ivar 7) (.reg 9)
    s s (qi : Int) (privateCell t 0 qi) scales.maximum hq
    (private_location p t 0 qi true (Or.inl rfl) hi)
    (by simp [evalExpr, hr.maximum]) (by omega)
  have h2 := execute_store_of ops (layout p) (geometry p) t 85 .local 1 (.ivar 7) (.reg 12)
    s1 s1 (qi : Int) (privateCell t 1 qi) scales.mass hq
    (private_location p t 1 qi true (Or.inr rfl) hi)
    (by simp [evalExpr, s1, storeState, record, advance, hr.mass]) (by simp [s1, storeState, advance])
  have h3 := execute_index_of ops (layout p) (geometry p) t 7 86 (.add (.ivar 7) (.const 1)) s2
    ((qi + 1 : Nat) : Int) (eval_counter (geometry p) t 7 qi s2 hq (by omega))
    (by simp [s2, storeState, advance])
  have e1 := source_step p ops t 83 (extra + 3) _ s s1 (by rfl) hp h1
  have e2 := source_step p ops t 84 (extra + 2) _ s1 s2 (by rfl) (by simp [s1, storeState, advance]) h2
  have e3 := source_step p ops t 85 (extra + 1) _ s2 s3 (by rfl) (by simp [s2, storeState, advance]) h3
  have e4 := source_step p ops t 86 extra (.jump 22) s3 (queryTail t qi scales s)
    (by rfl) (by simp [s3, setIndex, advance]) (by rfl)
  exact e1.trans (e2.trans (e3.trans e4))

theorem query_tail_fields (t qi : Nat) (scales : ScaleValues α) (s : State α) :
    (queryTail t qi scales s).pc t = 22 ∧
    (queryTail t qi scales s).indices t 7 = some ((qi + 1 : Nat) : Int) ∧
    (queryTail t qi scales s).epochs = s.epochs ∧ (queryTail t qi scales s).regs = s.regs := by
  simp [queryTail, storeState, setIndex, record, advance]

theorem query_tail_index (t qi r : Nat) (scales : ScaleValues α) (s : State α) (hr : r ≠ 7) :
    (queryTail t qi scales s).indices t r = s.indices t r := by
  simp [queryTail, storeState, setIndex, record, advance, hr]

theorem query_tail_memory (t qi : Nat) (scales : ScaleValues α) (s : State α) (l : Location) :
    (queryTail t qi scales s).memory l =
      if l = privateCell t 1 qi then some scales.mass else
      if l = privateCell t 0 qi then some scales.maximum else s.memory l := rfl

theorem query_tail_values (t qi : Nat) (scales : ScaleValues α) (s : State α) :
    (queryTail t qi scales s).memory (privateCell t 0 qi) = some scales.maximum ∧
    (queryTail t qi scales s).memory (privateCell t 1 qi) = some scales.mass := by
  constructor <;> rw [query_tail_memory] <;> simp [privateCell]

theorem query_tail_global (t qi buffer index : Nat) (scales : ScaleValues α) (s : State α) :
    (queryTail t qi scales s).memory (globalCell buffer index) = s.memory (globalCell buffer index) := by
  rw [query_tail_memory]
  simp [globalCell, privateCell]

theorem query_tail_good (t qi : Nat) (scales : ScaleValues α) (s : State α) (hg : TraceGood s) :
    TraceGood (queryTail t qi scales s) :=
  store_good _ t (privateCell t 1 qi) scales.mass 85
    (store_good s t (privateCell t 0 qi) scales.maximum 84 hg (private_access_good t 0 qi true (s.epochs t)))
    (private_access_good t 1 qi true (s.epochs t))

#print axioms query_tail_eq
#print axioms query_tail_values
#print axioms query_tail_global
#print axioms query_tail_good
end LarkNativeAttention
