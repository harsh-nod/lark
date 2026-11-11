import Lark.NativeAttentionQueryRow

/-! A query update preserves the old global/private values of every other row. -/
namespace LarkNativeAttention
open LarkNonlinear
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem global_rows_ne (t a b x y : Nat) (hx : x < 256) (hy : y < 256) (hab : a ≠ b) :
    globalCell 0 (globalAddress t a x) ≠ globalCell 0 (globalAddress t b y) := by
  intro he
  have he := congrArg Location.offset he
  simp only [globalCell, globalAddress] at he
  omega

theorem query_row_output_other (ops : Ops α) (input : Nat → Nat → α) (t qi key q col : Nat)
    (old : QueryValue α) (s : State α) (hc : col < 256) (hne : q ≠ qi) :
    (queryRow ops input t qi key old s).memory (globalCell 0 (globalAddress t q col)) =
      s.memory (globalCell 0 (globalAddress t q col)) :=
  query_row_memory_other ops input t qi key old s _
    (by intro c hc; simp [globalCell, sharedCell]) (by intro r hr; simp [globalCell, sharedCell])
    (by intro c hb; exact global_rows_ne t q qi col c hc hb hne)
    (by simp [globalCell, privateCell]) (by simp [globalCell, privateCell])

theorem query_row_private_other (ops : Ops α) (input : Nat → Nat → α) (t qi key buffer q : Nat)
    (old : QueryValue α) (s : State α) (hne : q ≠ qi) :
    (queryRow ops input t qi key old s).memory (privateCell t buffer q) = s.memory (privateCell t buffer q) :=
  query_row_memory_other ops input t qi key old s _
    (by intro c hc; simp [privateCell, sharedCell]) (by intro r hr; simp [privateCell, sharedCell])
    (by intro c hc; simp [privateCell, globalCell]) (by simp [privateCell, hne]) (by simp [privateCell, hne])

theorem query_row_old_other (ops : Ops α) (input : Nat → Nat → α) (t qi key q : Nat)
    (old other : QueryValue α) (s : State α) (hne : q ≠ qi) (ho : OldQuery t q key other s) :
    OldQuery t q key other (queryRow ops input t qi key old s) := by
  constructor
  · intro col hc hb
    exact (query_row_output_other ops input t qi key q col old s hb hne).trans (ho.1 col hc hb)
  · intro hj
    exact ⟨(query_row_private_other ops input t qi key 0 q old s hne).trans (ho.2 hj).1,
      (query_row_private_other ops input t qi key 1 q old s hne).trans (ho.2 hj).2⟩

def QueriesRange (t key : Nat) (old : Nat → QueryValue α) (start stop : Nat) (s : State α) : Prop :=
  ∀ qi, start ≤ qi → qi < stop → OldQuery t qi key (old qi) s

theorem query_row_range (ops : Ops α) (input : Nat → Nat → α) (t qi key stop : Nat)
    (old : Nat → QueryValue α) (s : State α) (ho : QueriesRange t key old qi stop s) :
    QueriesRange t key old (qi + 1) stop (queryRow ops input t qi key (old qi) s) := by
  intro q hq hb
  exact query_row_old_other ops input t qi key q (old qi) (old q) s (by omega) (ho q (by omega) hb)

#print axioms global_rows_ne
#print axioms query_row_old_other
#print axioms query_row_range
end LarkNativeAttention
