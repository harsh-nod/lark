import Lark.NativeAttentionQueryRange

/-! All four source query rows for one key tile, through the barrier at PC 87. -/
namespace LarkNativeAttention
open LarkNonlinear
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def queryRows (ops : Ops α) (input : Nat → Nat → α) (t key : Nat) (old : Nat → QueryValue α) : Nat → Nat → State α → State α
  | _, 0, s => advance s t 87
  | qi, remaining + 1, s => queryRows ops input t key old (qi + 1) remaining (queryRow ops input t qi key (old qi) s)

theorem query_rows_exit (p : Shape) (ops : Ops α) (t extra : Nat) (s : State α)
    (hq : s.indices t 7 = some 4) (hp : s.pc t = 22) :
    runLane ops (layout p) (geometry p) program t (extra + 1) s =
      runLane ops (layout p) (geometry p) program t extra (advance s t 87) := by
  have hg := LarkReduction.predicate_nlt_of (geometry p) t s (.ivar 7) (.const 4) 4 4 hq (by rfl) (by omega)
  exact source_step p ops t 22 extra _ s _ (by rfl) hp
    (execute_branch_of ops (layout p) (geometry p) t 23 87 _ s false hg (by omega))

theorem query_rows_eq (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (t key : Nat) (old : Nat → QueryValue α)
    (qi remaining extra : Nat) (s : State α) (ht : t < p.groups * 32) (stop : qi + remaining = 4)
    (hr : Reads p input s) (hn : NativeIndices t s) (hk : Tiles ops input t key s)
    (hq : s.indices t 7 = some (qi : Int)) (hj : s.indices t 5 = some (key : Int))
    (ho : QueriesRange t key old qi 4 s) (hp : s.pc t = 22) :
    runLane ops (layout p) (geometry p) program t (extra + (119062 + oldTailFuel key) * remaining + 1) s =
      runLane ops (layout p) (geometry p) program t extra (queryRows ops input t key old qi remaining s) := by
  induction remaining generalizing qi s with
  | zero =>
      have he : qi = 4 := by omega
      subst qi
      exact query_rows_exit p ops t extra s hq hp
  | succ remaining ih =>
      have hi : qi < 4 := by omega
      let next := queryRow ops input t qi key (old qi) s
      have hf := query_row_fields ops input t qi key (old qi) s
      have steps : extra + (119062 + oldTailFuel key) * (remaining + 1) + 1 =
          (extra + (119062 + oldTailFuel key) * remaining + 1) + (119062 + oldTailFuel key) := by
        rw [Nat.mul_succ]
        omega
      rw [steps, query_row_eq p ops input t qi key (extra + (119062 + oldTailFuel key) * remaining + 1) (old qi) s
        ht hi hr hn hk hq hj (ho qi (by omega) hi) hp]
      exact ih (qi + 1) next (by omega) (query_row_reads p ops input t qi key (old qi) s hr)
        (query_row_native ops input t qi key (old qi) s hn) (query_row_tiles ops input t qi key (old qi) s hk) hf.2.1
        ((query_row_index ops input t qi key 5 (old qi) s (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hj)
        (query_row_range ops input t qi key 4 old s ho) hf.1

theorem query_rows_fields (ops : Ops α) (input : Nat → Nat → α) (t key : Nat) (old : Nat → QueryValue α)
    (qi remaining : Nat) (s : State α) :
    (queryRows ops input t key old qi remaining s).pc t = 87 ∧
    (queryRows ops input t key old qi remaining s).epochs = s.epochs := by
  induction remaining generalizing qi s with
  | zero => exact ⟨by simp [queryRows, advance], rfl⟩
  | succ remaining ih =>
      have hf := ih (qi + 1) (queryRow ops input t qi key (old qi) s)
      exact ⟨hf.1, hf.2.trans (query_row_fields ops input t qi key (old qi) s).2.2⟩

theorem query_rows_index (ops : Ops α) (input : Nat → Nat → α) (t key : Nat) (old : Nat → QueryValue α)
    (qi remaining r : Nat) (s : State α)
    (h7 : r ≠ 7) (h8 : r ≠ 8) (h9 : r ≠ 9) (h10 : r ≠ 10) (h11 : r ≠ 11) (h12 : r ≠ 12) (h13 : r ≠ 13) :
    (queryRows ops input t key old qi remaining s).indices t r = s.indices t r := by
  induction remaining generalizing qi s with
  | zero => rfl
  | succ remaining ih =>
      exact (ih (qi + 1) (queryRow ops input t qi key (old qi) s)).trans
        (query_row_index ops input t qi key r (old qi) s h7 h8 h9 h10 h11 h12 h13)

theorem query_rows_native (ops : Ops α) (input : Nat → Nat → α) (t key : Nat) (old : Nat → QueryValue α)
    (qi remaining : Nat) (s : State α) (hn : NativeIndices t s) : NativeIndices t (queryRows ops input t key old qi remaining s) := by
  induction remaining generalizing qi s with
  | zero => exact hn
  | succ remaining ih => exact ih (qi + 1) _ (query_row_native ops input t qi key (old qi) s hn)

theorem query_rows_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (t key : Nat) (old : Nat → QueryValue α)
    (qi remaining : Nat) (s : State α) (hr : Reads p input s) : Reads p input (queryRows ops input t key old qi remaining s) := by
  induction remaining generalizing qi s with
  | zero => exact hr
  | succ remaining ih => exact ih (qi + 1) _ (query_row_reads p ops input t qi key (old qi) s hr)

theorem query_rows_tiles (ops : Ops α) (input : Nat → Nat → α) (t key : Nat) (old : Nat → QueryValue α)
    (qi remaining : Nat) (s : State α) (hk : Tiles ops input t key s) : Tiles ops input t key (queryRows ops input t key old qi remaining s) := by
  induction remaining generalizing qi s with
  | zero => exact hk
  | succ remaining ih => exact ih (qi + 1) _ (query_row_tiles ops input t qi key (old qi) s hk)

theorem query_rows_output_other (ops : Ops α) (input : Nat → Nat → α) (t key : Nat) (old : Nat → QueryValue α)
    (qi remaining q col : Nat) (s : State α) (hc : col < 256)
    (hne : ∀ r, qi ≤ r → r < qi + remaining → q ≠ r) :
    (queryRows ops input t key old qi remaining s).memory (globalCell 0 (globalAddress t q col)) =
      s.memory (globalCell 0 (globalAddress t q col)) := by
  induction remaining generalizing qi s with
  | zero => rfl
  | succ remaining ih =>
      exact (ih (qi + 1) (queryRow ops input t qi key (old qi) s) (by intro r hr hb; exact hne r (by omega) (by omega))).trans
        (query_row_output_other ops input t qi key q col (old qi) s hc (hne qi (by omega) (by omega)))

theorem query_rows_private_other (ops : Ops α) (input : Nat → Nat → α) (t key : Nat) (old : Nat → QueryValue α)
    (qi remaining buffer q : Nat) (s : State α) (hne : ∀ r, qi ≤ r → r < qi + remaining → q ≠ r) :
    (queryRows ops input t key old qi remaining s).memory (privateCell t buffer q) = s.memory (privateCell t buffer q) := by
  induction remaining generalizing qi s with
  | zero => rfl
  | succ remaining ih =>
      exact (ih (qi + 1) (queryRow ops input t qi key (old qi) s) (by intro r hr hb; exact hne r (by omega) (by omega))).trans
        (query_row_private_other ops input t qi key buffer q (old qi) s (hne qi (by omega) (by omega)))

theorem query_rows_value (ops : Ops α) (input : Nat → Nat → α) (t key : Nat) (old : Nat → QueryValue α)
    (qi remaining q col : Nat) (s : State α) (hq : qi ≤ q) (hb : q < qi + remaining) (hc : col < 256) :
    (queryRows ops input t key old qi remaining s).memory (globalCell 0 (globalAddress t q col)) =
      some ((nextQueryValue ops input t q key (old q)).stored col) := by
  induction remaining generalizing qi s with
  | zero => omega
  | succ remaining ih =>
      by_cases he : q = qi
      · subst q
        exact (query_rows_output_other ops input t key old (qi + 1) remaining qi col (queryRow ops input t qi key (old qi) s)
          hc (by intro r hr hb; omega)).trans (query_row_value ops input t qi key col (old qi) s hc)
      · exact ih (qi + 1) (queryRow ops input t qi key (old qi) s) (by omega) (by omega)

theorem query_rows_private (ops : Ops α) (input : Nat → Nat → α) (t key : Nat) (old : Nat → QueryValue α)
    (qi remaining q : Nat) (s : State α) (hq : qi ≤ q) (hb : q < qi + remaining) :
    (queryRows ops input t key old qi remaining s).memory (privateCell t 0 q) = some (nextQueryValue ops input t q key (old q)).maximum ∧
    (queryRows ops input t key old qi remaining s).memory (privateCell t 1 q) = some (nextQueryValue ops input t q key (old q)).mass := by
  induction remaining generalizing qi s with
  | zero => omega
  | succ remaining ih =>
      by_cases he : q = qi
      · subst q
        have hf := query_row_private ops input t qi key (old qi) s
        exact ⟨(query_rows_private_other ops input t key old (qi + 1) remaining 0 qi (queryRow ops input t qi key (old qi) s)
          (by intro r hr hb; omega)).trans hf.1,
          (query_rows_private_other ops input t key old (qi + 1) remaining 1 qi (queryRow ops input t qi key (old qi) s)
          (by intro r hr hb; omega)).trans hf.2⟩
      · exact ih (qi + 1) (queryRow ops input t qi key (old qi) s) (by omega) (by omega)

theorem query_rows_good (ops : Ops α) (input : Nat → Nat → α) (t key : Nat) (old : Nat → QueryValue α)
    (qi remaining : Nat) (s : State α) (stop : qi + remaining = 4)
    (he : (s.epochs t).block % 2 = 1) (hg : TraceGood s) : TraceGood (queryRows ops input t key old qi remaining s) := by
  induction remaining generalizing qi s with
  | zero => exact hg
  | succ remaining ih =>
      have hf := query_row_fields ops input t qi key (old qi) s
      exact ih (qi + 1) _ (by omega) (by simpa only [hf.2.2] using he)
        (query_row_good ops input t qi key (old qi) s (by omega) he hg)

#print axioms query_rows_eq
#print axioms query_rows_fields
#print axioms query_rows_value
#print axioms query_rows_private
#print axioms query_rows_reads
#print axioms query_rows_tiles
#print axioms query_rows_good
end LarkNativeAttention
