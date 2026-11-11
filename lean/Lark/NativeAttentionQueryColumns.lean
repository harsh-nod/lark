import Lark.NativeAttentionQueryCycle

/-! The complete 256-component query copy, using actual lane instructions. -/
namespace LarkNativeAttention
open LarkNonlinear
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def queryColumns (ops : Ops α) (input : Nat → Nat → α) (t tile : Nat) :
    Nat → Nat → State α → State α
  | _, 0, s => advance s t 28
  | col, remaining + 1, s => queryColumns ops input t tile (col + 1) remaining
      (queryCycle ops input t tile col s)

theorem query_columns_exit (p : Shape) (ops : Ops α) (t extra : Nat) (s : State α)
    (hi : s.indices t 8 = some 256) (hp : s.pc t = 24) :
    runLane ops (layout p) (geometry p) program t (extra + 1) s =
      runLane ops (layout p) (geometry p) program t extra (advance s t 28) := by
  have hg := LarkReduction.predicate_nlt_of (geometry p) t s (.ivar 8) (.const 256)
    256 256 hi (by rfl) (by omega)
  have he := execute_branch_of ops (layout p) (geometry p) t 25 28 _ s false hg (by omega)
  exact source_step p ops t 24 extra _ s _ (by rfl) hp he

theorem query_columns_eq (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t tile col remaining extra : Nat) (s : State α)
    (ht : t < p.groups * 32) (hi : tile < 4) (stop : col + remaining = 256)
    (hr : Reads p input s) (hn : NativeIndices t s)
    (hrow : s.indices t 7 = some (tile : Int)) (hcol : s.indices t 8 = some (col : Int))
    (hp : s.pc t = 24) :
    runLane ops (layout p) (geometry p) program t (extra + 4 * remaining + 1) s =
      runLane ops (layout p) (geometry p) program t extra
        (queryColumns ops input t tile col remaining s) := by
  induction remaining generalizing col s with
  | zero =>
      have he : col = 256 := by omega
      subst col
      exact query_columns_exit p ops t extra s hcol hp
  | succ remaining ih =>
      have hf := query_cycle_fields ops input t tile col s
      rw [show extra + 4 * (remaining + 1) + 1 = (extra + 4 * remaining + 1) + 4 by omega,
        query_cycle_eq p ops input t tile col (extra + 4 * remaining + 1) s ht hi (by omega) hr hn hrow hcol hp]
      exact ih (col + 1) (queryCycle ops input t tile col s) (by omega)
        (query_cycle_reads p ops input t tile col s hr) (query_cycle_native ops input t tile col s hn)
        ((query_cycle_index ops input t tile col 7 s (by decide)).trans hrow) hf.2.1 hf.1

theorem query_columns_fields (ops : Ops α) (input : Nat → Nat → α)
    (t tile col remaining : Nat) (s : State α) :
    (queryColumns ops input t tile col remaining s).pc t = 28 ∧
    (queryColumns ops input t tile col remaining s).epochs = s.epochs ∧
    (queryColumns ops input t tile col remaining s).regs = s.regs := by
  induction remaining generalizing col s with
  | zero => exact ⟨by simp [queryColumns, advance], rfl, rfl⟩
  | succ remaining ih =>
      have h := ih (col + 1) (queryCycle ops input t tile col s)
      have hf := query_cycle_fields ops input t tile col s
      exact ⟨h.1, h.2.1.trans hf.2.2.1, h.2.2.trans hf.2.2.2⟩

theorem query_columns_index (ops : Ops α) (input : Nat → Nat → α) (t tile col remaining r : Nat)
    (s : State α) (hr : r ≠ 8) : (queryColumns ops input t tile col remaining s).indices t r = s.indices t r := by
  induction remaining generalizing col s with
  | zero => rfl
  | succ remaining ih =>
      exact (ih (col + 1) (queryCycle ops input t tile col s)).trans
        (query_cycle_index ops input t tile col r s hr)

theorem query_columns_native (ops : Ops α) (input : Nat → Nat → α)
    (t tile col remaining : Nat) (s : State α) (hn : NativeIndices t s) :
    NativeIndices t (queryColumns ops input t tile col remaining s) := by
  induction remaining generalizing col s with
  | zero => exact hn
  | succ remaining ih => exact ih (col + 1) _ (query_cycle_native ops input t tile col s hn)

theorem query_columns_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t tile col remaining : Nat) (s : State α) (hr : Reads p input s) :
    Reads p input (queryColumns ops input t tile col remaining s) := by
  induction remaining generalizing col s with
  | zero => exact hr
  | succ remaining ih => exact ih (col + 1) _ (query_cycle_reads p ops input t tile col s hr)

theorem query_columns_good (ops : Ops α) (input : Nat → Nat → α)
    (t tile col remaining : Nat) (s : State α) (stop : col + remaining = 256) (hg : TraceGood s) :
    TraceGood (queryColumns ops input t tile col remaining s) := by
  induction remaining generalizing col s with
  | zero => exact hg
  | succ remaining ih => exact ih (col + 1) _ (by omega) (query_cycle_good ops input t tile col s (by omega) hg)

theorem query_columns_memory_other (ops : Ops α) (input : Nat → Nat → α)
    (t tile col remaining : Nat) (s : State α) (l : Location)
    (hl : ∀ c, col ≤ c → c < col + remaining → l ≠ sharedCell t 0 (sharedAddress t c)) :
    (queryColumns ops input t tile col remaining s).memory l = s.memory l := by
  induction remaining generalizing col s with
  | zero => rfl
  | succ remaining ih =>
      have h := ih (col + 1) (queryCycle ops input t tile col s)
        (by intro c hc hb; exact hl c (by omega) (by omega))
      rw [query_cycle_memory, if_neg (hl col (by omega) (by omega))] at h
      exact h

theorem query_columns_value (ops : Ops α) (input : Nat → Nat → α)
    (t tile col remaining c : Nat) (s : State α) (hc : col ≤ c) (hb : c < col + remaining) :
    (queryColumns ops input t tile col remaining s).memory (sharedCell t 0 (sharedAddress t c)) =
      some (ops.fromHalf (input 1 (globalAddress t tile c))) := by
  induction remaining generalizing col s with
  | zero => omega
  | succ remaining ih =>
      by_cases he : c = col
      · subst c
        have hf := query_columns_memory_other ops input t tile (col + 1) remaining
          (queryCycle ops input t tile col s) (sharedCell t 0 (sharedAddress t col))
          (by intro c hc hb; exact shared_column_ne t 0 0 col c (by omega))
        exact hf.trans (by rw [query_cycle_memory, if_pos rfl])
      · exact ih (col + 1) (queryCycle ops input t tile col s) (by omega) (by omega)

theorem query_columns_other (ops : Ops α) (input : Nat → Nat → α)
    (t u tile col remaining : Nat) (s : State α) (hne : u ≠ t) :
    (queryColumns ops input t tile col remaining s).pc u = s.pc u ∧
    (queryColumns ops input t tile col remaining s).indices u = s.indices u ∧
    (queryColumns ops input t tile col remaining s).regs u = s.regs u := by
  induction remaining generalizing col s with
  | zero => exact ⟨by simp [queryColumns, advance, hne], rfl, rfl⟩
  | succ remaining ih =>
      have h := ih (col + 1) (queryCycle ops input t tile col s)
      have hf := query_cycle_other ops input t u tile col s hne
      exact ⟨h.1.trans hf.1, h.2.1.trans hf.2.1, h.2.2.trans hf.2.2⟩

#print axioms query_columns_eq
#print axioms query_columns_value
#print axioms query_columns_good
end LarkNativeAttention
