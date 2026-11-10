import Lark.NativeAttentionZeroCycle

/-! Actual 256-component output zero loop, including the final false guard. -/
namespace LarkNativeAttention
open LarkNonlinear
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def zeroColumns (ops : Ops α) (t tile : Nat) : Nat → Nat → State α → State α
  | _, 0, s => advance s t 10
  | col, remaining + 1, s => zeroColumns ops t tile (col + 1) remaining
      (zeroCycle ops t tile col s)

theorem zero_columns_exit (p : Shape) (ops : Ops α) (t extra : Nat) (s : State α)
    (hi : s.indices t 4 = some 256) (hp : s.pc t = 6) :
    runLane ops (layout p) (geometry p) program t (extra + 1) s =
      runLane ops (layout p) (geometry p) program t extra (advance s t 10) := by
  have hg := LarkReduction.predicate_nlt_of (geometry p) t s (.ivar 4) (.const 256)
    256 256 hi (by rfl) (by omega)
  have he := execute_branch_of ops (layout p) (geometry p) t 7 10 _ s false hg (by omega)
  exact source_step p ops t 6 extra _ s _ (by rfl) hp he

theorem zero_columns_eq (p : Shape) (ops : Ops α) (t tile col remaining extra : Nat)
    (s : State α) (ht : t < p.groups * 32) (hi : tile < 4)
    (stop : col + remaining = 256) (hn : NativeIndices t s)
    (hrow : s.indices t 3 = some (tile : Int)) (hcol : s.indices t 4 = some (col : Int))
    (hp : s.pc t = 6) :
    runLane ops (layout p) (geometry p) program t (extra + 4 * remaining + 1) s =
      runLane ops (layout p) (geometry p) program t extra
        (zeroColumns ops t tile col remaining s) := by
  induction remaining generalizing col s with
  | zero =>
      have he : col = 256 := by omega
      subst col
      exact zero_columns_exit p ops t extra s hcol hp
  | succ remaining ih =>
      have hc : col < 256 := by omega
      have hf := zero_cycle_fields ops t tile col s
      rw [show extra + 4 * (remaining + 1) + 1 = (extra + 4 * remaining + 1) + 4 by omega,
        zero_cycle_eq p ops t tile col (extra + 4 * remaining + 1) s ht hi hc hn hrow hcol hp]
      exact ih (col + 1) (zeroCycle ops t tile col s) (by omega)
        (zero_cycle_native ops t tile col s hn) (hf.2.1.trans hrow) hf.2.2.1 hf.1

theorem zero_columns_fields (ops : Ops α) (t tile col remaining : Nat) (s : State α) :
    (zeroColumns ops t tile col remaining s).pc t = 10 ∧
    (zeroColumns ops t tile col remaining s).indices t 3 = s.indices t 3 ∧
    (zeroColumns ops t tile col remaining s).epochs = s.epochs := by
  induction remaining generalizing col s with
  | zero => exact ⟨by simp [zeroColumns, advance], rfl, rfl⟩
  | succ remaining ih =>
      have h := ih (col + 1) (zeroCycle ops t tile col s)
      have hf := zero_cycle_fields ops t tile col s
      exact ⟨h.1, h.2.1.trans hf.2.1, h.2.2.trans hf.2.2.2⟩

theorem zero_columns_native (ops : Ops α) (t tile col remaining : Nat) (s : State α)
    (hn : NativeIndices t s) : NativeIndices t (zeroColumns ops t tile col remaining s) := by
  induction remaining generalizing col s with
  | zero => exact hn
  | succ remaining ih => exact ih (col + 1) _ (zero_cycle_native ops t tile col s hn)

theorem zero_columns_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t tile col remaining : Nat) (s : State α) (hr : Reads p input s) :
    Reads p input (zeroColumns ops t tile col remaining s) := by
  induction remaining generalizing col s with
  | zero => exact hr
  | succ remaining ih => exact ih (col + 1) _ (zero_cycle_reads p ops input t tile col s hr)

theorem zero_columns_good (ops : Ops α) (t tile col remaining : Nat) (s : State α)
    (hi : tile < 4) (stop : col + remaining = 256) (hg : TraceGood s) :
    TraceGood (zeroColumns ops t tile col remaining s) := by
  induction remaining generalizing col s with
  | zero => exact hg
  | succ remaining ih =>
      exact ih (col + 1) _ (by omega) (zero_cycle_good ops t tile col s hi (by omega) hg)

theorem zero_columns_memory_other (ops : Ops α) (t tile col remaining : Nat)
    (s : State α) (l : Location)
    (hl : ∀ c, col ≤ c → c < col + remaining → l ≠ globalCell 0 (globalAddress t tile c)) :
    (zeroColumns ops t tile col remaining s).memory l = s.memory l := by
  induction remaining generalizing col s with
  | zero => rfl
  | succ remaining ih =>
      have h := ih (col + 1) (zeroCycle ops t tile col s)
        (by intro c hc hb; exact hl c (by omega) (by omega))
      rw [zero_cycle_memory, if_neg (hl col (by omega) (by omega))] at h
      exact h

theorem global_column_ne (t tile a b : Nat) (hab : a ≠ b) :
    globalCell 0 (globalAddress t tile a) ≠ globalCell 0 (globalAddress t tile b) := by
  intro he
  have he := congrArg Location.offset he
  simp only [globalCell, globalAddress] at he
  omega

theorem zero_columns_value (ops : Ops α) (t tile col remaining c : Nat)
    (s : State α) (hc : col ≤ c) (hb : c < col + remaining) :
    (zeroColumns ops t tile col remaining s).memory (globalCell 0 (globalAddress t tile c)) =
      some (zeroValue ops) := by
  induction remaining generalizing col s with
  | zero => omega
  | succ remaining ih =>
      by_cases he : c = col
      · subst c
        have hf := zero_columns_memory_other ops t tile (col + 1) remaining
          (zeroCycle ops t tile col s) (globalCell 0 (globalAddress t tile col))
          (by intro c hc hb; exact global_column_ne t tile col c (by omega))
        exact hf.trans (by rw [zero_cycle_memory, if_pos rfl])
      · exact ih (col + 1) (zeroCycle ops t tile col s) (by omega) (by omega)

theorem zero_columns_other (ops : Ops α) (t u tile col remaining : Nat)
    (s : State α) (hne : u ≠ t) :
    (zeroColumns ops t tile col remaining s).pc u = s.pc u ∧
    (zeroColumns ops t tile col remaining s).indices u = s.indices u ∧
    (zeroColumns ops t tile col remaining s).regs u = s.regs u := by
  induction remaining generalizing col s with
  | zero => exact ⟨by simp [zeroColumns, advance, hne], rfl, rfl⟩
  | succ remaining ih =>
      have h := ih (col + 1) (zeroCycle ops t tile col s)
      have hf := zero_cycle_other ops t u tile col s hne
      exact ⟨h.1.trans hf.1, h.2.1.trans hf.2.1, h.2.2.trans hf.2.2⟩

#print axioms zero_columns_eq
#print axioms zero_columns_value
#print axioms zero_columns_good
end LarkNativeAttention
