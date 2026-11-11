import Lark.NativeAttentionExpCycle

/-! All 32 in-place exponential updates and the ordered denominator fold. -/
namespace LarkNativeAttention
open LarkNonlinear
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def expFold (ops : Ops α) (values : Nat → α) (maximum : α) : Nat → Nat → α → α
  | _, 0, acc => acc
  | col, remaining + 1, acc => expFold ops values maximum (col + 1) remaining
      (ops.add acc (normalizedWeight ops (values col) maximum))
def expColumns (ops : Ops α) (t : Nat) (values : Nat → α) (maximum : α) :
    Nat → Nat → α → State α → State α
  | _, 0, _, s => advance s t 56
  | col, remaining + 1, acc, s => expColumns ops t values maximum (col + 1) remaining
      (ops.add acc (normalizedWeight ops (values col) maximum)) (expCycle ops t col (values col) maximum acc s)

theorem exp_columns_exit (p : Shape) (ops : Ops α) (t extra : Nat) (s : State α)
    (hi : s.indices t 11 = some 32) (hp : s.pc t = 50) :
    runLane ops (layout p) (geometry p) program t (extra + 1) s =
      runLane ops (layout p) (geometry p) program t extra (advance s t 56) := by
  have hg := LarkReduction.predicate_nlt_of (geometry p) t s (.ivar 11) (.const 32) 32 32 hi (by rfl) (by omega)
  have he := execute_branch_of ops (layout p) (geometry p) t 51 56 _ s false hg (by omega)
  exact source_step p ops t 50 extra _ s _ (by rfl) hp he

theorem exp_columns_eq (p : Shape) (ops : Ops α) (t : Nat) (values : Nat → α)
    (col remaining extra : Nat) (maximum acc : α) (s : State α) (stop : col + remaining = 32)
    (hs : ScoreRange t values col 32 s) (hn : NativeIndices t s) (hi : s.indices t 11 = some (col : Int))
    (hm : s.regs t 0 = some maximum) (ha : s.regs t 5 = some acc) (hp : s.pc t = 50) :
    runLane ops (layout p) (geometry p) program t (extra + 6 * remaining + 1) s =
      runLane ops (layout p) (geometry p) program t extra (expColumns ops t values maximum col remaining acc s) := by
  induction remaining generalizing col acc s with
  | zero =>
      have he : col = 32 := by omega
      subst col
      exact exp_columns_exit p ops t extra s hi hp
  | succ remaining ih =>
      have hc : col < 32 := by omega
      have hf := exp_cycle_fields ops t col (values col) maximum acc s
      rw [show extra + 6 * (remaining + 1) + 1 = (extra + 6 * remaining + 1) + 6 by omega,
        exp_cycle_eq p ops t col (extra + 6 * remaining + 1) (values col) maximum acc s hc hn hi hm ha
          (hs col (by omega) hc) hp]
      exact ih (col + 1) (ops.add acc (normalizedWeight ops (values col) maximum)) _ (by omega)
        (exp_cycle_range ops t col values maximum acc s hs)
        (exp_cycle_native ops t col (values col) maximum acc s hn) hf.2.1 (hf.2.2.2.1.trans hm) hf.2.2.1 hf.1

theorem exp_columns_fields (ops : Ops α) (t : Nat) (values : Nat → α)
    (col remaining : Nat) (maximum acc : α) (s : State α) :
    (expColumns ops t values maximum col remaining acc s).pc t = 56 ∧
    (expColumns ops t values maximum col remaining acc s).regs t 0 = s.regs t 0 ∧
    (expColumns ops t values maximum col remaining acc s).epochs = s.epochs := by
  induction remaining generalizing col acc s with
  | zero => exact ⟨by simp [expColumns, advance], rfl, rfl⟩
  | succ remaining ih =>
      have h := ih (col + 1) (ops.add acc (normalizedWeight ops (values col) maximum))
        (expCycle ops t col (values col) maximum acc s)
      have hf := exp_cycle_fields ops t col (values col) maximum acc s
      exact ⟨h.1, h.2.1.trans hf.2.2.2.1, h.2.2.trans hf.2.2.2.2⟩

theorem exp_columns_sum (ops : Ops α) (t : Nat) (values : Nat → α)
    (col remaining : Nat) (maximum acc : α) (s : State α) (ha : s.regs t 5 = some acc) :
    (expColumns ops t values maximum col remaining acc s).regs t 5 = some (expFold ops values maximum col remaining acc) := by
  induction remaining generalizing col acc s with
  | zero => exact ha
  | succ remaining ih =>
      exact ih (col + 1) (ops.add acc (normalizedWeight ops (values col) maximum)) _
        (exp_cycle_fields ops t col (values col) maximum acc s).2.2.1

theorem exp_columns_index (ops : Ops α) (t : Nat) (values : Nat → α)
    (col remaining r : Nat) (maximum acc : α) (s : State α) (hr : r ≠ 11) :
    (expColumns ops t values maximum col remaining acc s).indices t r = s.indices t r := by
  induction remaining generalizing col acc s with
  | zero => rfl
  | succ remaining ih =>
      exact (ih (col + 1) (ops.add acc (normalizedWeight ops (values col) maximum))
        (expCycle ops t col (values col) maximum acc s)).trans (exp_cycle_index ops t col r (values col) maximum acc s hr)

theorem exp_columns_native (ops : Ops α) (t : Nat) (values : Nat → α)
    (col remaining : Nat) (maximum acc : α) (s : State α) (hn : NativeIndices t s) :
    NativeIndices t (expColumns ops t values maximum col remaining acc s) := by
  induction remaining generalizing col acc s with
  | zero => exact hn
  | succ remaining ih =>
      exact ih (col + 1) (ops.add acc (normalizedWeight ops (values col) maximum)) _
        (exp_cycle_native ops t col (values col) maximum acc s hn)

theorem exp_columns_memory_other (ops : Ops α) (t : Nat) (values : Nat → α)
    (col remaining : Nat) (maximum acc : α) (s : State α) (l : Location)
    (hl : ∀ c, col ≤ c → c < col + remaining → l ≠ sharedCell t 3 (scoreAddress t c)) :
    (expColumns ops t values maximum col remaining acc s).memory l = s.memory l := by
  induction remaining generalizing col acc s with
  | zero => rfl
  | succ remaining ih =>
      have h := ih (col + 1) (ops.add acc (normalizedWeight ops (values col) maximum))
        (expCycle ops t col (values col) maximum acc s) (by intro c hc hb; exact hl c (by omega) (by omega))
      rw [exp_cycle_memory, if_neg (hl col (by omega) (by omega))] at h
      exact h

theorem exp_columns_value (ops : Ops α) (t : Nat) (values : Nat → α)
    (col remaining c : Nat) (maximum acc : α) (s : State α) (hc : col ≤ c) (hb : c < col + remaining) :
    (expColumns ops t values maximum col remaining acc s).memory (sharedCell t 3 (scoreAddress t c)) =
      some (normalizedWeight ops (values c) maximum) := by
  induction remaining generalizing col acc s with
  | zero => omega
  | succ remaining ih =>
      by_cases he : c = col
      · subst c
        have hf := exp_columns_memory_other ops t values (col + 1) remaining maximum
          (ops.add acc (normalizedWeight ops (values col) maximum))
          (expCycle ops t col (values col) maximum acc s) (sharedCell t 3 (scoreAddress t col))
          (by intro c hc hb; exact score_cell_ne t col c (by omega))
        exact hf.trans (by rw [exp_cycle_memory, if_pos rfl])
      · exact ih (col + 1) (ops.add acc (normalizedWeight ops (values col) maximum))
          (expCycle ops t col (values col) maximum acc s) (by omega) (by omega)

theorem exp_columns_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (values : Nat → α)
    (col remaining : Nat) (maximum acc : α) (s : State α) (hr : Reads p input s) :
    Reads p input (expColumns ops t values maximum col remaining acc s) := by
  intro b hb i hi
  exact (exp_columns_memory_other ops t values col remaining maximum acc s (globalCell b i)
    (by intro c hc hb; simp [globalCell, sharedCell])).trans (hr b hb i hi)

theorem exp_columns_good (ops : Ops α) (t : Nat) (values : Nat → α)
    (col remaining : Nat) (maximum acc : α) (s : State α) (stop : col + remaining = 32) (hg : TraceGood s) :
    TraceGood (expColumns ops t values maximum col remaining acc s) := by
  induction remaining generalizing col acc s with
  | zero => exact hg
  | succ remaining ih =>
      exact ih (col + 1) (ops.add acc (normalizedWeight ops (values col) maximum)) _ (by omega)
        (exp_cycle_good ops t col (values col) maximum acc s (by omega) hg)

#print axioms exp_columns_eq
#print axioms exp_columns_sum
#print axioms exp_columns_value
#print axioms exp_columns_good
end LarkNativeAttention
