import Lark.NativeAttentionDotCycle

/-! The complete 256-component source dot loop, including its false guard. -/
namespace LarkNativeAttention
open LarkNonlinear
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def dotFold (ops : Ops α) (input : Nat → Nat → α) (t qi kj row : Nat) : Nat → Nat → α → α
  | _, 0, acc => acc
  | col, remaining + 1, acc => dotFold ops input t qi kj row (col + 1) remaining
      (dotNext ops input t qi kj row col acc)

def dotColumns (ops : Ops α) (input : Nat → Nat → α) (t qi kj row : Nat) :
    Nat → Nat → α → State α → State α
  | _, 0, _, s => advance s t 40
  | col, remaining + 1, acc, s => dotColumns ops input t qi kj row (col + 1) remaining
      (dotNext ops input t qi kj row col acc) (dotCycle ops input t qi kj row col acc s)

theorem dot_columns_exit (p : Shape) (ops : Ops α) (t extra : Nat) (s : State α)
    (hi : s.indices t 10 = some 256) (hp : s.pc t = 33) :
    runLane ops (layout p) (geometry p) program t (extra + 1) s =
      runLane ops (layout p) (geometry p) program t extra (advance s t 40) := by
  have hg := LarkReduction.predicate_nlt_of (geometry p) t s (.ivar 10) (.const 256)
    256 256 hi (by rfl) (by omega)
  have he := execute_branch_of ops (layout p) (geometry p) t 34 40 _ s false hg (by omega)
  exact source_step p ops t 33 extra _ s _ (by rfl) hp he

theorem dot_columns_eq (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t qi kj row col remaining extra : Nat) (acc : α) (s : State α) (hr : row < 32)
    (stop : col + remaining = 256) (hq : QiReady ops input t qi s) (hk : Tiles ops input t kj s)
    (hn : NativeIndices t s) (hrow : s.indices t 9 = some (row : Int))
    (hcol : s.indices t 10 = some (col : Int)) (hacc : s.regs t 1 = some acc) (hp : s.pc t = 33) :
    runLane ops (layout p) (geometry p) program t (extra + 7 * remaining + 1) s =
      runLane ops (layout p) (geometry p) program t extra
        (dotColumns ops input t qi kj row col remaining acc s) := by
  induction remaining generalizing col acc s with
  | zero =>
      have he : col = 256 := by omega
      subst col
      exact dot_columns_exit p ops t extra s hcol hp
  | succ remaining ih =>
      have hf := dot_cycle_fields ops input t qi kj row col acc s
      have hm := hf.2.2.2.2
      rw [show extra + 7 * (remaining + 1) + 1 = (extra + 7 * remaining + 1) + 7 by omega,
        dot_cycle_eq p ops input t qi kj row col (extra + 7 * remaining + 1) acc s hr (by omega)
          hq hk hn hrow hcol hacc hp]
      exact ih (col + 1) (dotNext ops input t qi kj row col acc) (dotCycle ops input t qi kj row col acc s)
        (by omega) (qi_of_memory ops input t qi s _ hq hm) (tiles_of_memory ops input t kj s _ hk hm)
        (dot_cycle_native ops input t qi kj row col acc s hn)
        ((dot_cycle_index ops input t qi kj row col 9 acc s (by decide)).trans hrow)
        hf.2.1 hf.2.2.1 hf.1

theorem dot_columns_fields (ops : Ops α) (input : Nat → Nat → α)
    (t qi kj row col remaining : Nat) (acc : α) (s : State α) :
    (dotColumns ops input t qi kj row col remaining acc s).pc t = 40 ∧
    (dotColumns ops input t qi kj row col remaining acc s).epochs = s.epochs ∧
    (dotColumns ops input t qi kj row col remaining acc s).memory = s.memory := by
  induction remaining generalizing col acc s with
  | zero => exact ⟨by simp [dotColumns, advance], rfl, rfl⟩
  | succ remaining ih =>
      have h := ih (col + 1) (dotNext ops input t qi kj row col acc) (dotCycle ops input t qi kj row col acc s)
      have hf := dot_cycle_fields ops input t qi kj row col acc s
      exact ⟨h.1, h.2.1.trans hf.2.2.2.1, h.2.2.trans hf.2.2.2.2⟩

theorem dot_columns_value (ops : Ops α) (input : Nat → Nat → α)
    (t qi kj row col remaining : Nat) (acc : α) (s : State α) (hacc : s.regs t 1 = some acc) :
    (dotColumns ops input t qi kj row col remaining acc s).regs t 1 =
      some (dotFold ops input t qi kj row col remaining acc) := by
  induction remaining generalizing col acc s with
  | zero => exact hacc
  | succ remaining ih =>
      exact ih (col + 1) (dotNext ops input t qi kj row col acc) (dotCycle ops input t qi kj row col acc s)
        (dot_cycle_fields ops input t qi kj row col acc s).2.2.1

theorem dot_columns_index (ops : Ops α) (input : Nat → Nat → α)
    (t qi kj row col remaining r : Nat) (acc : α) (s : State α) (hr : r ≠ 10) :
    (dotColumns ops input t qi kj row col remaining acc s).indices t r = s.indices t r := by
  induction remaining generalizing col acc s with
  | zero => rfl
  | succ remaining ih =>
      exact (ih (col + 1) (dotNext ops input t qi kj row col acc) (dotCycle ops input t qi kj row col acc s)).trans
        (dot_cycle_index ops input t qi kj row col r acc s hr)

theorem dot_columns_reg (ops : Ops α) (input : Nat → Nat → α)
    (t qi kj row col remaining r : Nat) (acc : α) (s : State α)
    (h1 : r ≠ 1) (h2 : r ≠ 2) (h3 : r ≠ 3) (h4 : r ≠ 4) :
    (dotColumns ops input t qi kj row col remaining acc s).regs t r = s.regs t r := by
  induction remaining generalizing col acc s with
  | zero => rfl
  | succ remaining ih =>
      exact (ih (col + 1) (dotNext ops input t qi kj row col acc) (dotCycle ops input t qi kj row col acc s)).trans
        (dot_cycle_reg ops input t qi kj row col r acc s h1 h2 h3 h4)

theorem dot_columns_native (ops : Ops α) (input : Nat → Nat → α)
    (t qi kj row col remaining : Nat) (acc : α) (s : State α) (hn : NativeIndices t s) :
    NativeIndices t (dotColumns ops input t qi kj row col remaining acc s) := by
  induction remaining generalizing col acc s with
  | zero => exact hn
  | succ remaining ih =>
      exact ih (col + 1) (dotNext ops input t qi kj row col acc) _
        (dot_cycle_native ops input t qi kj row col acc s hn)

theorem dot_columns_good (ops : Ops α) (input : Nat → Nat → α)
    (t qi kj row col remaining : Nat) (acc : α) (s : State α) (stop : col + remaining = 256)
    (he : (s.epochs t).block % 2 = 1) (hg : TraceGood s) :
    TraceGood (dotColumns ops input t qi kj row col remaining acc s) := by
  induction remaining generalizing col acc s with
  | zero => exact hg
  | succ remaining ih =>
      have hf := dot_cycle_fields ops input t qi kj row col acc s
      exact ih (col + 1) (dotNext ops input t qi kj row col acc) _ (by omega)
        (by simpa only [hf.2.2.2.1] using he)
        (dot_cycle_good ops input t qi kj row col acc s (by omega) he hg)

theorem dot_columns_other (ops : Ops α) (input : Nat → Nat → α)
    (t u qi kj row col remaining : Nat) (acc : α) (s : State α) (hne : u ≠ t) :
    (dotColumns ops input t qi kj row col remaining acc s).pc u = s.pc u ∧
    (dotColumns ops input t qi kj row col remaining acc s).indices u = s.indices u ∧
    (dotColumns ops input t qi kj row col remaining acc s).regs u = s.regs u := by
  induction remaining generalizing col acc s with
  | zero => exact ⟨by simp [dotColumns, advance, hne], rfl, rfl⟩
  | succ remaining ih =>
      have h := ih (col + 1) (dotNext ops input t qi kj row col acc) (dotCycle ops input t qi kj row col acc s)
      have hf := dot_cycle_other ops input t u qi kj row col acc s hne
      exact ⟨h.1.trans hf.1, h.2.1.trans hf.2.1, h.2.2.trans hf.2.2⟩

#print axioms dot_columns_eq
#print axioms dot_columns_value
#print axioms dot_columns_good
end LarkNativeAttention
