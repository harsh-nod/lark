import Lark.NativeAttentionScoreRow

/-! All 32 actual score rows and their running maximum, with the final guard. -/
namespace LarkNativeAttention
open LarkNonlinear
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def scoreRowsFuel : Nat → Nat → Nat
  | _, 0 => 1
  | row, remaining + 1 => scoreRowFuel row + scoreRowsFuel (row + 1) remaining
def maximumFold (ops : Ops α) (input : Nat → Nat → α) (t qi kj : Nat) : Nat → Nat → α → α
  | _, 0, maximum => maximum
  | row, remaining + 1, maximum => maximumFold ops input t qi kj (row + 1) remaining
      (nextMaximum ops row (scoreValue ops input t qi kj row) maximum)
def scoreRows (ops : Ops α) (input : Nat → Nat → α) (t qi kj : Nat) :
    Nat → Nat → α → State α → State α
  | _, 0, _, s => advance s t 48
  | row, remaining + 1, maximum, s => scoreRows ops input t qi kj (row + 1) remaining
      (nextMaximum ops row (scoreValue ops input t qi kj row) maximum)
      (scoreRow ops input t qi kj row maximum s)

theorem score_full_fuel : scoreRowsFuel 0 32 = 57666 := by decide

theorem score_rows_exit (p : Shape) (ops : Ops α) (t extra : Nat) (s : State α)
    (hi : s.indices t 9 = some 32) (hp : s.pc t = 30) :
    runLane ops (layout p) (geometry p) program t (extra + 1) s =
      runLane ops (layout p) (geometry p) program t extra (advance s t 48) := by
  have hg := LarkReduction.predicate_nlt_of (geometry p) t s (.ivar 9) (.const 32) 32 32 hi (by rfl) (by omega)
  have he := execute_branch_of ops (layout p) (geometry p) t 31 48 _ s false hg (by omega)
  exact source_step p ops t 30 extra _ s _ (by rfl) hp he

theorem score_rows_eq (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t qi kj row remaining extra : Nat) (maximum : α) (s : State α) (stop : row + remaining = 32)
    (hq : QiReady ops input t qi s) (hk : Tiles ops input t kj s) (hn : NativeIndices t s)
    (hi : s.indices t 9 = some (row : Int)) (hm : s.regs t 0 = some maximum) (hp : s.pc t = 30) :
    runLane ops (layout p) (geometry p) program t (extra + scoreRowsFuel row remaining) s =
      runLane ops (layout p) (geometry p) program t extra (scoreRows ops input t qi kj row remaining maximum s) := by
  induction remaining generalizing row maximum s with
  | zero =>
      have he : row = 32 := by omega
      subst row
      exact score_rows_exit p ops t extra s hi hp
  | succ remaining ih =>
      have hf := score_row_fields ops input t qi kj row maximum s
      have hsteps : extra + scoreRowsFuel row (remaining + 1) =
          (extra + scoreRowsFuel (row + 1) remaining) + scoreRowFuel row := by
        simp only [scoreRowsFuel]
        omega
      rw [hsteps, score_row_eq p ops input t qi kj row (extra + scoreRowsFuel (row + 1) remaining)
        maximum s (by omega) hq hk hn hi hm hp]
      exact ih (row + 1) (nextMaximum ops row (scoreValue ops input t qi kj row) maximum) _ (by omega)
        (score_row_qi ops input t qi kj row maximum s hq) (score_row_tiles ops input t qi kj row maximum s hk)
        (score_row_native ops input t qi kj row maximum s hn) hf.2.1 hf.2.2.1 hf.1

theorem score_rows_fields (ops : Ops α) (input : Nat → Nat → α)
    (t qi kj row remaining : Nat) (maximum : α) (s : State α) :
    (scoreRows ops input t qi kj row remaining maximum s).pc t = 48 ∧
    (scoreRows ops input t qi kj row remaining maximum s).epochs = s.epochs := by
  induction remaining generalizing row maximum s with
  | zero => exact ⟨by simp [scoreRows, advance], rfl⟩
  | succ remaining ih =>
      have h := ih (row + 1) (nextMaximum ops row (scoreValue ops input t qi kj row) maximum)
        (scoreRow ops input t qi kj row maximum s)
      exact ⟨h.1, h.2.trans (score_row_fields ops input t qi kj row maximum s).2.2.2⟩

theorem score_rows_maximum (ops : Ops α) (input : Nat → Nat → α)
    (t qi kj row remaining : Nat) (maximum : α) (s : State α) (hm : s.regs t 0 = some maximum) :
    (scoreRows ops input t qi kj row remaining maximum s).regs t 0 =
      some (maximumFold ops input t qi kj row remaining maximum) := by
  induction remaining generalizing row maximum s with
  | zero => exact hm
  | succ remaining ih =>
      exact ih (row + 1) (nextMaximum ops row (scoreValue ops input t qi kj row) maximum)
        (scoreRow ops input t qi kj row maximum s) (score_row_fields ops input t qi kj row maximum s).2.2.1

theorem score_rows_index (ops : Ops α) (input : Nat → Nat → α)
    (t qi kj row remaining r : Nat) (maximum : α) (s : State α) (h9 : r ≠ 9) (h10 : r ≠ 10) :
    (scoreRows ops input t qi kj row remaining maximum s).indices t r = s.indices t r := by
  induction remaining generalizing row maximum s with
  | zero => rfl
  | succ remaining ih =>
      exact (ih (row + 1) (nextMaximum ops row (scoreValue ops input t qi kj row) maximum)
        (scoreRow ops input t qi kj row maximum s)).trans (score_row_index ops input t qi kj row r maximum s h9 h10)

theorem score_rows_native (ops : Ops α) (input : Nat → Nat → α)
    (t qi kj row remaining : Nat) (maximum : α) (s : State α) (hn : NativeIndices t s) :
    NativeIndices t (scoreRows ops input t qi kj row remaining maximum s) := by
  induction remaining generalizing row maximum s with
  | zero => exact hn
  | succ remaining ih =>
      exact ih (row + 1) (nextMaximum ops row (scoreValue ops input t qi kj row) maximum) _
        (score_row_native ops input t qi kj row maximum s hn)

theorem score_rows_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t qi kj row remaining : Nat) (maximum : α) (s : State α) (hr : Reads p input s) :
    Reads p input (scoreRows ops input t qi kj row remaining maximum s) := by
  induction remaining generalizing row maximum s with
  | zero => exact hr
  | succ remaining ih =>
      exact ih (row + 1) (nextMaximum ops row (scoreValue ops input t qi kj row) maximum) _
        (score_row_reads p ops input t qi kj row maximum s hr)

theorem score_rows_memory_other (ops : Ops α) (input : Nat → Nat → α)
    (t qi kj row remaining : Nat) (maximum : α) (s : State α) (l : Location)
    (hl : ∀ r, row ≤ r → r < row + remaining → l ≠ sharedCell t 3 (scoreAddress t r)) :
    (scoreRows ops input t qi kj row remaining maximum s).memory l = s.memory l := by
  induction remaining generalizing row maximum s with
  | zero => rfl
  | succ remaining ih =>
      have h := ih (row + 1) (nextMaximum ops row (scoreValue ops input t qi kj row) maximum)
        (scoreRow ops input t qi kj row maximum s) (by intro r hr hb; exact hl r (by omega) (by omega))
      rw [score_row_memory, if_neg (hl row (by omega) (by omega))] at h
      exact h

theorem score_cell_ne (t a b : Nat) (hne : a ≠ b) :
    sharedCell t 3 (scoreAddress t a) ≠ sharedCell t 3 (scoreAddress t b) := by
  intro he
  have he := congrArg Location.offset he
  simp only [sharedCell, scoreAddress] at he
  omega

theorem score_rows_value (ops : Ops α) (input : Nat → Nat → α)
    (t qi kj row remaining r : Nat) (maximum : α) (s : State α) (hr : row ≤ r) (hb : r < row + remaining) :
    (scoreRows ops input t qi kj row remaining maximum s).memory (sharedCell t 3 (scoreAddress t r)) =
      some (scoreValue ops input t qi kj r) := by
  induction remaining generalizing row maximum s with
  | zero => omega
  | succ remaining ih =>
      by_cases he : r = row
      · subst r
        have hf := score_rows_memory_other ops input t qi kj (row + 1) remaining
          (nextMaximum ops row (scoreValue ops input t qi kj row) maximum)
          (scoreRow ops input t qi kj row maximum s) (sharedCell t 3 (scoreAddress t row))
          (by intro r hr hb; exact score_cell_ne t row r (by omega))
        exact hf.trans (by rw [score_row_memory, if_pos rfl])
      · exact ih (row + 1) (nextMaximum ops row (scoreValue ops input t qi kj row) maximum)
          (scoreRow ops input t qi kj row maximum s) (by omega) (by omega)

theorem score_rows_qi (ops : Ops α) (input : Nat → Nat → α)
    (t qi kj row remaining : Nat) (maximum : α) (s : State α) (hq : QiReady ops input t qi s) :
    QiReady ops input t qi (scoreRows ops input t qi kj row remaining maximum s) := by
  induction remaining generalizing row maximum s with
  | zero => exact hq
  | succ remaining ih =>
      exact ih (row + 1) (nextMaximum ops row (scoreValue ops input t qi kj row) maximum) _
        (score_row_qi ops input t qi kj row maximum s hq)

theorem score_rows_tiles (ops : Ops α) (input : Nat → Nat → α)
    (t qi kj row remaining : Nat) (maximum : α) (s : State α) (hk : Tiles ops input t kj s) :
    Tiles ops input t kj (scoreRows ops input t qi kj row remaining maximum s) := by
  induction remaining generalizing row maximum s with
  | zero => exact hk
  | succ remaining ih =>
      exact ih (row + 1) (nextMaximum ops row (scoreValue ops input t qi kj row) maximum) _
        (score_row_tiles ops input t qi kj row maximum s hk)

theorem score_rows_good (ops : Ops α) (input : Nat → Nat → α)
    (t qi kj row remaining : Nat) (maximum : α) (s : State α) (stop : row + remaining = 32)
    (he : (s.epochs t).block % 2 = 1) (hg : TraceGood s) :
    TraceGood (scoreRows ops input t qi kj row remaining maximum s) := by
  induction remaining generalizing row maximum s with
  | zero => exact hg
  | succ remaining ih =>
      have hf := score_row_fields ops input t qi kj row maximum s
      exact ih (row + 1) (nextMaximum ops row (scoreValue ops input t qi kj row) maximum) _ (by omega)
        (by simpa only [hf.2.2.2] using he) (score_row_good ops input t qi kj row maximum s (by omega) he hg)

#print axioms score_rows_eq
#print axioms score_rows_maximum
#print axioms score_rows_value
#print axioms score_rows_good
end LarkNativeAttention
