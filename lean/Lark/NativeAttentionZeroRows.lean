import Lark.NativeAttentionZeroRow

/-! The full four-row initialization loop of the fixed native program. -/
namespace LarkNativeAttention
open LarkNonlinear
open LarkReduction (setIndex execute_index_of)
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def zeroRows (ops : Ops α) (t : Nat) : Nat → Nat → State α → State α
  | _, 0, s => advance s t 12
  | tile, remaining + 1, s => zeroRows ops t (tile + 1) remaining (zeroRow ops t tile s)

theorem zero_rows_exit (p : Shape) (ops : Ops α) (t extra : Nat) (s : State α)
    (hi : s.indices t 3 = some 4) (hp : s.pc t = 4) :
    runLane ops (layout p) (geometry p) program t (extra + 1) s =
      runLane ops (layout p) (geometry p) program t extra (advance s t 12) := by
  have hg := LarkReduction.predicate_nlt_of (geometry p) t s (.ivar 3) (.const 4)
    4 4 hi (by rfl) (by omega)
  have he := execute_branch_of ops (layout p) (geometry p) t 5 12 _ s false hg (by omega)
  exact source_step p ops t 4 extra _ s _ (by rfl) hp he

theorem zero_rows_eq (p : Shape) (ops : Ops α) (t tile remaining extra : Nat)
    (s : State α) (ht : t < p.groups * 32) (stop : tile + remaining = 4)
    (hn : NativeIndices t s) (hi : s.indices t 3 = some (tile : Int)) (hp : s.pc t = 4) :
    runLane ops (layout p) (geometry p) program t (extra + 1029 * remaining + 1) s =
      runLane ops (layout p) (geometry p) program t extra (zeroRows ops t tile remaining s) := by
  induction remaining generalizing tile s with
  | zero =>
      have he : tile = 4 := by omega
      subst tile
      exact zero_rows_exit p ops t extra s hi hp
  | succ remaining ih =>
      have hf := zero_row_fields ops t tile s
      rw [show extra + 1029 * (remaining + 1) + 1 = (extra + 1029 * remaining + 1) + 1029 by omega,
        zero_row_eq p ops t tile (extra + 1029 * remaining + 1) s ht (by omega) hn hi hp]
      exact ih (tile + 1) (zeroRow ops t tile s) (by omega)
        (zero_row_native ops t tile s hn) hf.2.1 hf.1

theorem zero_rows_fields (ops : Ops α) (t tile remaining : Nat) (s : State α) :
    (zeroRows ops t tile remaining s).pc t = 12 ∧
    (zeroRows ops t tile remaining s).epochs = s.epochs := by
  induction remaining generalizing tile s with
  | zero => exact ⟨by simp [zeroRows, advance], rfl⟩
  | succ remaining ih =>
      have h := ih (tile + 1) (zeroRow ops t tile s)
      exact ⟨h.1, h.2.trans (zero_row_fields ops t tile s).2.2⟩

theorem zero_rows_native (ops : Ops α) (t tile remaining : Nat) (s : State α)
    (hn : NativeIndices t s) : NativeIndices t (zeroRows ops t tile remaining s) := by
  induction remaining generalizing tile s with
  | zero => exact hn
  | succ remaining ih => exact ih (tile + 1) _ (zero_row_native ops t tile s hn)

theorem zero_rows_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t tile remaining : Nat) (s : State α) (hr : Reads p input s) :
    Reads p input (zeroRows ops t tile remaining s) := by
  induction remaining generalizing tile s with
  | zero => exact hr
  | succ remaining ih => exact ih (tile + 1) _ (zero_row_reads p ops input t tile s hr)

theorem zero_rows_good (ops : Ops α) (t tile remaining : Nat) (s : State α)
    (stop : tile + remaining = 4) (hg : TraceGood s) : TraceGood (zeroRows ops t tile remaining s) := by
  induction remaining generalizing tile s with
  | zero => exact hg
  | succ remaining ih =>
      exact ih (tile + 1) _ (by omega) (zero_row_good ops t tile s (by omega) hg)

theorem zero_rows_memory_other (ops : Ops α) (t tile remaining : Nat) (s : State α) (l : Location)
    (hl : ∀ r, tile ≤ r → r < tile + remaining → ∀ c, c < 256 →
      l ≠ globalCell 0 (globalAddress t r c)) :
    (zeroRows ops t tile remaining s).memory l = s.memory l := by
  induction remaining generalizing tile s with
  | zero => rfl
  | succ remaining ih =>
      have h := ih (tile + 1) (zeroRow ops t tile s)
        (by intro r hr hb c hc; exact hl r (by omega) (by omega) c hc)
      exact h.trans (zero_row_memory_other ops t tile s l (hl tile (by omega) (by omega)))

theorem global_row_ne (t a b x y : Nat) (hab : a ≠ b) (hx : x < 256) (hy : y < 256) :
    globalCell 0 (globalAddress t a x) ≠ globalCell 0 (globalAddress t b y) := by
  intro he
  have he := congrArg Location.offset he
  simp only [globalCell, globalAddress] at he
  omega

theorem zero_rows_value (ops : Ops α) (t tile remaining r c : Nat) (s : State α)
    (hr : tile ≤ r) (hb : r < tile + remaining) (hc : c < 256) :
    (zeroRows ops t tile remaining s).memory (globalCell 0 (globalAddress t r c)) = some (zeroValue ops) := by
  induction remaining generalizing tile s with
  | zero => omega
  | succ remaining ih =>
      by_cases he : r = tile
      · subst r
        have hf := zero_rows_memory_other ops t (tile + 1) remaining (zeroRow ops t tile s)
          (globalCell 0 (globalAddress t tile c))
          (by intro r hr hb x hx; exact global_row_ne t tile r c x (by omega) hc hx)
        exact hf.trans (zero_row_value ops t tile c s hc)
      · exact ih (tile + 1) (zeroRow ops t tile s) (by omega) (by omega)

theorem zero_rows_other (ops : Ops α) (t u tile remaining : Nat) (s : State α) (hne : u ≠ t) :
    (zeroRows ops t tile remaining s).pc u = s.pc u ∧
    (zeroRows ops t tile remaining s).indices u = s.indices u ∧
    (zeroRows ops t tile remaining s).regs u = s.regs u := by
  induction remaining generalizing tile s with
  | zero => exact ⟨by simp [zeroRows, advance, hne], rfl, rfl⟩
  | succ remaining ih =>
      have h := ih (tile + 1) (zeroRow ops t tile s)
      have hf := zero_row_other ops t u tile s hne
      exact ⟨h.1.trans hf.1, h.2.1.trans hf.2.1, h.2.2.trans hf.2.2⟩

#print axioms zero_rows_eq
#print axioms zero_rows_value
#print axioms zero_rows_good
end LarkNativeAttention
