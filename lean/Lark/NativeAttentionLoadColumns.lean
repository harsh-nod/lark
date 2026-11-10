import Lark.NativeAttentionLoadCycle

/-! Complete native K/V row copies, including the false guard at the barrier. -/
namespace LarkNativeAttention
open LarkNonlinear
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def loadColumns (ops : Ops α) (input : Nat → Nat → α) (t tile : Nat) :
    Nat → Nat → State α → State α
  | _, 0, s => advance s t 20
  | col, remaining + 1, s => loadColumns ops input t tile (col + 1) remaining
      (loadCycle ops input t tile col s)

theorem load_columns_exit (p : Shape) (ops : Ops α) (t extra : Nat) (s : State α)
    (hi : s.indices t 6 = some 256) (hp : s.pc t = 15) :
    runLane ops (layout p) (geometry p) program t (extra + 1) s =
      runLane ops (layout p) (geometry p) program t extra (advance s t 20) := by
  have hg := LarkReduction.predicate_nlt_of (geometry p) t s (.ivar 6) (.const 256)
    256 256 hi (by rfl) (by omega)
  have he := execute_branch_of ops (layout p) (geometry p) t 16 20 _ s false hg (by omega)
  exact source_step p ops t 15 extra _ s _ (by rfl) hp he

theorem load_columns_eq (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t tile col remaining extra : Nat) (s : State α)
    (ht : t < p.groups * 32) (hi : tile < 4) (stop : col + remaining = 256)
    (hr : Reads p input s) (hn : NativeIndices t s)
    (hrow : s.indices t 5 = some (tile : Int)) (hcol : s.indices t 6 = some (col : Int))
    (hp : s.pc t = 15) :
    runLane ops (layout p) (geometry p) program t (extra + 5 * remaining + 1) s =
      runLane ops (layout p) (geometry p) program t extra
        (loadColumns ops input t tile col remaining s) := by
  induction remaining generalizing col s with
  | zero =>
      have he : col = 256 := by omega
      subst col
      exact load_columns_exit p ops t extra s hcol hp
  | succ remaining ih =>
      have hf := load_cycle_fields ops input t tile col s
      rw [show extra + 5 * (remaining + 1) + 1 = (extra + 5 * remaining + 1) + 5 by omega,
        load_cycle_eq p ops input t tile col (extra + 5 * remaining + 1) s ht hi (by omega) hr hn hrow hcol hp]
      exact ih (col + 1) (loadCycle ops input t tile col s) (by omega)
        (load_cycle_reads p ops input t tile col s hr)
        (load_cycle_native ops input t tile col s hn) (hf.2.1.trans hrow) hf.2.2.1 hf.1

theorem load_columns_fields (ops : Ops α) (input : Nat → Nat → α)
    (t tile col remaining : Nat) (s : State α) :
    (loadColumns ops input t tile col remaining s).pc t = 20 ∧
    (loadColumns ops input t tile col remaining s).indices t 5 = s.indices t 5 ∧
    (loadColumns ops input t tile col remaining s).epochs = s.epochs := by
  induction remaining generalizing col s with
  | zero => exact ⟨by simp [loadColumns, advance], rfl, rfl⟩
  | succ remaining ih =>
      have h := ih (col + 1) (loadCycle ops input t tile col s)
      have hf := load_cycle_fields ops input t tile col s
      exact ⟨h.1, h.2.1.trans hf.2.1, h.2.2.trans hf.2.2.2⟩

theorem load_columns_native (ops : Ops α) (input : Nat → Nat → α)
    (t tile col remaining : Nat) (s : State α) (hn : NativeIndices t s) :
    NativeIndices t (loadColumns ops input t tile col remaining s) := by
  induction remaining generalizing col s with
  | zero => exact hn
  | succ remaining ih => exact ih (col + 1) _ (load_cycle_native ops input t tile col s hn)

theorem load_columns_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t tile col remaining : Nat) (s : State α) (hr : Reads p input s) :
    Reads p input (loadColumns ops input t tile col remaining s) := by
  induction remaining generalizing col s with
  | zero => exact hr
  | succ remaining ih => exact ih (col + 1) _ (load_cycle_reads p ops input t tile col s hr)

theorem load_columns_good (ops : Ops α) (input : Nat → Nat → α)
    (t tile col remaining : Nat) (s : State α) (stop : col + remaining = 256)
    (he : (s.epochs t).block % 2 = 0) (hg : TraceGood s) :
    TraceGood (loadColumns ops input t tile col remaining s) := by
  induction remaining generalizing col s with
  | zero => exact hg
  | succ remaining ih =>
      have hf := load_cycle_fields ops input t tile col s
      exact ih (col + 1) _ (by omega) (by simpa only [hf.2.2.2] using he)
        (load_cycle_good ops input t tile col s (by omega) he hg)

theorem load_columns_global (ops : Ops α) (input : Nat → Nat → α)
    (t tile col remaining b i : Nat) (s : State α) :
    (loadColumns ops input t tile col remaining s).memory (globalCell b i) = s.memory (globalCell b i) := by
  induction remaining generalizing col s with
  | zero => rfl
  | succ remaining ih =>
      exact (ih (col + 1) (loadCycle ops input t tile col s)).trans
        (load_cycle_global ops input t tile col b i s)

theorem load_columns_memory_other (ops : Ops α) (input : Nat → Nat → α)
    (t tile col remaining : Nat) (s : State α) (l : Location)
    (hl : ∀ c, col ≤ c → c < col + remaining →
      l ≠ sharedCell t 1 (sharedAddress t c) ∧ l ≠ sharedCell t 2 (sharedAddress t c)) :
    (loadColumns ops input t tile col remaining s).memory l = s.memory l := by
  induction remaining generalizing col s with
  | zero => rfl
  | succ remaining ih =>
      have h := ih (col + 1) (loadCycle ops input t tile col s)
        (by intro c hc hb; exact hl c (by omega) (by omega))
      rw [load_cycle_memory, if_neg (hl col (by omega) (by omega)).2,
        if_neg (hl col (by omega) (by omega)).1] at h
      exact h

theorem shared_column_ne (t b d x y : Nat) (hxy : x ≠ y) :
    sharedCell t b (sharedAddress t x) ≠ sharedCell t d (sharedAddress t y) := by
  intro he
  have he := congrArg Location.offset he
  simp only [sharedCell, sharedAddress] at he
  omega

theorem load_cycle_value (ops : Ops α) (input : Nat → Nat → α)
    (t tile col b : Nat) (s : State α) (hb : b = 1 ∨ b = 2) :
    (loadCycle ops input t tile col s).memory (sharedCell t b (sharedAddress t col)) =
      some (ops.fromHalf (input (b + 1) (globalAddress t tile col))) := by
  rw [load_cycle_memory]
  rcases hb with rfl | rfl <;> simp [sharedCell]

theorem load_columns_value (ops : Ops α) (input : Nat → Nat → α)
    (t tile col remaining c b : Nat) (s : State α)
    (hc : col ≤ c) (hbound : c < col + remaining) (hb : b = 1 ∨ b = 2) :
    (loadColumns ops input t tile col remaining s).memory (sharedCell t b (sharedAddress t c)) =
      some (ops.fromHalf (input (b + 1) (globalAddress t tile c))) := by
  induction remaining generalizing col s with
  | zero => omega
  | succ remaining ih =>
      by_cases he : c = col
      · subst c
        have hf := load_columns_memory_other ops input t tile (col + 1) remaining
          (loadCycle ops input t tile col s) (sharedCell t b (sharedAddress t col))
          (by intro c hc hb; exact ⟨shared_column_ne t b 1 col c (by omega), shared_column_ne t b 2 col c (by omega)⟩)
        exact hf.trans (load_cycle_value ops input t tile col b s hb)
      · exact ih (col + 1) (loadCycle ops input t tile col s) (by omega) (by omega)

theorem load_columns_other (ops : Ops α) (input : Nat → Nat → α)
    (t u tile col remaining : Nat) (s : State α) (hne : u ≠ t) :
    (loadColumns ops input t tile col remaining s).pc u = s.pc u ∧
    (loadColumns ops input t tile col remaining s).indices u = s.indices u ∧
    (loadColumns ops input t tile col remaining s).regs u = s.regs u := by
  induction remaining generalizing col s with
  | zero => exact ⟨by simp [loadColumns, advance, hne], rfl, rfl⟩
  | succ remaining ih =>
      have h := ih (col + 1) (loadCycle ops input t tile col s)
      have hf := load_cycle_other ops input t u tile col s hne
      exact ⟨h.1.trans hf.1, h.2.1.trans hf.2.1, h.2.2.trans hf.2.2⟩

#print axioms load_columns_eq
#print axioms load_columns_value
#print axioms load_columns_good
end LarkNativeAttention
