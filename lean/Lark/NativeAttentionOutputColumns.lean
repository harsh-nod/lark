import Lark.NativeAttentionOutputColumn

/-! Complete 256-column source output loops, preserving unread old outputs. -/
namespace LarkNativeAttention
open LarkNonlinear
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem output_column_scales (ops : Ops α) (input : Nat → Nat → α) (t qi key col : Nat) (weights : Nat → α)
    (scales : ScaleValues α) (oldMass oldStored : α) (s : State α) (hr : ScaleReady t scales oldMass s) :
    ScaleReady t scales oldMass (outputColumn ops input t qi key col weights scales oldMass oldStored s) := by
  have h := fun r h13 h14 h15 h16 h17 h18 h19 h20 =>
    output_column_reg ops input t qi key col r weights scales oldMass oldStored s h13 h14 h15 h16 h17 h18 h19 h20
  exact ⟨(h 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hr.previousMass,
    (h 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hr.maximum,
    (h 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hr.oldScale,
    (h 11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hr.tileScale,
    (h 12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hr.mass⟩

def outputValues (ops : Ops α) (input : Nat → Nat → α) (t key : Nat) (weights : Nat → α)
    (scales : ScaleValues α) (oldMass : α) (oldValues : Nat → α) : Nat → α :=
  fun col => storedOutput ops scales oldMass (oldValues col) (pvValue ops input t key col weights)
def outputColumns (ops : Ops α) (input : Nat → Nat → α) (t qi key : Nat) (weights : Nat → α)
    (scales : ScaleValues α) (oldMass : α) (oldValues : Nat → α) : Nat → Nat → State α → State α
  | _, 0, s => advance s t 83
  | col, remaining + 1, s => outputColumns ops input t qi key weights scales oldMass oldValues (col + 1) remaining
      (outputColumn ops input t qi key col weights scales oldMass (oldValues col) s)

theorem output_columns_exit (p : Shape) (ops : Ops α) (t extra : Nat) (s : State α)
    (hi : s.indices t 12 = some 256) (hp : s.pc t = 66) :
    runLane ops (layout p) (geometry p) program t (extra + 1) s =
      runLane ops (layout p) (geometry p) program t extra (advance s t 83) := by
  have hg := LarkReduction.predicate_nlt_of (geometry p) t s (.ivar 12) (.const 256) 256 256 hi (by rfl) (by omega)
  have he := execute_branch_of ops (layout p) (geometry p) t 67 83 _ s false hg (by omega)
  exact source_step p ops t 66 extra _ s _ (by rfl) hp he

theorem output_columns_eq (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (t qi key : Nat)
    (weights : Nat → α) (scales : ScaleValues α) (oldMass : α) (oldValues : Nat → α) (col remaining extra : Nat)
    (s : State α) (ht : t < p.groups * 32) (hi : qi < 4) (stop : col + remaining = 256)
    (hw : ScoreRange t weights 0 32 s) (hk : Tiles ops input t key s) (hn : NativeIndices t s)
    (hq : s.indices t 7 = some (qi : Int)) (hcol : s.indices t 12 = some (col : Int))
    (hr : ScaleReady t scales oldMass s) (ho : OutputRange t qi oldValues col 256 s) (hp : s.pc t = 66) :
    runLane ops (layout p) (geometry p) program t (extra + 235 * remaining + 1) s =
      runLane ops (layout p) (geometry p) program t extra
        (outputColumns ops input t qi key weights scales oldMass oldValues col remaining s) := by
  induction remaining generalizing col s with
  | zero =>
      have he : col = 256 := by omega
      subst col
      exact output_columns_exit p ops t extra s hcol hp
  | succ remaining ih =>
      have hc : col < 256 := by omega
      let next := outputColumn ops input t qi key col weights scales oldMass (oldValues col) s
      have hf := output_column_fields ops input t qi key col weights scales oldMass (oldValues col) s
      have hw' : ScoreRange t weights 0 32 next := by
        intro row hr hb
        rw [output_column_memory, if_neg (by simp [sharedCell, globalCell])]
        exact hw row hr hb
      have hk' : Tiles ops input t key next := by
        intro buffer hb row hr c hc
        rw [output_column_memory, if_neg (by simp [sharedCell, globalCell])]
        exact hk buffer hb row hr c hc
      rw [show extra + 235 * (remaining + 1) + 1 = (extra + 235 * remaining + 1) + 235 by omega,
        output_column_eq p ops input t qi key col (extra + 235 * remaining + 1) weights scales oldMass (oldValues col) s
          ht hi hc hw hk hn hq hcol hr (ho col (by omega) hc) hp]
      exact ih (col + 1) next (by omega) hw' hk'
        (output_column_native ops input t qi key col weights scales oldMass (oldValues col) s hn)
        ((output_column_index ops input t qi key col 7 weights scales oldMass (oldValues col) s (by decide) (by decide)).trans hq)
        hf.2.1 (output_column_scales ops input t qi key col weights scales oldMass (oldValues col) s hr)
        (output_column_range ops input t qi key col weights oldValues scales oldMass s ho) hf.1

theorem output_columns_fields (ops : Ops α) (input : Nat → Nat → α) (t qi key : Nat)
    (weights : Nat → α) (scales : ScaleValues α) (oldMass : α) (oldValues : Nat → α)
    (col remaining : Nat) (s : State α) :
    (outputColumns ops input t qi key weights scales oldMass oldValues col remaining s).pc t = 83 ∧
    (outputColumns ops input t qi key weights scales oldMass oldValues col remaining s).epochs = s.epochs := by
  induction remaining generalizing col s with
  | zero => exact ⟨by simp [outputColumns, advance], rfl⟩
  | succ remaining ih =>
      have h := ih (col + 1) (outputColumn ops input t qi key col weights scales oldMass (oldValues col) s)
      exact ⟨h.1, h.2.trans (output_column_fields ops input t qi key col weights scales oldMass (oldValues col) s).2.2⟩

theorem output_columns_index (ops : Ops α) (input : Nat → Nat → α) (t qi key : Nat)
    (weights : Nat → α) (scales : ScaleValues α) (oldMass : α) (oldValues : Nat → α)
    (col remaining r : Nat) (s : State α) (h12 : r ≠ 12) (h13 : r ≠ 13) :
    (outputColumns ops input t qi key weights scales oldMass oldValues col remaining s).indices t r = s.indices t r := by
  induction remaining generalizing col s with
  | zero => rfl
  | succ remaining ih =>
      exact (ih (col + 1) (outputColumn ops input t qi key col weights scales oldMass (oldValues col) s)).trans
        (output_column_index ops input t qi key col r weights scales oldMass (oldValues col) s h12 h13)

theorem output_columns_scales (ops : Ops α) (input : Nat → Nat → α) (t qi key : Nat)
    (weights : Nat → α) (scales : ScaleValues α) (oldMass : α) (oldValues : Nat → α)
    (col remaining : Nat) (s : State α) (hr : ScaleReady t scales oldMass s) :
    ScaleReady t scales oldMass (outputColumns ops input t qi key weights scales oldMass oldValues col remaining s) := by
  induction remaining generalizing col s with
  | zero => exact scales_of_regs t scales oldMass s _ hr rfl
  | succ remaining ih =>
      exact ih (col + 1) _ (output_column_scales ops input t qi key col weights scales oldMass (oldValues col) s hr)

theorem output_columns_memory_other (ops : Ops α) (input : Nat → Nat → α) (t qi key : Nat)
    (weights : Nat → α) (scales : ScaleValues α) (oldMass : α) (oldValues : Nat → α)
    (col remaining : Nat) (s : State α) (l : Location)
    (hl : ∀ c, col ≤ c → c < col + remaining → l ≠ globalCell 0 (globalAddress t qi c)) :
    (outputColumns ops input t qi key weights scales oldMass oldValues col remaining s).memory l = s.memory l := by
  induction remaining generalizing col s with
  | zero => rfl
  | succ remaining ih =>
      have h := ih (col + 1) (outputColumn ops input t qi key col weights scales oldMass (oldValues col) s)
        (by intro c hc hb; exact hl c (by omega) (by omega))
      rw [output_column_memory, if_neg (hl col (by omega) (by omega))] at h
      exact h

theorem output_columns_value (ops : Ops α) (input : Nat → Nat → α) (t qi key : Nat)
    (weights : Nat → α) (scales : ScaleValues α) (oldMass : α) (oldValues : Nat → α)
    (col remaining c : Nat) (s : State α) (hc : col ≤ c) (hb : c < col + remaining) :
    (outputColumns ops input t qi key weights scales oldMass oldValues col remaining s).memory (globalCell 0 (globalAddress t qi c)) =
      some (outputValues ops input t key weights scales oldMass oldValues c) := by
  induction remaining generalizing col s with
  | zero => omega
  | succ remaining ih =>
      by_cases he : c = col
      · subst c
        have hf := output_columns_memory_other ops input t qi key weights scales oldMass oldValues (col + 1) remaining
          (outputColumn ops input t qi key col weights scales oldMass (oldValues col) s) (globalCell 0 (globalAddress t qi col))
          (by intro c hc hb; exact global_column_ne t qi col c (by omega))
        exact hf.trans (by rw [output_column_memory, if_pos rfl]; rfl)
      · exact ih (col + 1) (outputColumn ops input t qi key col weights scales oldMass (oldValues col) s) (by omega) (by omega)

theorem output_columns_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (t qi key : Nat)
    (weights : Nat → α) (scales : ScaleValues α) (oldMass : α) (oldValues : Nat → α)
    (col remaining : Nat) (s : State α) (hr : Reads p input s) :
    Reads p input (outputColumns ops input t qi key weights scales oldMass oldValues col remaining s) := by
  intro b hb i hi
  have hb0 : b ≠ 0 := by omega
  exact (output_columns_memory_other ops input t qi key weights scales oldMass oldValues col remaining s (globalCell b i)
    (by intro c hc hb; simp [globalCell, hb0])).trans (hr b hb i hi)

theorem output_columns_good (ops : Ops α) (input : Nat → Nat → α) (t qi key : Nat)
    (weights : Nat → α) (scales : ScaleValues α) (oldMass : α) (oldValues : Nat → α)
    (col remaining : Nat) (s : State α) (hi : qi < 4) (stop : col + remaining = 256)
    (he : (s.epochs t).block % 2 = 1) (hg : TraceGood s) :
    TraceGood (outputColumns ops input t qi key weights scales oldMass oldValues col remaining s) := by
  induction remaining generalizing col s with
  | zero => exact hg
  | succ remaining ih =>
      have hf := output_column_fields ops input t qi key col weights scales oldMass (oldValues col) s
      exact ih (col + 1) _ (by omega) (by simpa only [hf.2.2] using he)
        (output_column_good ops input t qi key col weights scales oldMass (oldValues col) s hi (by omega) he hg)

#print axioms output_columns_eq
#print axioms output_columns_value
#print axioms output_columns_reads
#print axioms output_columns_good
end LarkNativeAttention
