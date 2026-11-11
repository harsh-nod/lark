import Lark.NativeAttentionPVCycle

/-! The full 32-row weighted-V dot loop, including its false guard. -/
namespace LarkNativeAttention
open LarkNonlinear
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem score_range_of_memory (t : Nat) (weights : Nat → α) (start stop : Nat) (s next : State α)
    (hw : ScoreRange t weights start stop s) (hm : next.memory = s.memory) : ScoreRange t weights start stop next := by
  intro row hr hb
  rw [hm]
  exact hw row hr hb

def pvFold (ops : Ops α) (input : Nat → Nat → α) (t key col : Nat) (weights : Nat → α) : Nat → Nat → α → α
  | _, 0, acc => acc
  | row, remaining + 1, acc => pvFold ops input t key col weights (row + 1) remaining
      (pvNext ops input t key col row weights acc)
def pvRows (ops : Ops α) (input : Nat → Nat → α) (t key col : Nat) (weights : Nat → α) :
    Nat → Nat → α → State α → State α
  | _, 0, _, s => advance s t 76
  | row, remaining + 1, acc, s => pvRows ops input t key col weights (row + 1) remaining
      (pvNext ops input t key col row weights acc) (pvCycle ops input t key col row weights acc s)

theorem pv_rows_exit (p : Shape) (ops : Ops α) (t extra : Nat) (s : State α)
    (hi : s.indices t 13 = some 32) (hp : s.pc t = 69) :
    runLane ops (layout p) (geometry p) program t (extra + 1) s =
      runLane ops (layout p) (geometry p) program t extra (advance s t 76) := by
  have hg := LarkReduction.predicate_nlt_of (geometry p) t s (.ivar 13) (.const 32) 32 32 hi (by rfl) (by omega)
  have he := execute_branch_of ops (layout p) (geometry p) t 70 76 _ s false hg (by omega)
  exact source_step p ops t 69 extra _ s _ (by rfl) hp he

theorem pv_rows_eq (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (t key col : Nat) (weights : Nat → α)
    (row remaining extra : Nat) (acc : α) (s : State α) (stop : row + remaining = 32) (hc : col < 256)
    (hw : ScoreRange t weights 0 32 s) (hk : Tiles ops input t key s) (hn : NativeIndices t s)
    (hrow : s.indices t 13 = some (row : Int)) (hcol : s.indices t 12 = some (col : Int))
    (ha : s.regs t 13 = some acc) (hp : s.pc t = 69) :
    runLane ops (layout p) (geometry p) program t (extra + 7 * remaining + 1) s =
      runLane ops (layout p) (geometry p) program t extra (pvRows ops input t key col weights row remaining acc s) := by
  induction remaining generalizing row acc s with
  | zero =>
      have he : row = 32 := by omega
      subst row
      exact pv_rows_exit p ops t extra s hrow hp
  | succ remaining ih =>
      have hf := pv_cycle_fields ops input t key col row weights acc s
      have hm := hf.2.2.2.2
      rw [show extra + 7 * (remaining + 1) + 1 = (extra + 7 * remaining + 1) + 7 by omega,
        pv_cycle_eq p ops input t key col row (extra + 7 * remaining + 1) weights acc s (by omega) hc
          hw hk hn hrow hcol ha hp]
      exact ih (row + 1) (pvNext ops input t key col row weights acc) _ (by omega)
        (score_range_of_memory t weights 0 32 s _ hw hm) (tiles_of_memory ops input t key s _ hk hm)
        (pv_cycle_native ops input t key col row weights acc s hn) hf.2.1
        ((pv_cycle_index ops input t key col row 12 weights acc s (by decide)).trans hcol) hf.2.2.1 hf.1

theorem pv_rows_fields (ops : Ops α) (input : Nat → Nat → α) (t key col : Nat) (weights : Nat → α)
    (row remaining : Nat) (acc : α) (s : State α) :
    (pvRows ops input t key col weights row remaining acc s).pc t = 76 ∧
    (pvRows ops input t key col weights row remaining acc s).epochs = s.epochs ∧
    (pvRows ops input t key col weights row remaining acc s).memory = s.memory := by
  induction remaining generalizing row acc s with
  | zero => exact ⟨by simp [pvRows, advance], rfl, rfl⟩
  | succ remaining ih =>
      have h := ih (row + 1) (pvNext ops input t key col row weights acc) (pvCycle ops input t key col row weights acc s)
      have hf := pv_cycle_fields ops input t key col row weights acc s
      exact ⟨h.1, h.2.1.trans hf.2.2.2.1, h.2.2.trans hf.2.2.2.2⟩

theorem pv_rows_value (ops : Ops α) (input : Nat → Nat → α) (t key col : Nat) (weights : Nat → α)
    (row remaining : Nat) (acc : α) (s : State α) (ha : s.regs t 13 = some acc) :
    (pvRows ops input t key col weights row remaining acc s).regs t 13 = some (pvFold ops input t key col weights row remaining acc) := by
  induction remaining generalizing row acc s with
  | zero => exact ha
  | succ remaining ih =>
      exact ih (row + 1) (pvNext ops input t key col row weights acc) _ (pv_cycle_fields ops input t key col row weights acc s).2.2.1

theorem pv_rows_index (ops : Ops α) (input : Nat → Nat → α) (t key col : Nat) (weights : Nat → α)
    (row remaining r : Nat) (acc : α) (s : State α) (hr : r ≠ 13) :
    (pvRows ops input t key col weights row remaining acc s).indices t r = s.indices t r := by
  induction remaining generalizing row acc s with
  | zero => rfl
  | succ remaining ih =>
      exact (ih (row + 1) (pvNext ops input t key col row weights acc) (pvCycle ops input t key col row weights acc s)).trans
        (pv_cycle_index ops input t key col row r weights acc s hr)

theorem pv_rows_reg (ops : Ops α) (input : Nat → Nat → α) (t key col : Nat) (weights : Nat → α)
    (row remaining r : Nat) (acc : α) (s : State α) (h13 : r ≠ 13) (h14 : r ≠ 14) (h15 : r ≠ 15) (h16 : r ≠ 16) :
    (pvRows ops input t key col weights row remaining acc s).regs t r = s.regs t r := by
  induction remaining generalizing row acc s with
  | zero => rfl
  | succ remaining ih =>
      exact (ih (row + 1) (pvNext ops input t key col row weights acc) (pvCycle ops input t key col row weights acc s)).trans
        (pv_cycle_reg ops input t key col row r weights acc s h13 h14 h15 h16)

theorem pv_rows_native (ops : Ops α) (input : Nat → Nat → α) (t key col : Nat) (weights : Nat → α)
    (row remaining : Nat) (acc : α) (s : State α) (hn : NativeIndices t s) :
    NativeIndices t (pvRows ops input t key col weights row remaining acc s) := by
  induction remaining generalizing row acc s with
  | zero => exact hn
  | succ remaining ih =>
      exact ih (row + 1) (pvNext ops input t key col row weights acc) _ (pv_cycle_native ops input t key col row weights acc s hn)

theorem pv_rows_scales (ops : Ops α) (input : Nat → Nat → α) (t key col : Nat) (weights : Nat → α)
    (row remaining : Nat) (acc oldMass : α) (scales : ScaleValues α) (s : State α) (hr : ScaleReady t scales oldMass s) :
    ScaleReady t scales oldMass (pvRows ops input t key col weights row remaining acc s) := by
  have h := fun r h13 h14 h15 h16 => pv_rows_reg ops input t key col weights row remaining r acc s h13 h14 h15 h16
  exact ⟨(h 8 (by decide) (by decide) (by decide) (by decide)).trans hr.previousMass,
    (h 9 (by decide) (by decide) (by decide) (by decide)).trans hr.maximum,
    (h 10 (by decide) (by decide) (by decide) (by decide)).trans hr.oldScale,
    (h 11 (by decide) (by decide) (by decide) (by decide)).trans hr.tileScale,
    (h 12 (by decide) (by decide) (by decide) (by decide)).trans hr.mass⟩

theorem pv_rows_good (ops : Ops α) (input : Nat → Nat → α) (t key col : Nat) (weights : Nat → α)
    (row remaining : Nat) (acc : α) (s : State α) (stop : row + remaining = 32)
    (he : (s.epochs t).block % 2 = 1) (hg : TraceGood s) : TraceGood (pvRows ops input t key col weights row remaining acc s) := by
  induction remaining generalizing row acc s with
  | zero => exact hg
  | succ remaining ih =>
      have hf := pv_cycle_fields ops input t key col row weights acc s
      exact ih (row + 1) (pvNext ops input t key col row weights acc) _ (by omega)
        (by simpa only [hf.2.2.2.1] using he) (pv_cycle_good ops input t key col row weights acc s (by omega) he hg)

#print axioms pv_rows_eq
#print axioms pv_rows_value
#print axioms pv_rows_scales
#print axioms pv_rows_good
end LarkNativeAttention
