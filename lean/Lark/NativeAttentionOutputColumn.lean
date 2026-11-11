import Lark.NativeAttentionPVComputed

/-! Actual complete output-column cycles: guard, weighted V dot, and half store. -/
namespace LarkNativeAttention
open LarkNonlinear
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def OutputRange (t qi : Nat) (values : Nat → α) (start stop : Nat) (s : State α) : Prop :=
  ∀ col, start ≤ col → col < stop → s.memory (globalCell 0 (globalAddress t qi col)) = some (values col)
def outputColumn (ops : Ops α) (input : Nat → Nat → α) (t qi key col : Nat) (weights : Nat → α)
    (scales : ScaleValues α) (oldMass oldStored : α) (s : State α) : State α :=
  outputFinish ops t qi col scales oldMass oldStored (pvValue ops input t key col weights)
    (pvComputed ops input t key col weights (advance s t 67))

theorem output_column_state (ops : Ops α) (input : Nat → Nat → α) (t qi key col : Nat) (weights : Nat → α)
    (scales : ScaleValues α) (oldMass oldStored : α) (s : State α) :
    outputColumn ops input t qi key col weights scales oldMass oldStored s =
      outputFinish ops t qi col scales oldMass oldStored (pvValue ops input t key col weights)
        (pvComputed ops input t key col weights (advance s t 67)) := rfl

theorem output_column_eq (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (t qi key col extra : Nat)
    (weights : Nat → α) (scales : ScaleValues α) (oldMass oldStored : α) (s : State α)
    (ht : t < p.groups * 32) (hi : qi < 4) (hc : col < 256) (hw : ScoreRange t weights 0 32 s)
    (hk : Tiles ops input t key s) (hn : NativeIndices t s) (hq : s.indices t 7 = some (qi : Int))
    (hcol : s.indices t 12 = some (col : Int)) (hr : ScaleReady t scales oldMass s)
    (ho : s.memory (globalCell 0 (globalAddress t qi col)) = some oldStored) (hp : s.pc t = 66) :
    runLane ops (layout p) (geometry p) program t (extra + 235) s =
      runLane ops (layout p) (geometry p) program t extra
        (outputColumn ops input t qi key col weights scales oldMass oldStored s) := by
  let s1 := advance s t 67
  let s2 := pvComputed ops input t key col weights s1
  have hg := LarkReduction.predicate_lt_of (geometry p) t s (.ivar 12) (.const 256)
    (col : Int) 256 hcol (by rfl) (by omega)
  have h1 := execute_branch_of ops (layout p) (geometry p) t 67 83 _ s true hg (by omega)
  have hf := pv_computed_fields ops input t key col weights s1
  have hn2 := pv_computed_native ops input t key col weights s1 hn
  have hq2 := (pv_computed_index ops input t key col 7 weights s1 (by decide)).trans hq
  have hcol2 := (pv_computed_index ops input t key col 12 weights s1 (by decide)).trans hcol
  have hr2 := pv_computed_scales ops input t key col weights scales oldMass s1 (scales_of_regs t scales oldMass s s1 hr rfl)
  have ho2 : s2.memory (globalCell 0 (globalAddress t qi col)) = some oldStored := (congrFun hf.2.2.2 _).trans ho
  have e1 := source_step p ops t 66 (extra + 234) _ s s1 (by rfl) hp h1
  have e2 := pv_computation_eq p ops input t key col (extra + 7) weights s1 hc hw hk hn hcol (by simp [s1, advance])
  have e3 := output_finish_eq p ops t qi col extra scales oldMass oldStored (pvValue ops input t key col weights) s2
    ht hi hc hn2 hq2 hcol2 hr2 hf.2.1 ho2 hf.1
  exact e1.trans (e2.trans e3)

theorem output_column_fields (ops : Ops α) (input : Nat → Nat → α) (t qi key col : Nat) (weights : Nat → α)
    (scales : ScaleValues α) (oldMass oldStored : α) (s : State α) :
    (outputColumn ops input t qi key col weights scales oldMass oldStored s).pc t = 66 ∧
    (outputColumn ops input t qi key col weights scales oldMass oldStored s).indices t 12 = some ((col + 1 : Nat) : Int) ∧
    (outputColumn ops input t qi key col weights scales oldMass oldStored s).epochs = s.epochs := by
  have hs := output_column_state ops input t qi key col weights scales oldMass oldStored s
  have hpv := pv_computed_fields ops input t key col weights (advance s t 67)
  have hf := output_finish_fields ops t qi col scales oldMass oldStored (pvValue ops input t key col weights)
    (pvComputed ops input t key col weights (advance s t 67))
  exact ⟨(congrArg (fun state : State α => state.pc t) hs).trans hf.1,
    (congrArg (fun state : State α => state.indices t 12) hs).trans hf.2.1,
    (congrArg (fun state : State α => state.epochs) hs).trans (hf.2.2.trans hpv.2.2.1)⟩

theorem output_column_index (ops : Ops α) (input : Nat → Nat → α) (t qi key col r : Nat) (weights : Nat → α)
    (scales : ScaleValues α) (oldMass oldStored : α) (s : State α) (h12 : r ≠ 12) (h13 : r ≠ 13) :
    (outputColumn ops input t qi key col weights scales oldMass oldStored s).indices t r = s.indices t r := by
  have hs := output_column_state ops input t qi key col weights scales oldMass oldStored s
  have hf := output_finish_index ops t qi col r scales oldMass oldStored (pvValue ops input t key col weights)
    (pvComputed ops input t key col weights (advance s t 67)) h12
  have hpv := pv_computed_index ops input t key col r weights (advance s t 67) h13
  exact (congrArg (fun state : State α => state.indices t r) hs).trans (hf.trans hpv)

theorem output_column_native (ops : Ops α) (input : Nat → Nat → α) (t qi key col : Nat) (weights : Nat → α)
    (scales : ScaleValues α) (oldMass oldStored : α) (s : State α) (hn : NativeIndices t s) :
    NativeIndices t (outputColumn ops input t qi key col weights scales oldMass oldStored s) :=
  ⟨(output_column_index ops input t qi key col 0 weights scales oldMass oldStored s (by decide) (by decide)).trans hn.1,
   (output_column_index ops input t qi key col 1 weights scales oldMass oldStored s (by decide) (by decide)).trans hn.2.1,
   (output_column_index ops input t qi key col 2 weights scales oldMass oldStored s (by decide) (by decide)).trans hn.2.2⟩

theorem output_column_reg (ops : Ops α) (input : Nat → Nat → α) (t qi key col r : Nat) (weights : Nat → α)
    (scales : ScaleValues α) (oldMass oldStored : α) (s : State α)
    (h13 : r ≠ 13) (h14 : r ≠ 14) (h15 : r ≠ 15) (h16 : r ≠ 16)
    (h17 : r ≠ 17) (h18 : r ≠ 18) (h19 : r ≠ 19) (h20 : r ≠ 20) :
    (outputColumn ops input t qi key col weights scales oldMass oldStored s).regs t r = s.regs t r := by
  have hs := output_column_state ops input t qi key col weights scales oldMass oldStored s
  have hf := output_finish_reg ops t qi col r scales oldMass oldStored (pvValue ops input t key col weights)
    (pvComputed ops input t key col weights (advance s t 67)) h17 h18 h19 h20
  have hpv := pv_rows_reg ops input t key col weights 0 32 r (ops.literal 0 1) (pvEntry ops t (advance s t 67)) h13 h14 h15 h16
  have hpvs := pv_computed_state ops input t key col weights (advance s t 67)
  have he : (pvEntry ops t (advance s t 67)).regs t r = s.regs t r := by simp [pvEntry, LarkReduction.setReg, LarkReduction.setIndex, advance, h13]
  exact (congrArg (fun state : State α => state.regs t r) hs).trans
    (hf.trans ((congrArg (fun state : State α => state.regs t r) hpvs).trans (hpv.trans he)))

theorem output_column_memory (ops : Ops α) (input : Nat → Nat → α) (t qi key col : Nat) (weights : Nat → α)
    (scales : ScaleValues α) (oldMass oldStored : α) (s : State α) (l : Location) :
    (outputColumn ops input t qi key col weights scales oldMass oldStored s).memory l =
      if l = globalCell 0 (globalAddress t qi col) then
        some (storedOutput ops scales oldMass oldStored (pvValue ops input t key col weights)) else s.memory l := by
  have hs := output_column_state ops input t qi key col weights scales oldMass oldStored s
  have hf := output_finish_memory ops t qi col scales oldMass oldStored (pvValue ops input t key col weights)
    (pvComputed ops input t key col weights (advance s t 67)) l
  have hm : (pvComputed ops input t key col weights (advance s t 67)).memory = s.memory :=
    (pv_computed_fields ops input t key col weights (advance s t 67)).2.2.2
  exact (congrArg (fun state : State α => state.memory l) hs).trans
    (hf.trans (congrArg (fun memory : Location → Option α => if l = globalCell 0 (globalAddress t qi col) then
      some (storedOutput ops scales oldMass oldStored (pvValue ops input t key col weights)) else memory l) hm))

theorem output_column_range (ops : Ops α) (input : Nat → Nat → α) (t qi key col : Nat) (weights oldValues : Nat → α)
    (scales : ScaleValues α) (oldMass : α) (s : State α) (ho : OutputRange t qi oldValues col 256 s) :
    OutputRange t qi oldValues (col + 1) 256 (outputColumn ops input t qi key col weights scales oldMass (oldValues col) s) := by
  intro c hc hb
  rw [output_column_memory, if_neg (global_column_ne t qi c col (by omega))]
  exact ho c (by omega) hb

theorem output_column_good (ops : Ops α) (input : Nat → Nat → α) (t qi key col : Nat) (weights : Nat → α)
    (scales : ScaleValues α) (oldMass oldStored : α) (s : State α) (hi : qi < 4) (hc : col < 256)
    (he : (s.epochs t).block % 2 = 1) (hg : TraceGood s) :
    TraceGood (outputColumn ops input t qi key col weights scales oldMass oldStored s) :=
  Eq.mpr (congrArg TraceGood (output_column_state ops input t qi key col weights scales oldMass oldStored s))
    (output_finish_good ops t qi col scales oldMass oldStored (pvValue ops input t key col weights) _ hi hc
      (pv_computed_good ops input t key col weights (advance s t 67) he hg))

#print axioms output_column_eq
#print axioms output_column_memory
#print axioms output_column_good
end LarkNativeAttention
