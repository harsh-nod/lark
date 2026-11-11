import Lark.NativeAttentionRescale

/-! Actual source prefix from weight completion to the output-column loop. -/
namespace LarkNativeAttention
open LarkNonlinear
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def outputScales (ops : Ops α) (key : Nat) (rowMaximum rowMass previousMaximum previousMass : α) : ScaleValues α :=
  scaleValues ops rowMaximum rowMass (selectedMaximum key rowMaximum previousMaximum) (selectedMass ops key previousMass)
def outputPrepared (ops : Ops α) (t qi key : Nat) (rowMaximum rowMass previousMaximum previousMass : α)
    (s : State α) : State α :=
  rescaled ops t rowMaximum rowMass (selectedMaximum key rowMaximum previousMaximum) (selectedMass ops key previousMass)
    (oldSelected ops t qi key rowMaximum previousMaximum previousMass s)

theorem output_prepared_state (ops : Ops α) (t qi key : Nat) (rowMaximum rowMass previousMaximum previousMass : α)
    (s : State α) : outputPrepared ops t qi key rowMaximum rowMass previousMaximum previousMass s =
    rescaled ops t rowMaximum rowMass (selectedMaximum key rowMaximum previousMaximum) (selectedMass ops key previousMass)
      (oldSelected ops t qi key rowMaximum previousMaximum previousMass s) := rfl

theorem output_prepare_eq (p : Shape) (ops : Ops α) (t qi key extra : Nat)
    (rowMaximum rowMass previousMaximum previousMass : α) (s : State α) (hi : qi < 4)
    (hq : s.indices t 7 = some (qi : Int)) (hk : s.indices t 5 = some (key : Int))
    (hm : s.regs t 0 = some rowMaximum) (hl : s.regs t 5 = some rowMass)
    (hr : key ≠ 0 → s.memory (privateCell t 0 qi) = some previousMaximum ∧
      s.memory (privateCell t 1 qi) = some previousMass) (hp : s.pc t = 56) :
    runLane ops (layout p) (geometry p) program t (extra + (7 + oldTailFuel key)) s =
      runLane ops (layout p) (geometry p) program t extra
        (outputPrepared ops t qi key rowMaximum rowMass previousMaximum previousMass s) := by
  have hf := old_selected_fields ops t qi key rowMaximum previousMaximum previousMass s
  have frames := old_selected_frames ops t qi key rowMaximum previousMaximum previousMass s
  have h1 := old_selected_eq p ops t qi key (extra + 5) rowMaximum previousMaximum previousMass s hi hq hk hm hr hp
  have h2 := rescale_eq p ops t extra rowMaximum rowMass (selectedMaximum key rowMaximum previousMaximum)
    (selectedMass ops key previousMass) _ (frames.2.2.2.1.trans hm) (frames.2.2.2.2.trans hl) hf.2.1 hf.2.2 hf.1
  have hsteps : extra + (7 + oldTailFuel key) = (extra + 5) + (2 + oldTailFuel key) := by omega
  exact (congrArg (fun n => runLane ops (layout p) (geometry p) program t n s) hsteps).trans (h1.trans h2)

theorem output_prepared_fields (ops : Ops α) (t qi key : Nat) (rowMaximum rowMass previousMaximum previousMass : α)
    (s : State α) : (outputPrepared ops t qi key rowMaximum rowMass previousMaximum previousMass s).pc t = 66 ∧
    (outputPrepared ops t qi key rowMaximum rowMass previousMaximum previousMass s).indices t 12 = some 0 := by
  have hs := output_prepared_state ops t qi key rowMaximum rowMass previousMaximum previousMass s
  have hf := rescaled_fields ops t rowMaximum rowMass (selectedMaximum key rowMaximum previousMaximum)
    (selectedMass ops key previousMass) (oldSelected ops t qi key rowMaximum previousMaximum previousMass s)
  exact ⟨(congrArg (fun state : State α => state.pc t) hs).trans hf.1,
    (congrArg (fun state : State α => state.indices t 12) hs).trans hf.2.1⟩

theorem output_prepared_ready (ops : Ops α) (t qi key : Nat) (rowMaximum rowMass previousMaximum previousMass : α)
    (s : State α) : ScaleReady t (outputScales ops key rowMaximum rowMass previousMaximum previousMass)
      (selectedMass ops key previousMass) (outputPrepared ops t qi key rowMaximum rowMass previousMaximum previousMass s) := by
  have hf := old_selected_fields ops t qi key rowMaximum previousMaximum previousMass s
  have hr := rescaled_ready ops t rowMaximum rowMass (selectedMaximum key rowMaximum previousMaximum)
    (selectedMass ops key previousMass) _ hf.2.2
  exact Eq.mpr (congrArg (ScaleReady t (outputScales ops key rowMaximum rowMass previousMaximum previousMass)
    (selectedMass ops key previousMass)) (output_prepared_state ops t qi key rowMaximum rowMass previousMaximum previousMass s)) hr

theorem output_prepared_index (ops : Ops α) (t qi key r : Nat) (rowMaximum rowMass previousMaximum previousMass : α)
    (s : State α) (hr : r ≠ 12) :
    (outputPrepared ops t qi key rowMaximum rowMass previousMaximum previousMass s).indices t r = s.indices t r := by
  have hs := output_prepared_state ops t qi key rowMaximum rowMass previousMaximum previousMass s
  have frames := old_selected_frames ops t qi key rowMaximum previousMaximum previousMass s
  exact (congrArg (fun state : State α => state.indices t r) hs).trans
    ((rescaled_index ops t r rowMaximum rowMass (selectedMaximum key rowMaximum previousMaximum)
      (selectedMass ops key previousMass) _ hr).trans (congrArg (fun indices => indices t r) frames.1))

theorem output_prepared_native (ops : Ops α) (t qi key : Nat) (rowMaximum rowMass previousMaximum previousMass : α)
    (s : State α) (hn : NativeIndices t s) :
    NativeIndices t (outputPrepared ops t qi key rowMaximum rowMass previousMaximum previousMass s) :=
  ⟨(output_prepared_index ops t qi key 0 rowMaximum rowMass previousMaximum previousMass s (by decide)).trans hn.1,
   (output_prepared_index ops t qi key 1 rowMaximum rowMass previousMaximum previousMass s (by decide)).trans hn.2.1,
   (output_prepared_index ops t qi key 2 rowMaximum rowMass previousMaximum previousMass s (by decide)).trans hn.2.2⟩

theorem output_prepared_frames (ops : Ops α) (t qi key : Nat) (rowMaximum rowMass previousMaximum previousMass : α)
    (s : State α) :
    (outputPrepared ops t qi key rowMaximum rowMass previousMaximum previousMass s).epochs = s.epochs ∧
    (outputPrepared ops t qi key rowMaximum rowMass previousMaximum previousMass s).memory = s.memory := by
  have hs := output_prepared_state ops t qi key rowMaximum rowMass previousMaximum previousMass s
  have old := old_selected_frames ops t qi key rowMaximum previousMaximum previousMass s
  have h := rescaled_frames ops t rowMaximum rowMass (selectedMaximum key rowMaximum previousMaximum)
    (selectedMass ops key previousMass) (oldSelected ops t qi key rowMaximum previousMaximum previousMass s)
  exact ⟨(congrArg (fun state : State α => state.epochs) hs).trans (h.1.trans old.2.1),
    (congrArg (fun state : State α => state.memory) hs).trans (h.2.1.trans old.2.2.1)⟩

theorem output_prepared_good (ops : Ops α) (t qi key : Nat) (rowMaximum rowMass previousMaximum previousMass : α)
    (s : State α) (hg : TraceGood s) : TraceGood (outputPrepared ops t qi key rowMaximum rowMass previousMaximum previousMass s) := by
  have hOld := old_selected_good ops t qi key rowMaximum previousMaximum previousMass s hg
  have hTrace := (rescaled_frames ops t rowMaximum rowMass (selectedMaximum key rowMaximum previousMaximum)
    (selectedMass ops key previousMass) (oldSelected ops t qi key rowMaximum previousMaximum previousMass s)).2.2
  have hRescaled : TraceGood (rescaled ops t rowMaximum rowMass (selectedMaximum key rowMaximum previousMaximum)
      (selectedMass ops key previousMass) (oldSelected ops t qi key rowMaximum previousMaximum previousMass s)) := by
    intro a ha
    exact hOld a (hTrace ▸ ha)
  exact Eq.mpr (congrArg TraceGood (output_prepared_state ops t qi key rowMaximum rowMass previousMaximum previousMass s)) hRescaled

#print axioms output_prepare_eq
#print axioms output_prepared_ready
#print axioms output_prepared_good
end LarkNativeAttention
