import Lark.NativeAttentionOutputColumns
import Lark.NativeAttentionOutputPrepare

/-! Actual source execution from completed weights through all output columns.
The private-state stores at PC 83 and later query/key tiles still follow. -/
namespace LarkNativeAttention
open LarkNonlinear
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def outputUpdated (ops : Ops α) (input : Nat → Nat → α) (t qi key : Nat)
    (weights : Nat → α) (rowMaximum rowMass previousMaximum previousMass : α)
    (oldValues : Nat → α) (s : State α) : State α :=
  outputColumns ops input t qi key weights (outputScales ops key rowMaximum rowMass previousMaximum previousMass)
    (selectedMass ops key previousMass) oldValues 0 256
    (outputPrepared ops t qi key rowMaximum rowMass previousMaximum previousMass s)

theorem output_updated_state (ops : Ops α) (input : Nat → Nat → α) (t qi key : Nat)
    (weights : Nat → α) (rowMaximum rowMass previousMaximum previousMass : α)
    (oldValues : Nat → α) (s : State α) :
    outputUpdated ops input t qi key weights rowMaximum rowMass previousMaximum previousMass oldValues s =
      outputColumns ops input t qi key weights (outputScales ops key rowMaximum rowMass previousMaximum previousMass)
        (selectedMass ops key previousMass) oldValues 0 256
        (outputPrepared ops t qi key rowMaximum rowMass previousMaximum previousMass s) := rfl

theorem output_update_eq (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (t qi key extra : Nat)
    (weights : Nat → α) (rowMaximum rowMass previousMaximum previousMass : α)
    (oldValues : Nat → α) (s : State α) (ht : t < p.groups * 32) (hi : qi < 4)
    (hw : ScoreRange t weights 0 32 s) (hk : Tiles ops input t key s) (hn : NativeIndices t s)
    (hq : s.indices t 7 = some (qi : Int)) (hj : s.indices t 5 = some (key : Int))
    (hm : s.regs t 0 = some rowMaximum) (hl : s.regs t 5 = some rowMass)
    (hr : key ≠ 0 → s.memory (privateCell t 0 qi) = some previousMaximum ∧
      s.memory (privateCell t 1 qi) = some previousMass)
    (ho : OutputRange t qi oldValues 0 256 s) (hp : s.pc t = 56) :
    runLane ops (layout p) (geometry p) program t (extra + (60168 + oldTailFuel key)) s =
      runLane ops (layout p) (geometry p) program t extra
        (outputUpdated ops input t qi key weights rowMaximum rowMass previousMaximum previousMass oldValues s) := by
  let next := outputPrepared ops t qi key rowMaximum rowMass previousMaximum previousMass s
  have frames := output_prepared_frames ops t qi key rowMaximum rowMass previousMaximum previousMass s
  have fields := output_prepared_fields ops t qi key rowMaximum rowMass previousMaximum previousMass s
  have hw' := score_range_of_memory t weights 0 32 s next hw frames.2
  have hk' := tiles_of_memory ops input t key s next hk frames.2
  have ho' : OutputRange t qi oldValues 0 256 next := by
    intro c hc hb
    rw [frames.2]
    exact ho c hc hb
  have h1 := output_prepare_eq p ops t qi key (extra + 60161) rowMaximum rowMass previousMaximum previousMass s
    hi hq hj hm hl hr hp
  have h2 := output_columns_eq p ops input t qi key weights
    (outputScales ops key rowMaximum rowMass previousMaximum previousMass) (selectedMass ops key previousMass)
    oldValues 0 256 extra next ht hi (by decide) hw' hk'
    (output_prepared_native ops t qi key rowMaximum rowMass previousMaximum previousMass s hn)
    ((output_prepared_index ops t qi key 7 rowMaximum rowMass previousMaximum previousMass s (by decide)).trans hq)
    fields.2 (output_prepared_ready ops t qi key rowMaximum rowMass previousMaximum previousMass s) ho' fields.1
  have steps : extra + (60168 + oldTailFuel key) = (extra + 60161) + (7 + oldTailFuel key) := by omega
  have columnSteps : extra + 60161 = extra + 235 * 256 + 1 := by omega
  have h2' := (congrArg (fun n => runLane ops (layout p) (geometry p) program t n next) columnSteps).trans h2
  exact (congrArg (fun n => runLane ops (layout p) (geometry p) program t n s) steps).trans (h1.trans h2')

theorem output_updated_fields (ops : Ops α) (input : Nat → Nat → α) (t qi key : Nat)
    (weights : Nat → α) (rowMaximum rowMass previousMaximum previousMass : α)
    (oldValues : Nat → α) (s : State α) :
    (outputUpdated ops input t qi key weights rowMaximum rowMass previousMaximum previousMass oldValues s).pc t = 83 ∧
    (outputUpdated ops input t qi key weights rowMaximum rowMass previousMaximum previousMass oldValues s).epochs = s.epochs := by
  have hs := output_updated_state ops input t qi key weights rowMaximum rowMass previousMaximum previousMass oldValues s
  have hf := output_columns_fields ops input t qi key weights
    (outputScales ops key rowMaximum rowMass previousMaximum previousMass) (selectedMass ops key previousMass)
    oldValues 0 256 (outputPrepared ops t qi key rowMaximum rowMass previousMaximum previousMass s)
  exact ⟨(congrArg (fun state : State α => state.pc t) hs).trans hf.1,
    (congrArg (fun state : State α => state.epochs) hs).trans
      (hf.2.trans (output_prepared_frames ops t qi key rowMaximum rowMass previousMaximum previousMass s).1)⟩

theorem output_updated_value (ops : Ops α) (input : Nat → Nat → α) (t qi key col : Nat)
    (weights : Nat → α) (rowMaximum rowMass previousMaximum previousMass : α)
    (oldValues : Nat → α) (s : State α) (hc : col < 256) :
    (outputUpdated ops input t qi key weights rowMaximum rowMass previousMaximum previousMass oldValues s).memory
      (globalCell 0 (globalAddress t qi col)) =
      some (outputValues ops input t key weights (outputScales ops key rowMaximum rowMass previousMaximum previousMass)
        (selectedMass ops key previousMass) oldValues col) :=
  (congrArg (fun state : State α => state.memory (globalCell 0 (globalAddress t qi col)))
    (output_updated_state ops input t qi key weights rowMaximum rowMass previousMaximum previousMass oldValues s)).trans
      (output_columns_value ops input t qi key weights
        (outputScales ops key rowMaximum rowMass previousMaximum previousMass) (selectedMass ops key previousMass)
        oldValues 0 256 col _ (by omega) hc)

theorem output_updated_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (t qi key : Nat)
    (weights : Nat → α) (rowMaximum rowMass previousMaximum previousMass : α)
    (oldValues : Nat → α) (s : State α) (hr : Reads p input s) :
    Reads p input (outputUpdated ops input t qi key weights rowMaximum rowMass previousMaximum previousMass oldValues s) := by
  let next := outputPrepared ops t qi key rowMaximum rowMass previousMaximum previousMass s
  have hr' := reads_of_memory p input s next hr
    (output_prepared_frames ops t qi key rowMaximum rowMass previousMaximum previousMass s).2
  exact Eq.mpr (congrArg (Reads p input)
    (output_updated_state ops input t qi key weights rowMaximum rowMass previousMaximum previousMass oldValues s))
    (output_columns_reads p ops input t qi key weights
      (outputScales ops key rowMaximum rowMass previousMaximum previousMass) (selectedMass ops key previousMass) oldValues 0 256 next hr')

theorem output_updated_good (ops : Ops α) (input : Nat → Nat → α) (t qi key : Nat)
    (weights : Nat → α) (rowMaximum rowMass previousMaximum previousMass : α)
    (oldValues : Nat → α) (s : State α) (hi : qi < 4) (he : (s.epochs t).block % 2 = 1) (hg : TraceGood s) :
    TraceGood (outputUpdated ops input t qi key weights rowMaximum rowMass previousMaximum previousMass oldValues s) := by
  have frames := output_prepared_frames ops t qi key rowMaximum rowMass previousMaximum previousMass s
  have he' : ((outputPrepared ops t qi key rowMaximum rowMass previousMaximum previousMass s).epochs t).block % 2 = 1 := by
    rw [frames.1]
    exact he
  exact Eq.mpr (congrArg TraceGood
    (output_updated_state ops input t qi key weights rowMaximum rowMass previousMaximum previousMass oldValues s))
    (output_columns_good ops input t qi key weights
      (outputScales ops key rowMaximum rowMass previousMaximum previousMass) (selectedMass ops key previousMass) oldValues
      0 256 _ hi (by decide) he' (output_prepared_good ops t qi key rowMaximum rowMass previousMaximum previousMass s hg))

#print axioms output_update_eq
#print axioms output_updated_fields
#print axioms output_updated_value
#print axioms output_updated_reads
#print axioms output_updated_good
end LarkNativeAttention
