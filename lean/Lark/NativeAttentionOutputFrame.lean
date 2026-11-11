import Lark.NativeAttentionFirstOutput

/-! Output-prefix frames used by the following private-state stores. -/
namespace LarkNativeAttention
open LarkNonlinear
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem output_updated_index (ops : Ops α) (input : Nat → Nat → α) (t qi key r : Nat)
    (weights : Nat → α) (rowMaximum rowMass previousMaximum previousMass : α)
    (oldValues : Nat → α) (s : State α) (h12 : r ≠ 12) (h13 : r ≠ 13) :
    (outputUpdated ops input t qi key weights rowMaximum rowMass previousMaximum previousMass oldValues s).indices t r =
      s.indices t r := by
  have hs := output_updated_state ops input t qi key weights rowMaximum rowMass previousMaximum previousMass oldValues s
  have h1 := output_columns_index ops input t qi key weights
    (outputScales ops key rowMaximum rowMass previousMaximum previousMass) (selectedMass ops key previousMass)
    oldValues 0 256 r (outputPrepared ops t qi key rowMaximum rowMass previousMaximum previousMass s) h12 h13
  exact (congrArg (fun state : State α => state.indices t r) hs).trans
    (h1.trans (output_prepared_index ops t qi key r rowMaximum rowMass previousMaximum previousMass s h12))

theorem output_updated_scales (ops : Ops α) (input : Nat → Nat → α) (t qi key : Nat)
    (weights : Nat → α) (rowMaximum rowMass previousMaximum previousMass : α)
    (oldValues : Nat → α) (s : State α) :
    ScaleReady t (outputScales ops key rowMaximum rowMass previousMaximum previousMass) (selectedMass ops key previousMass)
      (outputUpdated ops input t qi key weights rowMaximum rowMass previousMaximum previousMass oldValues s) :=
  Eq.mpr (congrArg (ScaleReady t (outputScales ops key rowMaximum rowMass previousMaximum previousMass)
    (selectedMass ops key previousMass))
    (output_updated_state ops input t qi key weights rowMaximum rowMass previousMaximum previousMass oldValues s))
    (output_columns_scales ops input t qi key weights
      (outputScales ops key rowMaximum rowMass previousMaximum previousMass) (selectedMass ops key previousMass) oldValues
      0 256 _ (output_prepared_ready ops t qi key rowMaximum rowMass previousMaximum previousMass s))

theorem output_updated_memory_other (ops : Ops α) (input : Nat → Nat → α) (t qi key : Nat)
    (weights : Nat → α) (rowMaximum rowMass previousMaximum previousMass : α)
    (oldValues : Nat → α) (s : State α) (l : Location)
    (hl : ∀ c, c < 256 → l ≠ globalCell 0 (globalAddress t qi c)) :
    (outputUpdated ops input t qi key weights rowMaximum rowMass previousMaximum previousMass oldValues s).memory l =
      s.memory l := by
  have hs := output_updated_state ops input t qi key weights rowMaximum rowMass previousMaximum previousMass oldValues s
  have h1 := output_columns_memory_other ops input t qi key weights
    (outputScales ops key rowMaximum rowMass previousMaximum previousMass) (selectedMass ops key previousMass) oldValues
    0 256 (outputPrepared ops t qi key rowMaximum rowMass previousMaximum previousMass s) l (by intro c hc hb; exact hl c hb)
  exact (congrArg (fun state : State α => state.memory l) hs).trans
    (h1.trans (congrArg (fun memory => memory l)
      (output_prepared_frames ops t qi key rowMaximum rowMass previousMaximum previousMass s).2))

def firstScales (ops : Ops α) (input : Nat → Nat → α) (t : Nat) : ScaleValues α :=
  outputScales ops 0 (tileMaximum ops input t 0 0) (tileDenominator ops input t 0 0)
    (tileMaximum ops input t 0 0) (ops.literal 0 1)

theorem first_output_query (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) :
    (firstOutput ops input t s).indices t 7 = some 0 := by
  have h1 := output_updated_index ops input t 0 0 7 (firstTileWeights ops input t)
    (tileMaximum ops input t 0 0) (tileDenominator ops input t 0 0)
    (tileMaximum ops input t 0 0) (ops.literal 0 1) (fun _ => zeroValue ops) (firstWeights ops input t 0 s) (by decide) (by decide)
  exact (congrArg (fun state : State α => state.indices t 7) (first_output_state ops input t s)).trans
    (h1.trans (first_weights_query ops input t 0 s))

theorem first_output_scales (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) :
    ScaleReady t (firstScales ops input t) (selectedMass ops 0 (ops.literal 0 1)) (firstOutput ops input t s) :=
  Eq.mpr (congrArg (ScaleReady t (firstScales ops input t) (selectedMass ops 0 (ops.literal 0 1))) (first_output_state ops input t s))
    (output_updated_scales ops input t 0 0 (firstTileWeights ops input t)
      (tileMaximum ops input t 0 0) (tileDenominator ops input t 0 0)
      (tileMaximum ops input t 0 0) (ops.literal 0 1) (fun _ => zeroValue ops) (firstWeights ops input t 0 s))

#print axioms output_updated_index
#print axioms output_updated_scales
#print axioms output_updated_memory_other
#print axioms first_output_query
#print axioms first_output_scales
end LarkNativeAttention
