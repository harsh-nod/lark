import Lark.NativeQKNormRopeWeightSelect
import Lark.NativeQKNormRopeNormalize
import Lark.NativeQKNormRopeReduction

/-! Complete actual scalar continuation from the final reduction snapshot to
PC59. Split-half parks here; interleaved continues into its rotary suffix. -/
namespace LarkNativeQKNormRope
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def normalWeights (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (a b : α) (s : State α) : State α :=
  weightSelected ops input t (weightIndexed t (scaleAfter ops t a b s))

def normalLane (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (a b : α) (s : State α) : State α :=
  normalizedFour ops input t (weightBuffer t) (normalScale ops (ops.add a b)) (normalWeights ops input t a b s)

theorem normal_weights_ready (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (a b : α)
    (s : State α) (hv : InputValues ops input t s) :
    NormalizeReady ops input t (weightBuffer t) (normalScale ops (ops.add a b)) (normalWeights ops input t a b s) := by
  refine ⟨?_, ?_, ?_⟩
  · intro r hr
    exact (weight_selected_low ops input t r _ (by omega)).trans ((scale_input_reg ops t r a b s hr).trans (hv r hr))
  · intro e he; exact weight_selected_value ops input t e _ he
  · exact (weight_selected_low ops input t 12 _ (by decide)).trans (scale_value ops t a b s)

theorem normal_lane_eq (p : Shape) (neox : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (t extra : Nat) (a b : α) (s : State α) (hp : s.pc t = 33)
    (ha : s.regs t 4 = some a) (hb : s.regs t 9 = some b)
    (hv : InputValues ops input t s) (hi : NativeIndices t s) (hr : Reads p input s) :
    LarkCollective.runLane ops (layout p) (geometry p) (program neox) t (extra + (weightSteps t + 16)) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program neox) t extra (normalLane ops input t a b s) := by
  let scaled := scaleAfter ops t a b s
  let indexedWeights := weightIndexed t scaled
  have hc : scaled.indices t 4 = some ((column t 0 : Nat) : Int) := hi.2.2.2.1
  have hh : indexedWeights.indices t 2 = some ((head t : Nat) : Int) :=
    (weight_indexed_low t 2 scaled (by decide)).trans hi.2.1
  have hcount : extra + (weightSteps t + 16) = ((extra + 8) + weightSteps t + 4) + 4 := by omega
  rw [hcount, scale_eq p neox ops t ((extra + 8) + weightSteps t + 4) a b s hp ha hb]
  rw [weight_indexed_eq p neox ops t ((extra + 8) + weightSteps t) scaled (scale_pc ops t a b s) hc]
  rw [weight_selected_eq p neox ops input t (extra + 8) indexedWeights (weight_indexed_pc t scaled) hh
    (fun e he => weight_indexed_value t e scaled he) hr]
  change LarkCollective.runLane ops (layout p) (geometry p) (program neox) t (extra + 8)
    (normalWeights ops input t a b s) = _
  exact normalized_four_eq p neox ops input t (weightBuffer t) (normalScale ops (ops.add a b)) extra
    (normalWeights ops input t a b s) (weight_selected_pc ops input t indexedWeights)
    (normal_weights_ready ops input t a b s hv)

theorem normal_lane_pc (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (a b : α) (s : State α) :
    (normalLane ops input t a b s).pc t = 59 :=
  normalized_four_pc ops input t (weightBuffer t) (normalScale ops (ops.add a b)) _

theorem normal_lane_value (ops : Ops α) (input : Nat → Nat → α) (t e : Nat) (a b : α)
    (s : State α) (he : e < 4) :
    (normalLane ops input t a b s).regs t (18 + 2 * e) =
      some (normalizedValue ops input t (weightBuffer t) (normalScale ops (ops.add a b)) e) :=
  normalized_four_value ops input t (weightBuffer t) (normalScale ops (ops.add a b)) e _ he

theorem normal_lane_preserves (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (a b : α) (s : State α) :
    (normalLane ops input t a b s).memory = s.memory ∧ (normalLane ops input t a b s).epochs = s.epochs := by
  have nf := normalized_four_preserves ops input t (weightBuffer t) (normalScale ops (ops.add a b))
    (normalWeights ops input t a b s)
  have wf := weight_selected_preserves ops input t (weightIndexed t (scaleAfter ops t a b s))
  exact ⟨nf.1.trans wf.1, nf.2.2.1.trans wf.2.2⟩

theorem normal_lane_low_index (ops : Ops α) (input : Nat → Nat → α) (t r : Nat) (a b : α)
    (s : State α) (hr : r < 11) : (normalLane ops input t a b s).indices t r = s.indices t r := by
  have nf := normalized_four_preserves ops input t (weightBuffer t) (normalScale ops (ops.add a b))
    (normalWeights ops input t a b s)
  have wf := weight_selected_preserves ops input t (weightIndexed t (scaleAfter ops t a b s))
  exact (congrFun (congrFun nf.2.1 t) r).trans
    ((congrFun (congrFun wf.2.1 t) r).trans (weight_indexed_low t r _ hr))

theorem normal_lane_indices (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (a b : α)
    (s : State α) (hi : NativeIndices t s) : NativeIndices t (normalLane ops input t a b s) := by
  simpa only [NativeIndices,
    normal_lane_low_index ops input t 1 a b s (by decide), normal_lane_low_index ops input t 2 a b s (by decide),
    normal_lane_low_index ops input t 3 a b s (by decide), normal_lane_low_index ops input t 4 a b s (by decide),
    normal_lane_low_index ops input t 5 a b s (by decide), normal_lane_low_index ops input t 6 a b s (by decide)] using hi

theorem normal_lane_trace (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (a b : α) (s : State α) :
    (normalLane ops input t a b s).trace =
      [⟨t, globalCell (weightBuffer t) (column t 3), false, s.epochs t⟩,
       ⟨t, globalCell (weightBuffer t) (column t 2), false, s.epochs t⟩,
       ⟨t, globalCell (weightBuffer t) (column t 1), false, s.epochs t⟩,
       ⟨t, globalCell (weightBuffer t) (column t 0), false, s.epochs t⟩] ++ s.trace := by
  have nf := normalized_four_preserves ops input t (weightBuffer t) (normalScale ops (ops.add a b))
    (normalWeights ops input t a b s)
  exact nf.2.2.2.trans (weight_selected_trace ops input t (weightIndexed t (scaleAfter ops t a b s)))

theorem normal_lane_good (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (a b : α)
    (s : State α) (good : ∀ access ∈ s.trace, Good access) :
    ∀ access ∈ (normalLane ops input t a b s).trace, Good access := by
  have nf := normalized_four_preserves ops input t (weightBuffer t) (normalScale ops (ops.add a b))
    (normalWeights ops input t a b s)
  change ∀ access ∈ (normalizedFour ops input t (weightBuffer t) (normalScale ops (ops.add a b))
    (normalWeights ops input t a b s)).trace, Good access
  rw [nf.2.2.2]
  exact weight_selected_good ops input t (weightIndexed t (scaleAfter ops t a b s)) good

theorem normal_lane_other (ops : Ops α) (input : Nat → Nat → α) (t u : Nat) (a b : α)
    (s : State α) (hu : u ≠ t) :
    (normalLane ops input t a b s).pc u = s.pc u ∧
    (normalLane ops input t a b s).indices u = s.indices u ∧
    (normalLane ops input t a b s).regs u = s.regs u := by
  have nf := normalized_four_other ops input t (weightBuffer t) (normalScale ops (ops.add a b)) u
    (normalWeights ops input t a b s) hu
  have wi := weight_indexed_other t u (scaleAfter ops t a b s) hu
  have wf := weight_selected_other ops input t u (weightIndexed t (scaleAfter ops t a b s)) hu
  have sc := scale_other ops t u a b s hu
  have ni := normalized_four_preserves ops input t (weightBuffer t) (normalScale ops (ops.add a b))
    (normalWeights ops input t a b s)
  have wsi := weight_selected_preserves ops input t (weightIndexed t (scaleAfter ops t a b s))
  exact ⟨nf.1.trans (wf.1.trans (wi.1.trans sc.1)),
    (congrFun ni.2.1 u).trans ((congrFun wsi.2.1 u).trans wi.2), nf.2.trans (wf.2.trans sc.2)⟩

#print axioms normal_weights_ready
#print axioms normal_lane_eq
#print axioms normal_lane_pc
#print axioms normal_lane_value
#print axioms normal_lane_preserves
#print axioms normal_lane_low_index
#print axioms normal_lane_indices
#print axioms normal_lane_trace
#print axioms normal_lane_good
#print axioms normal_lane_other
end LarkNativeQKNormRope
