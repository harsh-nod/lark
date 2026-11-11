import Lark.NativeAttentionQueryTail
import Lark.NativeAttentionOutputFrame

/-! First-query completion through private running state and return to PC 22.
This is still one query row and one key tile, not a block or launch certificate. -/
namespace LarkNativeAttention
open LarkNonlinear
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def firstQueryComplete (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) : State α :=
  queryTail t 0 (firstScales ops input t) (firstOutput ops input t s)

theorem first_query_complete_state (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) :
    firstQueryComplete ops input t s = queryTail t 0 (firstScales ops input t) (firstOutput ops input t s) := rfl

theorem first_query_complete_eq (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (t extra : Nat) (s : State α)
    (ht : t < p.groups * 32) (hr : Reads p input s) (hn : NativeIndices t s) (hk : Tiles ops input t 0 s)
    (hj : s.indices t 5 = some 0) (ho : OutputRange t 0 (fun _ => zeroValue ops) 0 256 s) (hp : s.pc t = 21) :
    runLane ops (layout p) (geometry p) program t (extra + 119064) s =
      runLane ops (layout p) (geometry p) program t extra (firstQueryComplete ops input t s) := by
  have h1 := first_output_eq p ops input t (extra + 4) s ht hr hn hk hj ho hp
  have h2 := query_tail_eq p ops t 0 extra (firstScales ops input t) (selectedMass ops 0 (ops.literal 0 1))
    (firstOutput ops input t s) (by decide) (first_output_query ops input t s) (first_output_scales ops input t s)
    (first_output_fields ops input t s).1
  have steps : extra + 119064 = (extra + 4) + 119060 := by omega
  exact (congrArg (fun n => runLane ops (layout p) (geometry p) program t n s) steps).trans (h1.trans h2)

theorem first_query_complete_fields (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) :
    (firstQueryComplete ops input t s).pc t = 22 ∧
    (firstQueryComplete ops input t s).indices t 7 = some 1 ∧
    (firstQueryComplete ops input t s).epochs = s.epochs := by
  have hs := first_query_complete_state ops input t s
  have hf := query_tail_fields t 0 (firstScales ops input t) (firstOutput ops input t s)
  exact ⟨(congrArg (fun state : State α => state.pc t) hs).trans hf.1,
    (congrArg (fun state : State α => state.indices t 7) hs).trans hf.2.1,
    (congrArg (fun state : State α => state.epochs) hs).trans (hf.2.2.1.trans (first_output_fields ops input t s).2)⟩

theorem first_query_complete_output (ops : Ops α) (input : Nat → Nat → α) (t col : Nat) (s : State α) (hc : col < 256) :
    (firstQueryComplete ops input t s).memory (globalCell 0 (globalAddress t 0 col)) = some (firstOutputValues ops input t col) :=
  (congrArg (fun state : State α => state.memory (globalCell 0 (globalAddress t 0 col))) (first_query_complete_state ops input t s)).trans
    ((query_tail_global t 0 0 (globalAddress t 0 col) (firstScales ops input t) (firstOutput ops input t s)).trans
      (first_output_value ops input t col s hc))

theorem first_query_complete_private (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) :
    (firstQueryComplete ops input t s).memory (privateCell t 0 0) = some (firstScales ops input t).maximum ∧
    (firstQueryComplete ops input t s).memory (privateCell t 1 0) = some (firstScales ops input t).mass := by
  have hs := first_query_complete_state ops input t s
  have hf := query_tail_values t 0 (firstScales ops input t) (firstOutput ops input t s)
  exact ⟨(congrArg (fun state : State α => state.memory (privateCell t 0 0)) hs).trans hf.1,
    (congrArg (fun state : State α => state.memory (privateCell t 1 0)) hs).trans hf.2⟩

theorem first_query_complete_good (ops : Ops α) (input : Nat → Nat → α) (t : Nat)
    (s : State α) (he : (s.epochs t).block % 2 = 1) (hg : TraceGood s) : TraceGood (firstQueryComplete ops input t s) :=
  Eq.mpr (congrArg TraceGood (first_query_complete_state ops input t s))
    (query_tail_good t 0 (firstScales ops input t) _ (first_output_good ops input t s he hg))

#print axioms first_query_complete_eq
#print axioms first_query_complete_fields
#print axioms first_query_complete_output
#print axioms first_query_complete_private
#print axioms first_query_complete_good
end LarkNativeAttention
