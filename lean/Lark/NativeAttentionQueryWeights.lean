import Lark.NativeAttentionQueryScores

/-! Actual weight/denominator computation for every query/key tile. -/
namespace LarkNativeAttention
open LarkNonlinear
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def rowWeights (ops : Ops α) (input : Nat → Nat → α) (t qi key : Nat) (s : State α) : State α :=
  weightsComputed ops t (scoreValues ops input t qi key) (tileMaximum ops input t qi key) (rowScores ops input t qi key s)
def rowWeightValues (ops : Ops α) (input : Nat → Nat → α) (t qi key : Nat) : Nat → α :=
  fun row => normalizedWeight ops (scoreValue ops input t qi key row) (tileMaximum ops input t qi key)
theorem row_weights_state (ops : Ops α) (input : Nat → Nat → α) (t qi key : Nat) (s : State α) :
    rowWeights ops input t qi key s =
      weightsComputed ops t (scoreValues ops input t qi key) (tileMaximum ops input t qi key) (rowScores ops input t qi key s) := rfl

theorem row_weights_eq (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (t qi key extra : Nat) (s : State α)
    (ht : t < p.groups * 32) (hi : qi < 4) (hr : Reads p input s) (hn : NativeIndices t s)
    (hk : Tiles ops input t key s) (hq : s.indices t 7 = some (qi : Int)) (hp : s.pc t = 22) :
    runLane ops (layout p) (geometry p) program t (extra + 58890) s =
      runLane ops (layout p) (geometry p) program t extra (rowWeights ops input t qi key s) := by
  have hf := row_scores_fields ops input t qi key s
  have h1 := row_scores_eq p ops input t qi key (extra + 195) s ht hi hr hn hk hq hp
  have h2 := exp_computation_eq p ops t (scoreValues ops input t qi key) extra (tileMaximum ops input t qi key)
    (rowScores ops input t qi key s) (row_scores_values ops input t qi key s) (row_scores_native ops input t qi key s hn) hf.2.1 hf.1
  have steps : extra + 58890 = (extra + 195) + 58695 := by omega
  exact (congrArg (fun n => runLane ops (layout p) (geometry p) program t n s) steps).trans (h1.trans h2)

theorem row_weights_fields (ops : Ops α) (input : Nat → Nat → α) (t qi key : Nat) (s : State α) :
    (rowWeights ops input t qi key s).pc t = 56 ∧
    (rowWeights ops input t qi key s).regs t 0 = some (tileMaximum ops input t qi key) ∧
    (rowWeights ops input t qi key s).regs t 5 = some (tileDenominator ops input t qi key) ∧
    (rowWeights ops input t qi key s).epochs = s.epochs := by
  have hs := row_weights_state ops input t qi key s
  have hf := weights_computed_fields ops t (scoreValues ops input t qi key) (tileMaximum ops input t qi key) (rowScores ops input t qi key s)
  have hr := row_scores_fields ops input t qi key s
  exact ⟨(congrArg (fun state : State α => state.pc t) hs).trans hf.1,
    (congrArg (fun state : State α => state.regs t 0) hs).trans (hf.2.1.trans hr.2.1),
    (congrArg (fun state : State α => state.regs t 5) hs).trans hf.2.2.1,
    (congrArg (fun state : State α => state.epochs) hs).trans (hf.2.2.2.trans hr.2.2)⟩

theorem row_weights_values (ops : Ops α) (input : Nat → Nat → α) (t qi key : Nat) (s : State α) :
    ScoreRange t (rowWeightValues ops input t qi key) 0 32 (rowWeights ops input t qi key s) := by
  have h : ScoreRange t (rowWeightValues ops input t qi key) 0 32
      (weightsComputed ops t (scoreValues ops input t qi key) (tileMaximum ops input t qi key) (rowScores ops input t qi key s)) := by
    intro row hr hb
    exact weights_computed_value ops t (scoreValues ops input t qi key) row (tileMaximum ops input t qi key) _ hb
  exact Eq.mpr (congrArg (ScoreRange t (rowWeightValues ops input t qi key) 0 32) (row_weights_state ops input t qi key s)) h

theorem row_weights_native (ops : Ops α) (input : Nat → Nat → α) (t qi key : Nat)
    (s : State α) (hn : NativeIndices t s) : NativeIndices t (rowWeights ops input t qi key s) :=
  Eq.mpr (congrArg (NativeIndices t) (row_weights_state ops input t qi key s))
    (weights_computed_native ops t _ _ _ (row_scores_native ops input t qi key s hn))

theorem row_weights_index (ops : Ops α) (input : Nat → Nat → α) (t qi key r : Nat) (s : State α)
    (h8 : r ≠ 8) (h9 : r ≠ 9) (h10 : r ≠ 10) (h11 : r ≠ 11) :
    (rowWeights ops input t qi key s).indices t r = s.indices t r :=
  (congrArg (fun state : State α => state.indices t r) (row_weights_state ops input t qi key s)).trans
    ((weights_computed_index ops t r (scoreValues ops input t qi key) (tileMaximum ops input t qi key) _ h11).trans
      (row_scores_index ops input t qi key r s h8 h9 h10))

theorem row_weights_memory_other (ops : Ops α) (input : Nat → Nat → α) (t qi key : Nat) (s : State α) (l : Location)
    (hq : ∀ c, c < 256 → l ≠ sharedCell t 0 (sharedAddress t c))
    (hs : ∀ r, r < 32 → l ≠ sharedCell t 3 (scoreAddress t r)) :
    (rowWeights ops input t qi key s).memory l = s.memory l :=
  (congrArg (fun state : State α => state.memory l) (row_weights_state ops input t qi key s)).trans
    ((weights_computed_memory_other ops t (scoreValues ops input t qi key) (tileMaximum ops input t qi key) _ l hs).trans
      (row_scores_memory_other ops input t qi key s l hq hs))

theorem row_weights_tiles (ops : Ops α) (input : Nat → Nat → α) (t qi key : Nat)
    (s : State α) (hk : Tiles ops input t key s) : Tiles ops input t key (rowWeights ops input t qi key s) := by
  intro buffer hb row hr col hc
  exact (row_weights_memory_other ops input t qi key s (sharedCell t buffer (row * 256 + col))
    (by intro c hc; rcases hb with rfl | rfl <;> simp [sharedCell])
    (by intro r hr; rcases hb with rfl | rfl <;> simp [sharedCell])).trans (hk buffer hb row hr col hc)

theorem row_weights_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (t qi key : Nat)
    (s : State α) (hr : Reads p input s) : Reads p input (rowWeights ops input t qi key s) :=
  Eq.mpr (congrArg (Reads p input) (row_weights_state ops input t qi key s))
    (weights_computed_reads p ops input t _ _ _ (row_scores_reads p ops input t qi key s hr))

theorem row_weights_good (ops : Ops α) (input : Nat → Nat → α) (t qi key : Nat)
    (s : State α) (he : (s.epochs t).block % 2 = 1) (hg : TraceGood s) : TraceGood (rowWeights ops input t qi key s) :=
  Eq.mpr (congrArg TraceGood (row_weights_state ops input t qi key s))
    (weights_computed_good ops t _ _ _ (row_scores_good ops input t qi key s he hg))

#print axioms row_weights_eq
#print axioms row_weights_fields
#print axioms row_weights_values
#print axioms row_weights_memory_other
#print axioms row_weights_good
end LarkNativeAttention
