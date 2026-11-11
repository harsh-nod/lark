import Lark.NativeAttentionOutputFrame

/-! Source query preparation and all score products for any query/key tile. -/
namespace LarkNativeAttention
open LarkNonlinear
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def rowScores (ops : Ops α) (input : Nat → Nat → α) (t qi key : Nat) (s : State α) : State α :=
  scoresComputed ops input t qi key (queryPrepared ops input t qi s)
theorem row_scores_state (ops : Ops α) (input : Nat → Nat → α) (t qi key : Nat) (s : State α) :
    rowScores ops input t qi key s = scoresComputed ops input t qi key (queryPrepared ops input t qi s) := rfl

theorem row_scores_eq (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (t qi key extra : Nat) (s : State α)
    (ht : t < p.groups * 32) (hi : qi < 4) (hr : Reads p input s) (hn : NativeIndices t s)
    (hk : Tiles ops input t key s) (hq : s.indices t 7 = some (qi : Int)) (hp : s.pc t = 22) :
    runLane ops (layout p) (geometry p) program t (extra + 58695) s =
      runLane ops (layout p) (geometry p) program t extra (rowScores ops input t qi key s) := by
  let next := queryPrepared ops input t qi s
  have hf := query_prepared_fields ops input t qi s
  have h1 := query_prepare_eq p ops input t qi (extra + 57666) s ht hi hr hn hq hp
  have h2 := score_computation_eq p ops input t qi key extra next (query_prepared_qi ops input t qi s)
    (query_prepared_tiles ops input t qi key s hk) (query_prepared_native ops input t qi s hn) hf.2.1 hf.2.2.1 hf.1
  have steps : extra + 58695 = (extra + 57666) + 1029 := by omega
  exact (congrArg (fun n => runLane ops (layout p) (geometry p) program t n s) steps).trans (h1.trans h2)

theorem row_scores_fields (ops : Ops α) (input : Nat → Nat → α) (t qi key : Nat) (s : State α) :
    (rowScores ops input t qi key s).pc t = 48 ∧
    (rowScores ops input t qi key s).regs t 0 = some (tileMaximum ops input t qi key) ∧
    (rowScores ops input t qi key s).epochs = s.epochs := by
  have hs := row_scores_state ops input t qi key s
  have hf := scores_computed_fields ops input t qi key (queryPrepared ops input t qi s)
  have hm := scores_computed_maximum ops input t qi key _ (query_prepared_fields ops input t qi s).2.2.1
  exact ⟨(congrArg (fun state : State α => state.pc t) hs).trans hf.1,
    (congrArg (fun state : State α => state.regs t 0) hs).trans hm,
    (congrArg (fun state : State α => state.epochs) hs).trans (hf.2.trans (query_prepared_fields ops input t qi s).2.2.2)⟩

theorem row_scores_values (ops : Ops α) (input : Nat → Nat → α) (t qi key : Nat) (s : State α) :
    ScoreRange t (scoreValues ops input t qi key) 0 32 (rowScores ops input t qi key s) :=
  Eq.mpr (congrArg (ScoreRange t (scoreValues ops input t qi key) 0 32) (row_scores_state ops input t qi key s))
    (scores_computed_values ops input t qi key _)

theorem row_scores_native (ops : Ops α) (input : Nat → Nat → α) (t qi key : Nat)
    (s : State α) (hn : NativeIndices t s) : NativeIndices t (rowScores ops input t qi key s) :=
  Eq.mpr (congrArg (NativeIndices t) (row_scores_state ops input t qi key s))
    (scores_computed_native ops input t qi key _ (query_prepared_native ops input t qi s hn))

theorem row_scores_index (ops : Ops α) (input : Nat → Nat → α) (t qi key r : Nat) (s : State α)
    (h8 : r ≠ 8) (h9 : r ≠ 9) (h10 : r ≠ 10) :
    (rowScores ops input t qi key s).indices t r = s.indices t r := by
  have hs : rowScores ops input t qi key s =
      scoreRows ops input t qi key 0 32 (ops.literal 0 1) (queryPrepared ops input t qi s) := rfl
  exact (congrArg (fun state : State α => state.indices t r) hs).trans
    ((score_rows_index ops input t qi key 0 32 r (ops.literal 0 1) _ h9 h10).trans
      (query_prepared_index ops input t qi r s h8 h9))

theorem row_scores_memory_other (ops : Ops α) (input : Nat → Nat → α) (t qi key : Nat) (s : State α) (l : Location)
    (hq : ∀ c, c < 256 → l ≠ sharedCell t 0 (sharedAddress t c))
    (hs : ∀ r, r < 32 → l ≠ sharedCell t 3 (scoreAddress t r)) :
    (rowScores ops input t qi key s).memory l = s.memory l := by
  have he : rowScores ops input t qi key s =
      scoreRows ops input t qi key 0 32 (ops.literal 0 1) (queryPrepared ops input t qi s) := rfl
  exact (congrArg (fun state : State α => state.memory l) he).trans
    ((score_rows_memory_other ops input t qi key 0 32 (ops.literal 0 1) _ l (by intro r hr hb; exact hs r hb)).trans
      (query_prepared_memory_other ops input t qi s l hq))

theorem row_scores_tiles (ops : Ops α) (input : Nat → Nat → α) (t qi key : Nat)
    (s : State α) (hk : Tiles ops input t key s) : Tiles ops input t key (rowScores ops input t qi key s) := by
  intro buffer hb row hr col hc
  exact (row_scores_memory_other ops input t qi key s (sharedCell t buffer (row * 256 + col))
    (by intro c hc; rcases hb with rfl | rfl <;> simp [sharedCell])
    (by intro r hr; rcases hb with rfl | rfl <;> simp [sharedCell])).trans (hk buffer hb row hr col hc)

theorem row_scores_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (t qi key : Nat)
    (s : State α) (hr : Reads p input s) : Reads p input (rowScores ops input t qi key s) :=
  Eq.mpr (congrArg (Reads p input) (row_scores_state ops input t qi key s))
    (scores_computed_reads p ops input t qi key _ (query_prepared_reads p ops input t qi s hr))

theorem row_scores_good (ops : Ops α) (input : Nat → Nat → α) (t qi key : Nat)
    (s : State α) (he : (s.epochs t).block % 2 = 1) (hg : TraceGood s) : TraceGood (rowScores ops input t qi key s) := by
  have he' : ((queryPrepared ops input t qi s).epochs t).block % 2 = 1 := by
    rw [(query_prepared_fields ops input t qi s).2.2.2]
    exact he
  exact Eq.mpr (congrArg TraceGood (row_scores_state ops input t qi key s))
    (scores_computed_good ops input t qi key _ he' (query_prepared_good ops input t qi s hg))

#print axioms row_scores_eq
#print axioms row_scores_fields
#print axioms row_scores_values
#print axioms row_scores_memory_other
#print axioms row_scores_good
end LarkNativeAttention
