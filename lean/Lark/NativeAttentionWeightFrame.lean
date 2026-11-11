import Lark.NativeAttentionWeights

/-! Counters and memory frames needed to connect weight completion to outputs. -/
namespace LarkNativeAttention
open LarkNonlinear
open LarkReduction (setIndex setReg)
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem first_lane_key (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) :
    (firstLane ops input t s).indices t 5 = some 0 := by
  have hs : firstLane ops input t s =
      loadColumns ops input t 0 0 256 (loadEntry t (zeroInit ops t (headerState t s))) := rfl
  exact (congrArg (fun state : State α => state.indices t 5) hs).trans
    ((load_columns_fields ops input t 0 0 256 _).2.1.trans (load_entry_fields t _).2.1)

theorem first_fold_key (ops : Ops α) (input : Nat → Nat → α) (ts : List Nat)
    (t : Nat) (s : State α) (hn : ts.Nodup) (ht : t ∈ ts) :
    (firstFold ops input ts s).indices t 5 = some 0 := by
  induction ts generalizing s with
  | nil => simp at ht
  | cons u ts ih =>
      rcases List.nodup_cons.mp hn with ⟨hnot, hnodup⟩
      rcases List.mem_cons.mp ht with he | hm
      · subst t
        have hf := (first_fold_other ops input ts u (firstLane ops input u s) hnot).2.1
        exact (congrArg (fun indices => indices 5) hf).trans (first_lane_key ops input u s)
      · exact ih (firstLane ops input u s) hnodup hm

theorem first_resumed_key (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (b t : Nat) (s : State α) (ht : t ∈ blockThreads (geometry p) b) :
    (firstResumed p ops input b s).indices t 5 = some 0 := by
  have hi := first_fold_key ops input (blockThreads (geometry p) b) t s (block_nodup p b) ht
  have hf : (resume (blockThreads (geometry p) b) .block (firstBlock p ops input b s)).indices t 5 =
      (firstBlock p ops input b s).indices t 5 := rfl
  exact (congrArg (fun state : State α => state.indices t 5) (first_resumed_eq p ops input b s)).trans (hf.trans hi)

theorem weights_computed_index (ops : Ops α) (t r : Nat) (values : Nat → α) (maximum : α)
    (s : State α) (h11 : r ≠ 11) :
    (weightsComputed ops t values maximum s).indices t r = s.indices t r := by
  have hs : weightsComputed ops t values maximum s =
      expColumns ops t values maximum 0 32 (ops.literal 0 1) (expEntry ops t s) := rfl
  exact (congrArg (fun state : State α => state.indices t r) hs).trans
    ((exp_columns_index ops t values 0 32 r maximum (ops.literal 0 1) _ h11).trans
      (by simp [expEntry, setIndex, setReg, advance, h11]))

theorem first_weights_index (ops : Ops α) (input : Nat → Nat → α) (t key r : Nat)
    (s : State α) (h7 : r ≠ 7) (h8 : r ≠ 8) (h9 : r ≠ 9) (h10 : r ≠ 10) (h11 : r ≠ 11) :
    (firstWeights ops input t key s).indices t r = s.indices t r := by
  have h1 := weights_computed_index ops t r (scoreValues ops input t 0 key) (tileMaximum ops input t 0 key)
    (firstScores ops input t key s) h11
  have hs : firstScores ops input t key s = scoreRows ops input t 0 key 0 32 (ops.literal 0 1) (firstQuery ops input t s) := rfl
  have h2 := (congrArg (fun state : State α => state.indices t r) hs).trans
    (score_rows_index ops input t 0 key 0 32 r (ops.literal 0 1) _ h9 h10)
  have h3 : (firstQuery ops input t s).indices t r = s.indices t r :=
    (congrArg (fun state : State α => state.indices t r) (first_query_state ops input t s)).trans
    ((query_prepared_index ops input t 0 r (setIndex s t 7 0 22) h8 h9).trans
      (by simp [setIndex, advance, h7]))
  exact (congrArg (fun state : State α => state.indices t r) (first_weights_state ops input t key s)).trans
    (h1.trans (h2.trans h3))

theorem first_weights_query (ops : Ops α) (input : Nat → Nat → α) (t key : Nat) (s : State α) :
    (firstWeights ops input t key s).indices t 7 = some 0 := by
  have h1 := weights_computed_index ops t 7 (scoreValues ops input t 0 key) (tileMaximum ops input t 0 key)
    (firstScores ops input t key s) (by decide)
  have hs : firstScores ops input t key s = scoreRows ops input t 0 key 0 32 (ops.literal 0 1) (firstQuery ops input t s) := rfl
  have h2 := (congrArg (fun state : State α => state.indices t 7) hs).trans
    (score_rows_index ops input t 0 key 0 32 7 (ops.literal 0 1) _ (by decide) (by decide))
  have h3 : (firstQuery ops input t s).indices t 7 = some 0 :=
    (congrArg (fun state : State α => state.indices t 7) (first_query_state ops input t s)).trans
    ((query_prepared_index ops input t 0 7 (setIndex s t 7 0 22) (by decide) (by decide)).trans
      (by simp [setIndex, advance]))
  exact (congrArg (fun state : State α => state.indices t 7) (first_weights_state ops input t key s)).trans
    (h1.trans (h2.trans h3))

theorem first_weights_native (ops : Ops α) (input : Nat → Nat → α) (t key : Nat)
    (s : State α) (hn : NativeIndices t s) : NativeIndices t (firstWeights ops input t key s) :=
  Eq.mpr (congrArg (NativeIndices t) (first_weights_state ops input t key s))
    (weights_computed_native ops t _ _ _ (first_scores_native ops input t key s hn))

theorem first_weights_tiles (ops : Ops α) (input : Nat → Nat → α) (t key : Nat)
    (s : State α) (hk : Tiles ops input t key s) : Tiles ops input t key (firstWeights ops input t key s) := by
  have h1 := first_query_tiles ops input t key s hk
  have hs : firstScores ops input t key s = scoreRows ops input t 0 key 0 32 (ops.literal 0 1) (firstQuery ops input t s) := rfl
  have h2 : Tiles ops input t key (firstScores ops input t key s) :=
    Eq.mpr (congrArg (Tiles ops input t key) hs) (score_rows_tiles ops input t 0 key 0 32 (ops.literal 0 1) _ h1)
  have h3 : Tiles ops input t key (weightsComputed ops t (scoreValues ops input t 0 key)
      (tileMaximum ops input t 0 key) (firstScores ops input t key s)) := by
    intro buffer hb row hr col hc
    have hm := weights_computed_memory_other ops t (scoreValues ops input t 0 key) (tileMaximum ops input t 0 key)
      (firstScores ops input t key s) (sharedCell t buffer (row * 256 + col))
      (by intro c hc; rcases hb with rfl | rfl <;> simp [sharedCell])
    exact hm.trans (h2 buffer hb row hr col hc)
  exact Eq.mpr (congrArg (Tiles ops input t key) (first_weights_state ops input t key s)) h3

theorem first_weights_global (ops : Ops α) (input : Nat → Nat → α) (t key buffer index : Nat) (s : State α) :
    (firstWeights ops input t key s).memory (globalCell buffer index) = s.memory (globalCell buffer index) := by
  have h1 := weights_computed_memory_other ops t (scoreValues ops input t 0 key) (tileMaximum ops input t 0 key)
    (firstScores ops input t key s) (globalCell buffer index) (by intro c hc; simp [globalCell, sharedCell])
  have hs : firstScores ops input t key s = scoreRows ops input t 0 key 0 32 (ops.literal 0 1) (firstQuery ops input t s) := rfl
  have h2 := (congrArg (fun state : State α => state.memory (globalCell buffer index)) hs).trans
    (score_rows_memory_other ops input t 0 key 0 32 (ops.literal 0 1) _ (globalCell buffer index)
      (by intro r hr hb; simp [globalCell, sharedCell]))
  have h3 := (congrArg (fun state : State α => state.memory (globalCell buffer index)) (first_query_state ops input t s)).trans
    (query_prepared_memory_other ops input t 0 (setIndex s t 7 0 22) (globalCell buffer index)
      (by intro c hc; simp [globalCell, sharedCell]))
  exact (congrArg (fun state : State α => state.memory (globalCell buffer index)) (first_weights_state ops input t key s)).trans
    (h1.trans (h2.trans h3))

#print axioms first_resumed_key
#print axioms first_weights_index
#print axioms first_weights_query
#print axioms first_weights_native
#print axioms first_weights_tiles
#print axioms first_weights_global
end LarkNativeAttention
