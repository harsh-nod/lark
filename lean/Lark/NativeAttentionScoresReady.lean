import Lark.NativeAttentionScoreRows

/-! The full score tile and the actual query-to-score execution reduction. -/
namespace LarkNativeAttention
open LarkNonlinear
open LarkReduction (setIndex)
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def ScoreRange (t : Nat) (values : Nat → α) (start stop : Nat) (s : State α) : Prop :=
  ∀ row, start ≤ row → row < stop → s.memory (sharedCell t 3 (scoreAddress t row)) = some (values row)
def scoreValues (ops : Ops α) (input : Nat → Nat → α) (t qi kj : Nat) : Nat → α :=
  fun row => scoreValue ops input t qi kj row
def tileMaximum (ops : Ops α) (input : Nat → Nat → α) (t qi kj : Nat) : α :=
  maximumFold ops input t qi kj 0 32 (ops.literal 0 1)
def scoresComputed (ops : Ops α) (input : Nat → Nat → α) (t qi kj : Nat) (s : State α) : State α :=
  scoreRows ops input t qi kj 0 32 (ops.literal 0 1) s

theorem scores_computed_state (ops : Ops α) (input : Nat → Nat → α) (t qi kj : Nat) (s : State α) :
    scoresComputed ops input t qi kj s = scoreRows ops input t qi kj 0 32 (ops.literal 0 1) s := rfl

theorem scores_computed_native (ops : Ops α) (input : Nat → Nat → α) (t qi kj : Nat)
    (s : State α) (hn : NativeIndices t s) : NativeIndices t (scoresComputed ops input t qi kj s) :=
  Eq.mpr (congrArg (NativeIndices t) (scores_computed_state ops input t qi kj s))
    (score_rows_native ops input t qi kj 0 32 (ops.literal 0 1) s hn)

theorem scores_computed_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (t qi kj : Nat)
    (s : State α) (hr : Reads p input s) : Reads p input (scoresComputed ops input t qi kj s) :=
  Eq.mpr (congrArg (Reads p input) (scores_computed_state ops input t qi kj s))
    (score_rows_reads p ops input t qi kj 0 32 (ops.literal 0 1) s hr)

theorem scores_computed_good (ops : Ops α) (input : Nat → Nat → α) (t qi kj : Nat)
    (s : State α) (he : (s.epochs t).block % 2 = 1) (hg : TraceGood s) : TraceGood (scoresComputed ops input t qi kj s) :=
  Eq.mpr (congrArg TraceGood (scores_computed_state ops input t qi kj s))
    (score_rows_good ops input t qi kj 0 32 (ops.literal 0 1) s (by decide) he hg)

theorem score_computation_eq (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t qi kj extra : Nat) (s : State α) (hq : QiReady ops input t qi s) (hk : Tiles ops input t kj s)
    (hn : NativeIndices t s) (hi : s.indices t 9 = some 0) (hm : s.regs t 0 = some (ops.literal 0 1)) (hp : s.pc t = 30) :
    runLane ops (layout p) (geometry p) program t (extra + 57666) s =
      runLane ops (layout p) (geometry p) program t extra (scoresComputed ops input t qi kj s) := by
  simpa only [score_full_fuel] using
    score_rows_eq p ops input t qi kj 0 32 extra (ops.literal 0 1) s (by decide) hq hk hn hi hm hp

theorem scores_computed_values (ops : Ops α) (input : Nat → Nat → α) (t qi kj : Nat) (s : State α) :
    ScoreRange t (scoreValues ops input t qi kj) 0 32 (scoresComputed ops input t qi kj s) := by
  intro row hr hb
  exact score_rows_value ops input t qi kj 0 32 row (ops.literal 0 1) s hr hb

theorem scores_computed_maximum (ops : Ops α) (input : Nat → Nat → α) (t qi kj : Nat)
    (s : State α) (hm : s.regs t 0 = some (ops.literal 0 1)) :
    (scoresComputed ops input t qi kj s).regs t 0 = some (tileMaximum ops input t qi kj) :=
  score_rows_maximum ops input t qi kj 0 32 (ops.literal 0 1) s hm

theorem scores_computed_fields (ops : Ops α) (input : Nat → Nat → α) (t qi kj : Nat) (s : State α) :
    (scoresComputed ops input t qi kj s).pc t = 48 ∧
    (scoresComputed ops input t qi kj s).epochs = s.epochs := score_rows_fields ops input t qi kj 0 32 _ s

def firstScores (ops : Ops α) (input : Nat → Nat → α) (t keyTile : Nat) (s : State α) : State α :=
  scoresComputed ops input t 0 keyTile (firstQuery ops input t s)

theorem first_scores_state (ops : Ops α) (input : Nat → Nat → α) (t keyTile : Nat) (s : State α) :
    firstScores ops input t keyTile s = scoresComputed ops input t 0 keyTile (firstQuery ops input t s) := rfl

theorem first_scores_native (ops : Ops α) (input : Nat → Nat → α) (t keyTile : Nat)
    (s : State α) (hn : NativeIndices t s) : NativeIndices t (firstScores ops input t keyTile s) :=
  Eq.mpr (congrArg (NativeIndices t) (first_scores_state ops input t keyTile s))
    (scores_computed_native ops input t 0 keyTile _ (first_query_native ops input t s hn))

theorem first_scores_values (ops : Ops α) (input : Nat → Nat → α) (t keyTile : Nat) (s : State α) :
    ScoreRange t (scoreValues ops input t 0 keyTile) 0 32 (firstScores ops input t keyTile s) :=
  Eq.mpr (congrArg (ScoreRange t (scoreValues ops input t 0 keyTile) 0 32) (first_scores_state ops input t keyTile s))
    (scores_computed_values ops input t 0 keyTile _)

theorem first_scores_fields (ops : Ops α) (input : Nat → Nat → α) (t keyTile : Nat) (s : State α) :
    (firstScores ops input t keyTile s).pc t = 48 ∧ (firstScores ops input t keyTile s).epochs = s.epochs := by
  have hs := first_scores_state ops input t keyTile s
  have h := scores_computed_fields ops input t 0 keyTile (firstQuery ops input t s)
  exact ⟨(congrArg (fun state : State α => state.pc t) hs).trans h.1,
    (congrArg (fun state : State α => state.epochs) hs).trans (h.2.trans (first_query_fields ops input t s).2.2.2)⟩

theorem first_scores_maximum (ops : Ops α) (input : Nat → Nat → α) (t keyTile : Nat) (s : State α) :
    (firstScores ops input t keyTile s).regs t 0 = some (tileMaximum ops input t 0 keyTile) :=
  (congrArg (fun state : State α => state.regs t 0) (first_scores_state ops input t keyTile s)).trans
    (scores_computed_maximum ops input t 0 keyTile _ (first_query_fields ops input t s).2.2.1)

theorem first_scores_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (t keyTile : Nat)
    (s : State α) (hr : Reads p input s) : Reads p input (firstScores ops input t keyTile s) :=
  Eq.mpr (congrArg (Reads p input) (first_scores_state ops input t keyTile s))
    (scores_computed_reads p ops input t 0 keyTile _ (first_query_reads p ops input t s hr))

theorem first_scores_good (ops : Ops α) (input : Nat → Nat → α) (t keyTile : Nat)
    (s : State α) (he : (s.epochs t).block % 2 = 1) (hg : TraceGood s) : TraceGood (firstScores ops input t keyTile s) := by
  have heq : ((firstQuery ops input t s).epochs t).block % 2 = 1 :=
    Eq.mpr (congrArg (fun epochs : Nat → Epoch => (epochs t).block % 2 = 1) (first_query_fields ops input t s).2.2.2) he
  exact Eq.mpr (congrArg TraceGood (first_scores_state ops input t keyTile s))
    (scores_computed_good ops input t 0 keyTile _ heq (first_query_good ops input t s hg))

theorem first_scores_eq (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t keyTile extra : Nat) (s : State α) (ht : t < p.groups * 32) (hr : Reads p input s)
    (hn : NativeIndices t s) (hk : Tiles ops input t keyTile s) (hp : s.pc t = 21) :
    runLane ops (layout p) (geometry p) program t (extra + 58696) s =
      runLane ops (layout p) (geometry p) program t extra (firstScores ops input t keyTile s) := by
  let s1 := firstQuery ops input t s
  have hf := query_prepared_fields ops input t 0 (setIndex s t 7 0 22)
  have hn1 := query_prepared_native ops input t 0 (setIndex s t 7 0 22)
    (indices_set s t 7 22 0 (by decide) hn)
  have h1 := first_query_eq p ops input t (extra + 57666) s ht hr hn hp
  have h2 := score_computation_eq p ops input t 0 keyTile extra s1
    (first_query_qi ops input t s) (first_query_tiles ops input t keyTile s hk) hn1 hf.2.1 hf.2.2.1 hf.1
  exact h1.trans h2

theorem first_scores_from_resumed (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (b t extra : Nat) (s : State α) (hb : b < p.groups) (ht : t ∈ blockThreads (geometry p) b)
    (hr : Reads p input s) :
    runLane ops (layout p) (geometry p) program t (extra + 58696) (firstResumed p ops input b s) =
      runLane ops (layout p) (geometry p) program t extra
        (firstScores ops input t 0 (firstResumed p ops input b s)) := by
  have hbound : t < p.groups * 32 := by
    obtain ⟨lane, hl, rfl⟩ := (block_mem p b t).mp ht
    omega
  exact first_scores_eq p ops input t 0 extra _ hbound (first_resumed_reads p ops input b s hr)
    (first_resumed_native p ops input b t s ht) (first_resumed_tiles p ops input b t s ht)
    (first_resumed_pc p ops input b t s ht)

#print axioms score_computation_eq
#print axioms scores_computed_values
#print axioms scores_computed_maximum
#print axioms first_scores_from_resumed
end LarkNativeAttention
