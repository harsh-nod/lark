import Lark.NativeAttentionExpColumns

/-! Actual source execution through score exponentiation and denominator setup.
This is still a prefix: old-state selection and output computation follow PC 56. -/
namespace LarkNativeAttention
open LarkNonlinear
open LarkReduction (setIndex setReg execute_index_of execute_pure_of)
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def expEntry (ops : Ops α) (t : Nat) (s : State α) : State α :=
  setIndex (setReg s t 5 (ops.literal 0 1) 49) t 11 0 50
def weightsComputed (ops : Ops α) (t : Nat) (values : Nat → α) (maximum : α) (s : State α) : State α :=
  expColumns ops t values maximum 0 32 (ops.literal 0 1) (expEntry ops t s)

theorem exp_entry_fields (ops : Ops α) (t : Nat) (s : State α) :
    (expEntry ops t s).pc t = 50 ∧ (expEntry ops t s).indices t 11 = some 0 ∧
    (expEntry ops t s).regs t 5 = some (ops.literal 0 1) ∧ (expEntry ops t s).regs t 0 = s.regs t 0 := by
  simp [expEntry, setIndex, setReg, advance]

theorem exp_entry_native (ops : Ops α) (t : Nat) (s : State α) (hn : NativeIndices t s) :
    NativeIndices t (expEntry ops t s) := indices_set (setReg s t 5 (ops.literal 0 1) 49) t 11 50 0 (by decide) hn

theorem exp_computation_eq (p : Shape) (ops : Ops α) (t : Nat) (values : Nat → α)
    (extra : Nat) (maximum : α) (s : State α) (hs : ScoreRange t values 0 32 s)
    (hn : NativeIndices t s) (hm : s.regs t 0 = some maximum) (hp : s.pc t = 48) :
    runLane ops (layout p) (geometry p) program t (extra + 195) s =
      runLane ops (layout p) (geometry p) program t extra (weightsComputed ops t values maximum s) := by
  let s1 := setReg s t 5 (ops.literal 0 1) 49
  let s2 := expEntry ops t s
  have h1 := execute_pure_of ops (layout p) (geometry p) t 5 49 (.lit 0 1) s (ops.literal 0 1) (by rfl) (by omega)
  have h2 := execute_index_of ops (layout p) (geometry p) t 11 50 (.const 0) s1 0 (by rfl)
    (by simp [s1, setReg, advance])
  have hf := exp_entry_fields ops t s
  have e1 := source_step p ops t 48 (extra + 194) _ s s1 (by rfl) hp h1
  have e2 := source_step p ops t 49 (extra + 193) _ s1 s2 (by rfl) (by simp [s1, setReg, advance]) h2
  have e3 := exp_columns_eq p ops t values 0 32 extra maximum (ops.literal 0 1) s2 (by decide) hs
    (exp_entry_native ops t s hn) hf.2.1 (hf.2.2.2.trans hm) hf.2.2.1 hf.1
  exact e1.trans (e2.trans e3)

theorem weights_computed_fields (ops : Ops α) (t : Nat) (values : Nat → α) (maximum : α) (s : State α) :
    (weightsComputed ops t values maximum s).pc t = 56 ∧
    (weightsComputed ops t values maximum s).regs t 0 = s.regs t 0 ∧
    (weightsComputed ops t values maximum s).regs t 5 = some (expFold ops values maximum 0 32 (ops.literal 0 1)) ∧
    (weightsComputed ops t values maximum s).epochs = s.epochs := by
  have hf := exp_columns_fields ops t values 0 32 maximum (ops.literal 0 1) (expEntry ops t s)
  have hs := exp_columns_sum ops t values 0 32 maximum (ops.literal 0 1) (expEntry ops t s)
    (exp_entry_fields ops t s).2.2.1
  exact ⟨hf.1, hf.2.1.trans (exp_entry_fields ops t s).2.2.2, hs, hf.2.2⟩

theorem weights_computed_value (ops : Ops α) (t : Nat) (values : Nat → α) (col : Nat)
    (maximum : α) (s : State α) (hc : col < 32) :
    (weightsComputed ops t values maximum s).memory (sharedCell t 3 (scoreAddress t col)) =
      some (normalizedWeight ops (values col) maximum) :=
  exp_columns_value ops t values 0 32 col maximum (ops.literal 0 1) (expEntry ops t s) (by omega) hc

theorem weights_computed_native (ops : Ops α) (t : Nat) (values : Nat → α) (maximum : α)
    (s : State α) (hn : NativeIndices t s) : NativeIndices t (weightsComputed ops t values maximum s) :=
  exp_columns_native ops t values 0 32 maximum (ops.literal 0 1) _ (exp_entry_native ops t s hn)

theorem weights_computed_memory_other (ops : Ops α) (t : Nat) (values : Nat → α) (maximum : α)
    (s : State α) (l : Location) (hl : ∀ col, col < 32 → l ≠ sharedCell t 3 (scoreAddress t col)) :
    (weightsComputed ops t values maximum s).memory l = s.memory l :=
  exp_columns_memory_other ops t values 0 32 maximum (ops.literal 0 1) (expEntry ops t s) l
    (by intro c _ hc; exact hl c hc)

theorem weights_computed_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (t : Nat)
    (values : Nat → α) (maximum : α) (s : State α) (hr : Reads p input s) :
    Reads p input (weightsComputed ops t values maximum s) :=
  exp_columns_reads p ops input t values 0 32 maximum (ops.literal 0 1) (expEntry ops t s) hr

theorem weights_computed_good (ops : Ops α) (t : Nat) (values : Nat → α) (maximum : α)
    (s : State α) (hg : TraceGood s) : TraceGood (weightsComputed ops t values maximum s) :=
  exp_columns_good ops t values 0 32 maximum (ops.literal 0 1) (expEntry ops t s) (by decide) hg

def tileDenominator (ops : Ops α) (input : Nat → Nat → α) (t qi kj : Nat) : α :=
  expFold ops (scoreValues ops input t qi kj) (tileMaximum ops input t qi kj) 0 32 (ops.literal 0 1)
def firstWeights (ops : Ops α) (input : Nat → Nat → α) (t keyTile : Nat) (s : State α) : State α :=
  weightsComputed ops t (scoreValues ops input t 0 keyTile) (tileMaximum ops input t 0 keyTile)
    (firstScores ops input t keyTile s)

theorem first_weights_state (ops : Ops α) (input : Nat → Nat → α) (t keyTile : Nat) (s : State α) :
    firstWeights ops input t keyTile s = weightsComputed ops t (scoreValues ops input t 0 keyTile)
      (tileMaximum ops input t 0 keyTile) (firstScores ops input t keyTile s) := rfl

theorem first_weights_eq (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t keyTile extra : Nat) (s : State α) (ht : t < p.groups * 32) (hr : Reads p input s)
    (hn : NativeIndices t s) (hk : Tiles ops input t keyTile s) (hp : s.pc t = 21) :
    runLane ops (layout p) (geometry p) program t (extra + 58891) s =
      runLane ops (layout p) (geometry p) program t extra (firstWeights ops input t keyTile s) := by
  let s2 := firstScores ops input t keyTile s
  have h1 := first_scores_eq p ops input t keyTile (extra + 195) s ht hr hn hk hp
  have h2 := exp_computation_eq p ops t (scoreValues ops input t 0 keyTile) extra
    (tileMaximum ops input t 0 keyTile) s2 (first_scores_values ops input t keyTile s)
    (first_scores_native ops input t keyTile s hn) (first_scores_maximum ops input t keyTile s)
    (first_scores_fields ops input t keyTile s).1
  have hsteps : extra + 58891 = (extra + 195) + 58696 := by omega
  exact (congrArg (fun n => runLane ops (layout p) (geometry p) program t n s) hsteps).trans (h1.trans h2)

theorem first_weights_fields (ops : Ops α) (input : Nat → Nat → α) (t keyTile : Nat) (s : State α) :
    (firstWeights ops input t keyTile s).pc t = 56 ∧
    (firstWeights ops input t keyTile s).regs t 0 = some (tileMaximum ops input t 0 keyTile) ∧
    (firstWeights ops input t keyTile s).regs t 5 = some (tileDenominator ops input t 0 keyTile) ∧
    (firstWeights ops input t keyTile s).epochs = s.epochs := by
  have heq := first_weights_state ops input t keyTile s
  have hs := first_scores_fields ops input t keyTile s
  have hm := first_scores_maximum ops input t keyTile s
  have hw := weights_computed_fields ops t (scoreValues ops input t 0 keyTile) (tileMaximum ops input t 0 keyTile)
    (firstScores ops input t keyTile s)
  exact ⟨(congrArg (fun state : State α => state.pc t) heq).trans hw.1,
    (congrArg (fun state : State α => state.regs t 0) heq).trans (hw.2.1.trans hm),
    (congrArg (fun state : State α => state.regs t 5) heq).trans hw.2.2.1,
    (congrArg (fun state : State α => state.epochs) heq).trans (hw.2.2.2.trans hs.2)⟩

theorem first_weights_values (ops : Ops α) (input : Nat → Nat → α) (t keyTile : Nat) (s : State α) :
    ScoreRange t (fun row => normalizedWeight ops (scoreValue ops input t 0 keyTile row)
      (tileMaximum ops input t 0 keyTile)) 0 32 (firstWeights ops input t keyTile s) := by
  have h : ScoreRange t (fun row => normalizedWeight ops (scoreValue ops input t 0 keyTile row)
      (tileMaximum ops input t 0 keyTile)) 0 32
      (weightsComputed ops t (scoreValues ops input t 0 keyTile) (tileMaximum ops input t 0 keyTile)
        (firstScores ops input t keyTile s)) := by
    intro col hc hb
    exact weights_computed_value ops t (scoreValues ops input t 0 keyTile) col (tileMaximum ops input t 0 keyTile) _ hb
  exact Eq.mpr (congrArg (ScoreRange t (fun row => normalizedWeight ops (scoreValue ops input t 0 keyTile row)
    (tileMaximum ops input t 0 keyTile)) 0 32) (first_weights_state ops input t keyTile s)) h

theorem first_weights_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t keyTile : Nat) (s : State α) (hr : Reads p input s) : Reads p input (firstWeights ops input t keyTile s) :=
  Eq.mpr (congrArg (Reads p input) (first_weights_state ops input t keyTile s))
    (weights_computed_reads p ops input t _ _ _ (first_scores_reads p ops input t keyTile s hr))

theorem first_weights_good (ops : Ops α) (input : Nat → Nat → α) (t keyTile : Nat)
    (s : State α) (he : (s.epochs t).block % 2 = 1) (hg : TraceGood s) : TraceGood (firstWeights ops input t keyTile s) :=
  Eq.mpr (congrArg TraceGood (first_weights_state ops input t keyTile s))
    (weights_computed_good ops t _ _ _ (first_scores_good ops input t keyTile s he hg))

theorem first_weights_from_resumed (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (b t extra : Nat) (s : State α) (hb : b < p.groups) (ht : t ∈ blockThreads (geometry p) b)
    (hr : Reads p input s) :
    runLane ops (layout p) (geometry p) program t (extra + 58891) (firstResumed p ops input b s) =
      runLane ops (layout p) (geometry p) program t extra
        (firstWeights ops input t 0 (firstResumed p ops input b s)) := by
  have hbound : t < p.groups * 32 := by
    obtain ⟨lane, hl, rfl⟩ := (block_mem p b t).mp ht
    omega
  exact first_weights_eq p ops input t 0 extra _ hbound (first_resumed_reads p ops input b s hr)
    (first_resumed_native p ops input b t s ht) (first_resumed_tiles p ops input b t s ht)
    (first_resumed_pc p ops input b t s ht)

#print axioms exp_computation_eq
#print axioms weights_computed_fields
#print axioms weights_computed_value
#print axioms first_weights_eq
#print axioms first_weights_fields
#print axioms first_weights_values
#print axioms first_weights_reads
#print axioms first_weights_good
#print axioms first_weights_from_resumed
end LarkNativeAttention
