import Lark.NativeAttentionOutputComputed
import Lark.NativeAttentionWeightFrame

/-! Joined, source-bound first-query output prefix from native initialization.
PC 83 is a continuation before the private-state stores, not a completed launch. -/
namespace LarkNativeAttention
open LarkNonlinear
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def firstTileWeights (ops : Ops α) (input : Nat → Nat → α) (t : Nat) : Nat → α :=
  fun row => normalizedWeight ops (scoreValue ops input t 0 0 row) (tileMaximum ops input t 0 0)
def firstOutputValues (ops : Ops α) (input : Nat → Nat → α) (t : Nat) : Nat → α :=
  outputValues ops input t 0 (firstTileWeights ops input t)
    (outputScales ops 0 (tileMaximum ops input t 0 0) (tileDenominator ops input t 0 0)
      (tileMaximum ops input t 0 0) (ops.literal 0 1))
    (selectedMass ops 0 (ops.literal 0 1)) (fun _ => zeroValue ops)
def firstOutput (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) : State α :=
  outputUpdated ops input t 0 0 (firstTileWeights ops input t)
    (tileMaximum ops input t 0 0) (tileDenominator ops input t 0 0)
    (tileMaximum ops input t 0 0) (ops.literal 0 1) (fun _ => zeroValue ops) (firstWeights ops input t 0 s)

theorem first_output_state (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) :
    firstOutput ops input t s = outputUpdated ops input t 0 0 (firstTileWeights ops input t)
      (tileMaximum ops input t 0 0) (tileDenominator ops input t 0 0)
      (tileMaximum ops input t 0 0) (ops.literal 0 1) (fun _ => zeroValue ops) (firstWeights ops input t 0 s) := rfl

theorem first_output_eq (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (t extra : Nat) (s : State α)
    (ht : t < p.groups * 32) (hr : Reads p input s) (hn : NativeIndices t s) (hk : Tiles ops input t 0 s)
    (hj : s.indices t 5 = some 0) (ho : OutputRange t 0 (fun _ => zeroValue ops) 0 256 s) (hp : s.pc t = 21) :
    runLane ops (layout p) (geometry p) program t (extra + 119060) s =
      runLane ops (layout p) (geometry p) program t extra (firstOutput ops input t s) := by
  let next := firstWeights ops input t 0 s
  have fields := first_weights_fields ops input t 0 s
  have ho' : OutputRange t 0 (fun _ => zeroValue ops) 0 256 next := by
    intro c hc hb
    exact (first_weights_global ops input t 0 0 (globalAddress t 0 c) s).trans (ho c hc hb)
  have h1 := first_weights_eq p ops input t 0 (extra + 60169) s ht hr hn hk hp
  have h2 := output_update_eq p ops input t 0 0 extra (firstTileWeights ops input t)
    (tileMaximum ops input t 0 0) (tileDenominator ops input t 0 0)
    (tileMaximum ops input t 0 0) (ops.literal 0 1) (fun _ => zeroValue ops) next ht (by decide)
    (first_weights_values ops input t 0 s) (first_weights_tiles ops input t 0 s hk)
    (first_weights_native ops input t 0 s hn) (first_weights_query ops input t 0 s)
    ((first_weights_index ops input t 0 5 s (by decide) (by decide) (by decide) (by decide) (by decide)).trans hj)
    fields.2.1 fields.2.2.1 (by intro h; exact False.elim (h rfl)) ho' fields.1
  have steps : extra + 119060 = (extra + 60169) + 58891 := by omega
  exact (congrArg (fun n => runLane ops (layout p) (geometry p) program t n s) steps).trans (h1.trans h2)

theorem first_output_fields (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) :
    (firstOutput ops input t s).pc t = 83 ∧ (firstOutput ops input t s).epochs = s.epochs := by
  have hs := first_output_state ops input t s
  have hf := output_updated_fields ops input t 0 0 (firstTileWeights ops input t)
    (tileMaximum ops input t 0 0) (tileDenominator ops input t 0 0)
    (tileMaximum ops input t 0 0) (ops.literal 0 1) (fun _ => zeroValue ops) (firstWeights ops input t 0 s)
  exact ⟨(congrArg (fun state : State α => state.pc t) hs).trans hf.1,
    (congrArg (fun state : State α => state.epochs) hs).trans (hf.2.trans (first_weights_fields ops input t 0 s).2.2.2)⟩

theorem first_output_value (ops : Ops α) (input : Nat → Nat → α) (t col : Nat) (s : State α) (hc : col < 256) :
    (firstOutput ops input t s).memory (globalCell 0 (globalAddress t 0 col)) =
      some (firstOutputValues ops input t col) :=
  (congrArg (fun state : State α => state.memory (globalCell 0 (globalAddress t 0 col)))
    (first_output_state ops input t s)).trans
    (output_updated_value ops input t 0 0 col (firstTileWeights ops input t)
      (tileMaximum ops input t 0 0) (tileDenominator ops input t 0 0)
      (tileMaximum ops input t 0 0) (ops.literal 0 1) (fun _ => zeroValue ops) (firstWeights ops input t 0 s) hc)

theorem first_output_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (t : Nat)
    (s : State α) (hr : Reads p input s) : Reads p input (firstOutput ops input t s) :=
  Eq.mpr (congrArg (Reads p input) (first_output_state ops input t s))
    (output_updated_reads p ops input t 0 0 (firstTileWeights ops input t)
      (tileMaximum ops input t 0 0) (tileDenominator ops input t 0 0)
      (tileMaximum ops input t 0 0) (ops.literal 0 1) (fun _ => zeroValue ops) _ (first_weights_reads p ops input t 0 s hr))

theorem first_output_good (ops : Ops α) (input : Nat → Nat → α) (t : Nat)
    (s : State α) (he : (s.epochs t).block % 2 = 1) (hg : TraceGood s) : TraceGood (firstOutput ops input t s) := by
  have he' : ((firstWeights ops input t 0 s).epochs t).block % 2 = 1 := by
    rw [(first_weights_fields ops input t 0 s).2.2.2]
    exact he
  exact Eq.mpr (congrArg TraceGood (first_output_state ops input t s))
    (output_updated_good ops input t 0 0 (firstTileWeights ops input t)
      (tileMaximum ops input t 0 0) (tileDenominator ops input t 0 0)
      (tileMaximum ops input t 0 0) (ops.literal 0 1) (fun _ => zeroValue ops) _ (by decide)
      he' (first_weights_good ops input t 0 s he hg))

theorem first_output_from_resumed (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (b t extra : Nat) (s : State α) (hb : b < p.groups) (ht : t ∈ blockThreads (geometry p) b)
    (hr : Reads p input s) :
    runLane ops (layout p) (geometry p) program t (extra + 119060) (firstResumed p ops input b s) =
      runLane ops (layout p) (geometry p) program t extra (firstOutput ops input t (firstResumed p ops input b s)) := by
  have hbound : t < p.groups * 32 := by
    obtain ⟨lane, hl, rfl⟩ := (block_mem p b t).mp ht
    omega
  exact first_output_eq p ops input t extra _ hbound (first_resumed_reads p ops input b s hr)
    (first_resumed_native p ops input b t s ht) (first_resumed_tiles p ops input b t s ht)
    (first_resumed_key p ops input b t s ht)
    (by intro c hc hb; exact first_resumed_output p ops input b t 0 c s ht (by decide) hb)
    (first_resumed_pc p ops input b t s ht)

/-- From every input and outside memory: the real first native block resume,
then the real first-query lane continuation through all 256 output stores.
Neither the remaining query/key tiles nor a dense-reference certificate is claimed. -/
theorem first_output_initial_prefix (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (b t extra : Nat) (hb : b < p.groups)
    (ht : t ∈ blockThreads (geometry p) b) :
    ∃ final,
      runBlock ops (layout p) (geometry p) fuel program b fuel.block (initial (layout p) input outside) =
        runBlock ops (layout p) (geometry p) fuel program b 8
          (firstResumed p ops input b (initial (layout p) input outside)) ∧
      runLane ops (layout p) (geometry p) program t (extra + 119060)
          (firstResumed p ops input b (initial (layout p) input outside)) =
        runLane ops (layout p) (geometry p) program t extra final ∧
      final.pc t = 83 ∧
      (∀ col, col < 256 → final.memory (globalCell 0 (globalAddress t 0 col)) = some (firstOutputValues ops input t col)) ∧
      Reads p input final ∧ raceFree (geometry p) final.trace = true := by
  let start := initial (layout p) input outside
  let resumed := firstResumed p ops input b start
  have hr := initial_reads p input outside
  have hg : TraceGood resumed := first_resumed_good p ops input b start
    (by intro u hu; rfl) (by intro a ha; cases ha)
  have he : (resumed.epochs t).block % 2 = 1 :=
    congrArg (fun epoch : Epoch => epoch.block % 2) (first_resumed_epoch p ops input b t start ht)
  refine ⟨firstOutput ops input t resumed,
    first_block_step p ops input b 8 start hb hr (by intro u hu; rfl),
    first_output_from_resumed p ops input b t extra start hb ht hr,
    (first_output_fields ops input t resumed).1, ?_,
    first_output_reads p ops input t resumed (first_resumed_reads p ops input b start hr),
    race_free p _ (first_output_good ops input t resumed he hg)⟩
  intro col hc
  exact first_output_value ops input t col resumed hc

#print axioms first_output_eq
#print axioms first_output_fields
#print axioms first_output_value
#print axioms first_output_reads
#print axioms first_output_good
#print axioms first_output_from_resumed
#print axioms first_output_initial_prefix
end LarkNativeAttention
