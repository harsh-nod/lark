import Lark.NativeSglangRmsNormScaleLane
import Lark.NativeSglangRmsNormOutputCopyLane

/-! Complete actual output-phase lane execution from the reached second block
barrier resumption to halt109. All16 outputs match the source-ordered arbitrary
Ops expression, all81 accesses remain, and no prior trace-safety premise is
needed for successful execution. Whole-block/grid composition is still pending.
-/
namespace LarkNativeSglangRmsNorm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
attribute [local irreducible] prefixFold reductionSnapshot partialFold firstBlockFold secondFold regAddFold inverseFold secondSnapshot skipFold inactiveWaves scalePairs scaleRounds outputCopies

def outputLane (ops : Ops α) (input : Nat → Nat → α) (row tid t : Nat) (inverse : α) (s : State α) : State α :=
  copiedLane ops input row tid t inverse (scaledLane ops input row tid t inverse s)

theorem output_lane_run (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid t : Nat) (inverse : α) (s : State α) (hr : row<p.rows) (ht : tid<1024) (hp : s.pc t=77)
    (h0 : s.indices t 0=some (row : Int)) (h1 : s.indices t 1=some (tid : Int))
    (h3 : s.indices t 3=some ((tid/32 : Nat) : Int)) (shared : s.memory (partialSlot t (tid/32))=some inverse)
    (cached : InputPrefix input row tid 16 t s) (weights : WeightPrefix input tid 16 t s) :
    LarkCollective.runLane ops (layout p) (geometry p) (program true) t fuel.lane s=
      some (outputLane ops input row tid t inverse s) := by
  change LarkCollective.runLane ops (layout p) (geometry p) (program true) t (387+125) s=_
  rw [scaled_lane_eq p ops input row tid t 387 inverse s ht hp h0 h1 h3 shared cached weights]
  have fields := scaled_lane_fields ops input row tid t inverse s h0 h1 cached weights
  exact copied_lane_run p ops input row tid t 262 inverse _ hr ht fields.1 fields.2.1 fields.2.2.1
    (scaled_lane_prefix ops input row tid t inverse s h0 h1 cached weights)

theorem output_lane_prefix (ops : Ops α) (input : Nat → Nat → α)
    (row tid t : Nat) (inverse : α) (s : State α)
    (h0 : s.indices t 0=some (row : Int)) (h1 : s.indices t 1=some (tid : Int))
    (cached : InputPrefix input row tid 16 t s) (weights : WeightPrefix input tid 16 t s) :
    GlobalPrefix ops input row tid 16 inverse (outputLane ops input row tid t inverse s) := by
  have fields := scaled_lane_fields ops input row tid t inverse s h0 h1 cached weights
  exact copied_lane_prefix ops input row tid t inverse _ fields.2.1 fields.2.2.1
    (scaled_lane_prefix ops input row tid t inverse s h0 h1 cached weights)

theorem output_lane_private (ops : Ops α) (input : Nat → Nat → α)
    (row tid t : Nat) (inverse : α) (s : State α)
    (h0 : s.indices t 0=some (row : Int)) (h1 : s.indices t 1=some (tid : Int))
    (cached : InputPrefix input row tid 16 t s) (weights : WeightPrefix input tid 16 t s) :
    OutputPrefix ops input row tid 16 t inverse (outputLane ops input row tid t inverse s) := by
  have fields := scaled_lane_fields ops input row tid t inverse s h0 h1 cached weights
  exact (copied_lane_fields ops input row tid t inverse _ fields.2.1 fields.2.2.1
    (scaled_lane_prefix ops input row tid t inverse s h0 h1 cached weights)).2.2.2

theorem output_lane_pc (ops : Ops α) (input : Nat → Nat → α)
    (row tid t : Nat) (inverse : α) (s : State α) :
    (outputLane ops input row tid t inverse s).pc t=109 := by simp only [outputLane,copiedLane,advance,↓reduceIte]

theorem output_lane_memory_outside (ops : Ops α) (input : Nat → Nat → α)
    (row tid t : Nat) (inverse : α) (s : State α) (l : Location)
    (localOutside : OutsideOutput t l) (globalOutside : OutsideCopies row tid l) :
    (outputLane ops input row tid t inverse s).memory l=s.memory l :=
  (copied_lane_memory_outside ops input row tid t inverse _ l globalOutside).trans
    (scaled_lane_memory_outside ops input row tid t inverse s l localOutside)

theorem output_lane_epochs (ops : Ops α) (input : Nat → Nat → α)
    (row tid t : Nat) (inverse : α) (s : State α) :
    (outputLane ops input row tid t inverse s).epochs=s.epochs :=
  (copied_lane_epochs ops input row tid t inverse _).trans (scaled_lane_epochs ops input row tid t inverse s)

theorem output_lane_trace_length (ops : Ops α) (input : Nat → Nat → α)
    (row tid t : Nat) (inverse : α) (s : State α) :
    (outputLane ops input row tid t inverse s).trace.length=s.trace.length+81 := by
  simp only [outputLane,copied_lane_trace_length,scaled_lane_trace_length]

theorem output_lane_good (ops : Ops α) (input : Nat → Nat → α)
    (row tid t : Nat) (inverse : α) (s : State α) (ht : tid<1024) (he : t=row*1024+tid)
    (epoch : (s.epochs t).block=2) (good : ∀ event∈s.trace,Good event) :
    ∀ event∈(outputLane ops input row tid t inverse s).trace,Good event := by
  have hmod : t%1024=tid := by rw [he]; omega
  have scaled : ∀ event∈(scaledLane ops input row tid t inverse s).trace,Good event := by
    simpa only [hmod] using scaled_lane_good ops input row t inverse s epoch good
  exact copied_lane_good ops input row tid t inverse _ ht he scaled

theorem resumed_output_lane (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row w lane : Nat) (s : State α) (reads : Reads p input s)
    (hr : row<p.rows) (hw : w<16) (hl : lane<64) :
    let t := cohortBase row w+lane
    let tid := w*64+lane
    let reached := resumedSecondBlock p ops input row (resumedFirstBlock p ops input row s)
    LarkCollective.runLane ops (layout p) (geometry p) (program true) t fuel.lane reached=
      some (outputLane ops input row tid t (blockInverseValue ops input row (tid/32)) reached) := by
  dsimp only
  let t := cohortBase row w+lane
  let tid := w*64+lane
  let reached := resumedSecondBlock p ops input row (resumedFirstBlock p ops input row s)
  have ht := cohort_in_block p row w t hw ((cohort_mem row w 64 t).mpr ⟨lane,hl,rfl⟩)
  have coords := cohort_arithmetic row w lane hw hl
  have hrow : t/1024=row := coords.1
  have htid : t%1024=tid := coords.2.1
  have indices := resumed_twice_indices p ops input row t s reads ht
  have caches := resumed_twice_caches p ops input row w lane s reads hw hl
  apply output_lane_run p ops input row tid t _ reached hr (by dsimp only [tid]; omega)
  · exact resumed_second_block_pc p ops input row t (resumedFirstBlock p ops input row s) ht
  · simpa only [hrow] using indices.1
  · simpa only [htid] using indices.2.1
  · simpa only [htid] using indices.2.2.2
  · change reached.memory ⟨.shared,t/1024,0,tid/32⟩=_
    rw [hrow]
    exact resumed_twice_shared_values p ops input row (tid/32) s (by dsimp only [tid]; omega)
  · exact caches.1
  · exact caches.2

#print axioms output_lane_run
#print axioms output_lane_prefix
#print axioms output_lane_private
#print axioms output_lane_pc
#print axioms output_lane_memory_outside
#print axioms output_lane_epochs
#print axioms output_lane_trace_length
#print axioms output_lane_good
#print axioms resumed_output_lane
end LarkNativeSglangRmsNorm
