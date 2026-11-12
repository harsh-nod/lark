import Lark.NativeSglangRmsNormOutputBlock

/-! Complete actual guarded SGLang native block execution from initialization:
both reductions, both block-barrier resumptions, all output loops and halt.
Successful execution, ordered output values and complete trace classification
are proved separately. Whole-grid and exact-real equality remain outside here.
-/
namespace LarkNativeSglangRmsNorm
open LarkNonlinear LarkCollective
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
attribute [local irreducible] prefixFold reductionSnapshot partialFold firstBlockFold secondFold regAddFold inverseFold secondSnapshot skipFold inactiveWaves scalePairs scaleRounds outputCopies outputFold

def completeBlock (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row : Nat) (s : State α) : State α :=
  outputBlock p ops input row (resumedSecondBlock p ops input row (resumedFirstBlock p ops input row s))

theorem complete_block_run (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) (hr : row<p.rows) (hp : ∀ t∈blockThreads (geometry p) row,s.pc t=0)
    (reads : Reads p input s) :
    LarkPartitionCollective.runBlock ops (layout p) (geometry p) fuel (program true) row fuel.block s=
      some (completeBlock p ops input row s) := by
  have first : LarkPartitionCollective.runBlock ops (layout p) (geometry p) fuel (program true) row fuel.block s=
      LarkPartitionCollective.runBlock ops (layout p) (geometry p) fuel (program true) row 2
        (resumedFirstBlock p ops input row s) := native_first_block_step p true ops input row 2 s hr hp reads
  rw [first,native_second_block_step p ops input row 1 s reads]
  exact output_block_run p ops input row _ hr (reached_output_block_ready p ops input row s reads)

theorem complete_block_pc (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row : Nat) (s : State α) :
    ∀ t∈blockThreads (geometry p) row,(completeBlock p ops input row s).pc t=109 :=
  output_block_all_pc p ops input row _

theorem complete_block_value (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component : Nat) (s : State α) (reads : Reads p input s)
    (ht : tid<1024) (hi : iteration<2) (hc : component<8) :
    (completeBlock p ops input row s).memory (globalCell 0 (address row (column tid iteration component)))=
      some (outputScaled ops input row tid iteration component (blockInverseValue ops input row (tid/32))) :=
  output_block_value p ops input row tid iteration component _ ht hi hc
    (reached_output_block_ready p ops input row s reads)

theorem complete_block_epochs (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row t : Nat) (s : State α) (ht : t∈blockThreads (geometry p) row) :
    ((completeBlock p ops input row s).epochs t).block=(s.epochs t).block+2 ∧
    ((completeBlock p ops input row s).epochs t).warp=(s.epochs t).warp ∧
    ((completeBlock p ops input row s).epochs t).grid=(s.epochs t).grid := by
  change ((outputBlock p ops input row _).epochs t).block=_ ∧
    ((outputBlock p ops input row _).epochs t).warp=_ ∧ ((outputBlock p ops input row _).epochs t).grid=_
  rw [output_block_epochs]
  exact resumed_twice_epochs p ops input row t s ht

theorem complete_block_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) (reads : Reads p input s)
    (epochs : ∀ t∈blockThreads (geometry p) row,(s.epochs t).block=0)
    (good : ∀ event∈s.trace,Good event) :
    ∀ event∈(completeBlock p ops input row s).trace,Good event := by
  change ∀ event∈(outputBlock p ops input row (resumedSecondBlock p ops input row (resumedFirstBlock p ops input row s))).trace,
    Good event
  apply output_block_good p ops input row (resumedSecondBlock p ops input row (resumedFirstBlock p ops input row s))
  · intro t ht
    have h := (resumed_twice_epochs p ops input row t s ht).1
    rw [epochs t ht] at h
    exact h
  · apply resumed_second_block_good p ops input row (resumedFirstBlock p ops input row s)
    · intro t ht
      have hb := cohort_in_block p row 0 t (by decide) ht
      have h := (resumed_first_block_epochs p ops input row t s hb).1
      rw [epochs t hb] at h
      exact h
    · exact resumed_first_block_good p ops input row s reads epochs good

theorem initial_complete_block_run (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row : Nat) (hr : row<p.rows) :
    LarkPartitionCollective.runBlock ops (layout p) (geometry p) fuel (program true) row fuel.block
      (initial p input outside)=some (completeBlock p ops input row (initial p input outside)) :=
  complete_block_run p ops input row _ hr (by intro t ht; rfl) (initial_reads p input outside)

theorem initial_complete_block_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row : Nat) :
    ∀ event∈(completeBlock p ops input row (initial p input outside)).trace,Good event :=
  complete_block_good p ops input row _ (initial_reads p input outside)
    (by intro t ht; rfl) (by intro event he; cases he)

theorem initial_complete_block_race_free (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row : Nat) :
    raceFree (geometry p) (completeBlock p ops input row (initial p input outside)).trace=true :=
  race_free p _ (initial_complete_block_good p ops input outside row)

theorem initial_complete_block_value (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row tid iteration component : Nat)
    (ht : tid<1024) (hi : iteration<2) (hc : component<8) :
    (completeBlock p ops input row (initial p input outside)).memory (globalCell 0 (address row (column tid iteration component)))=
      some (outputScaled ops input row tid iteration component (blockInverseValue ops input row (tid/32))) :=
  complete_block_value p ops input row tid iteration component _ (initial_reads p input outside) ht hi hc

#print axioms complete_block_run
#print axioms complete_block_pc
#print axioms complete_block_value
#print axioms complete_block_epochs
#print axioms complete_block_good
#print axioms initial_complete_block_run
#print axioms initial_complete_block_good
#print axioms initial_complete_block_race_free
#print axioms initial_complete_block_value
end LarkNativeSglangRmsNorm
