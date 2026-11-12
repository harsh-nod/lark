import Lark.NativeSglangRmsNormSecondBlock

/-! The reached output-phase state: lane-specific inverses, unchanged cached
halves and native indices, both barrier epochs, and the actual safe trace.
-/
namespace LarkNativeSglangRmsNorm
open LarkNonlinear LarkCollective
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
attribute [local irreducible] prefixFold reductionSnapshot partialFold firstBlockFold secondFold regAddFold inverseFold secondSnapshot skipFold inactiveWaves

theorem second_block_outside_shared (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) (l : Location) (hl : l.space≠.shared) :
    (secondBlock p ops input row s).memory l=s.memory l := by
  change (inactiveWaves row remainingWaves (waveSecond p ops input row s)).memory l=_
  rw [(inactive_waves_preserves row remainingWaves _).1]
  exact wave_second_outside_shared p ops input row s l hl

theorem second_block_shared_value (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row lane : Nat) (s : State α) (hl : lane<32) :
    (secondBlock p ops input row s).memory ⟨.shared,row,0,lane⟩=some (blockInverseValue ops input row lane) := by
  change (inactiveWaves row remainingWaves (waveSecond p ops input row s)).memory _=_
  rw [(inactive_waves_preserves row remainingWaves _).1]
  exact wave_second_shared_value p ops input row lane s hl

theorem resumed_twice_shared_values (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row lane : Nat) (s : State α) (hl : lane<32) :
    (resumedSecondBlock p ops input row (resumedFirstBlock p ops input row s)).memory ⟨.shared,row,0,lane⟩=
      some (blockInverseValue ops input row lane) :=
  second_block_shared_value p ops input row lane _ hl

theorem resumed_twice_indices (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row t : Nat) (s : State α) (reads : Reads p input s) (ht : t∈blockThreads (geometry p) row) :
    NativeIndices t (resumedSecondBlock p ops input row (resumedFirstBlock p ops input row s)) := by
  change NativeIndices t (secondBlock p ops input row (resumedFirstBlock p ops input row s))
  unfold NativeIndices
  rw [(second_block_indices_epochs p ops input row _).1]
  exact resumed_first_block_indices p ops input row t s reads ht

theorem resumed_twice_caches (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row w lane : Nat) (s : State α) (reads : Reads p input s) (hw : w<16) (hl : lane<64) :
    InputPrefix input row (w*64+lane) 16 (cohortBase row w+lane)
      (resumedSecondBlock p ops input row (resumedFirstBlock p ops input row s)) ∧
    WeightPrefix input (w*64+lane) 16 (cohortBase row w+lane)
      (resumedSecondBlock p ops input row (resumedFirstBlock p ops input row s)) := by
  have h := resumed_first_block_caches p ops input row w lane s reads hw hl
  constructor
  · intro k hk
    change (secondBlock p ops input row _).memory (privateCell _ 0 k)=_
    rw [second_block_outside_shared p ops input row _ _ (by simp [privateCell])]
    exact h.1 k hk
  · intro k hk
    change (secondBlock p ops input row _).memory (privateCell _ 1 k)=_
    rw [second_block_outside_shared p ops input row _ _ (by simp [privateCell])]
    exact h.2 k hk

theorem resumed_twice_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) (reads : Reads p input s) :
    Reads p input (resumedSecondBlock p ops input row (resumedFirstBlock p ops input row s)) := by
  have h := resumed_first_block_reads p ops input row s reads
  constructor
  · intro offset ho
    change (secondBlock p ops input row _).memory (globalCell 1 offset)=_
    rw [second_block_outside_shared p ops input row _ _ (by simp [globalCell])]
    exact h.1 offset ho
  · intro offset ho
    change (secondBlock p ops input row _).memory (globalCell 2 offset)=_
    rw [second_block_outside_shared p ops input row _ _ (by simp [globalCell])]
    exact h.2 offset ho

theorem resumed_twice_epochs (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row t : Nat) (s : State α) (ht : t∈blockThreads (geometry p) row) :
    ((resumedSecondBlock p ops input row (resumedFirstBlock p ops input row s)).epochs t).block=(s.epochs t).block+2 ∧
    ((resumedSecondBlock p ops input row (resumedFirstBlock p ops input row s)).epochs t).warp=(s.epochs t).warp ∧
    ((resumedSecondBlock p ops input row (resumedFirstBlock p ops input row s)).epochs t).grid=(s.epochs t).grid := by
  have h1 := resumed_first_block_epochs p ops input row t s ht
  have h2 := resumed_second_block_epochs p ops input row t (resumedFirstBlock p ops input row s) ht
  exact ⟨by omega,h2.2.1.trans h1.2.1,h2.2.2.trans h1.2.2⟩

theorem second_block_trace (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) :
    (secondBlock p ops input row s).trace=
      inverseEvents s.epochs (cohortThreads row 0 32) ++ secondEvents s.epochs (cohortThreads row 0 64) ++ s.trace := by
  change (inactiveWaves row remainingWaves _).trace=_
  rw [(inactive_waves_preserves row remainingWaves _).2.2.2.2,wave_second_trace]

theorem second_block_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) (epochs : ∀ t∈cohortThreads row 0 64,(s.epochs t).block=1)
    (good : ∀ event∈s.trace,Good event) :
    ∀ event∈(secondBlock p ops input row s).trace,Good event := by
  change ∀ event∈(inactiveWaves row remainingWaves _).trace,Good event
  rw [(inactive_waves_preserves row remainingWaves _).2.2.2.2]
  exact wave_second_good p ops input row s epochs good

theorem initial_resumed_twice_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row : Nat) :
    ∀ event∈(resumedSecondBlock p ops input row (resumedFirstBlock p ops input row (initial p input outside))).trace,
      Good event := by
  apply second_block_good
  · intro t ht
    have h := resumed_first_block_epochs p ops input row t (initial p input outside)
      (cohort_in_block p row 0 t (by decide) ht)
    exact h.1
  · exact initial_fixed_first_block_good p ops input outside row

theorem initial_resumed_twice_race_free (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row : Nat) :
    raceFree (geometry p)
      (resumedSecondBlock p ops input row (resumedFirstBlock p ops input row (initial p input outside))).trace=true :=
  race_free p _ (initial_resumed_twice_good p ops input outside row)

#print axioms second_block_outside_shared
#print axioms second_block_shared_value
#print axioms resumed_twice_shared_values
#print axioms resumed_twice_indices
#print axioms resumed_twice_caches
#print axioms resumed_twice_reads
#print axioms resumed_twice_epochs
#print axioms second_block_trace
#print axioms second_block_good
#print axioms initial_resumed_twice_good
#print axioms initial_resumed_twice_race_free
end LarkNativeSglangRmsNorm
