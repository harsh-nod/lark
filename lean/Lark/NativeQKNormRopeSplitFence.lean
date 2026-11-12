import Lark.NativeQKNormRopeFrames

/-! Actual warp-fence convergence and first resume in the split-half source.
The memory and historical trace stay unchanged; participating warp epochs advance. -/
namespace LarkNativeQKNormRope
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem split_barrier_code (pc : Nat) (h : pc = 59 ∨ pc = 97) :
    (program true)[pc]? = some (.scalar (.barrier .warp)) := by
  rcases h with rfl | rfl <;> decide

theorem cohort_split_barrier (block warp active pc : Nat) (s : State α) (hpos : 0 < active)
    (code : (program true)[pc]? = some (.scalar (.barrier .warp)))
    (hp : ∀ lane, lane < active → s.pc (cohortBase block warp + lane) = pc) :
    LarkPartitionCollective.nextCohort (program true) (cohortThreads block warp active) s = none ∧
    LarkCollective.converged (program true) (cohortThreads block warp active) s = some .warp := by
  have hp0 : s.pc (cohortBase block warp) = pc := by simpa only [Nat.add_zero] using hp 0 hpos
  have hf : (cohortThreads block warp active).filter (LarkPartitionCollective.isShuffle (program true) s) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro t ht
    obtain ⟨lane, hl, rfl⟩ := (cohort_mem block warp active t).mp ht
    simp only [LarkPartitionCollective.isShuffle, hp lane hl, code]
    decide
  have ha : (cohortThreads block warp active).all (fun t => s.pc t == s.pc (cohortBase block warp)) = true := by
    apply List.all_eq_true.mpr
    intro t ht
    obtain ⟨lane, hl, rfl⟩ := (cohort_mem block warp active t).mp ht
    simp [hp lane hl, hp0]
  constructor
  · simp only [LarkPartitionCollective.nextCohort, hf, List.head?_nil, bind, Option.bind]
  · unfold LarkCollective.converged
    rw [cohort_head block warp active hpos]
    simp only [bind, pure, Option.bind, ha, ↓reduceIte]
    unfold LarkCollective.parked
    rw [hp0, code]
    rfl

theorem continue_at_split_fence (p : Shape) (ops : Ops α) (block warp active pc n : Nat)
    (s : State α) (hpos : 0 < active)
    (code : (program true)[pc]? = some (.scalar (.barrier .warp)))
    (hp : ∀ lane, lane < active → s.pc (cohortBase block warp + lane) = pc) :
    continueCohort p true ops (cohortThreads block warp active) n s =
      LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel (program true)
        (cohortThreads block warp active) n (resume (cohortThreads block warp active) .warp s) := by
  obtain ⟨hc, hf⟩ := cohort_split_barrier block warp active pc s hpos code hp
  simp only [continueCohort, hc, hf, bind, pure, Option.some_bind, ↓reduceIte]

def splitFirstFence (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (block warp : Nat)
    (s : State α) : State α :=
  resume (cohortThreads block warp 64) .warp (normalWaveState p ops input block warp s)

theorem split_first_fence_pc (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (block warp lane : Nat)
    (s : State α) (hl : lane < 64) :
    (splitFirstFence p ops input block warp s).pc (cohortBase block warp + lane) = 60 := by
  have ht : (cohortThreads block warp 64).contains (cohortBase block warp + lane) = true :=
    List.contains_iff_mem.mpr ((cohort_mem block warp 64 _).mpr ⟨lane, hl, rfl⟩)
  simp only [splitFirstFence, resume, ht, ↓reduceIte,
    (normal_wave_ready p ops input block warp lane s hl).pc]

theorem split_first_fence_value (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (block warp lane e : Nat)
    (s : State α) (hl : lane < 64) (he : e < 4) :
    let t := cohortBase block warp + lane
    (splitFirstFence p ops input block warp s).regs t (18 + 2 * e) =
      some (normalizedValue ops input t (weightBuffer t)
        (normalScale ops (waveValues ops input block warp 5 lane)) e) :=
  normal_wave_value p ops input block warp lane e s hl he

theorem split_first_fence_indices (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (block warp lane : Nat)
    (s : State α) (hl : lane < 64) :
    NativeIndices (cohortBase block warp + lane) (splitFirstFence p ops input block warp s) :=
  (normal_wave_ready p ops input block warp lane s hl).indices

theorem split_first_fence_epoch (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (block warp lane : Nat)
    (s : State α) (hl : lane < 64) :
    let t := cohortBase block warp + lane
    ((splitFirstFence p ops input block warp s).epochs t).block = (s.epochs t).block ∧
    ((splitFirstFence p ops input block warp s).epochs t).warp = (s.epochs t).warp + 1 := by
  have ht : (cohortThreads block warp 64).contains (cohortBase block warp + lane) = true :=
    List.contains_iff_mem.mpr ((cohort_mem block warp 64 _).mpr ⟨lane, hl, rfl⟩)
  simp only [splitFirstFence, resume, ht, ↓reduceIte, bumpEpoch,
    (normal_wave_preserves p ops input block warp s).2]
  trivial

theorem split_first_fence_other (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (block warp t : Nat)
    (s : State α) (ht : t ∉ cohortThreads block warp 64) :
    (splitFirstFence p ops input block warp s).pc t = s.pc t ∧
    (splitFirstFence p ops input block warp s).indices t = s.indices t ∧
    (splitFirstFence p ops input block warp s).regs t = s.regs t ∧
    (splitFirstFence p ops input block warp s).epochs t = s.epochs t := by
  have hc : (cohortThreads block warp 64).contains t = false := by simp [ht]
  have frame := normal_wave_other p ops input block warp t s ht
  simp only [splitFirstFence, resume, hc, Bool.false_eq_true, ↓reduceIte]
  exact ⟨frame.1, frame.2.1, frame.2.2, congrFun (normal_wave_preserves p ops input block warp s).2 t⟩

theorem native_split_first_fence (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (block warp : Nat)
    (s : State α) (hb : block < p.rows * 5) (hw : warp < 4)
    (hp : ∀ t ∈ cohortThreads block warp 64, s.pc t = 0) (hr : Reads p input s) :
    LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel (program true)
      (warpThreads (geometry p) block warp) fuel.warp s =
      LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel (program true)
        (cohortThreads block warp 64) 10 (splitFirstFence p ops input block warp s) := by
  rw [native_normalization_step p ops input block warp s hb hw hp hr]
  exact continue_at_split_fence p ops block warp 64 59 10 _ (by decide)
    (split_barrier_code 59 (Or.inl rfl))
    (fun lane hl => (normal_wave_ready p ops input block warp lane s hl).pc)

#print axioms split_barrier_code
#print axioms cohort_split_barrier
#print axioms continue_at_split_fence
#print axioms split_first_fence_pc
#print axioms split_first_fence_value
#print axioms split_first_fence_indices
#print axioms split_first_fence_epoch
#print axioms split_first_fence_other
#print axioms native_split_first_fence
end LarkNativeQKNormRope
