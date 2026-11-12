import Lark.NativeQKNormRopeNormalWave

/-! Other-thread frames for the actual native reduction and preparation prefix. -/
namespace LarkNativeQKNormRope
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem xor_step_other (p : Shape) (ops : Ops α) (block warp active pc mask t : Nat)
    (values : Nat → α) (s : State α) (ht : t ∉ cohortThreads block warp active) :
    (xorStep p ops block warp active pc mask values s).pc t = s.pc t ∧
    (xorStep p ops block warp active pc mask values s).regs t = s.regs t := by
  have sf := xor_shuffled_other p block warp active mask 9 t values s ht
  have af := add_fold_other ops (pc + 1)
    (fun u => values (LarkPartitionCollective.nativeLane (geometry p) u))
    (fun u => values (xorPeer32 (LarkPartitionCollective.nativeLane (geometry p) u) mask))
    (cohortThreads block warp active) t
    (LarkCollective.shuffleUpdates 9 (xorSnapshot p block warp active mask values) s) ht
  exact ⟨af.1.trans sf.1, af.2.trans sf.2⟩

theorem first_stages_other (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (block warp n remaining t : Nat) (s : State α) (ht : t ∉ cohortThreads block warp 64) :
    (firstStages p ops input block warp n remaining s).pc t = s.pc t ∧
    (firstStages p ops input block warp n remaining s).regs t = s.regs t := by
  induction remaining generalizing n s with
  | zero => exact ⟨rfl, rfl⟩
  | succ remaining ih =>
      have first := xor_step_other p ops block warp 64 (24 + 2 * n) (xorMask n) t
        (waveValues ops input block warp n) s ht
      have later := ih (n + 1) (xorStep p ops block warp 64 (24 + 2 * n) (xorMask n)
        (waveValues ops input block warp n) s)
      exact ⟨later.1.trans first.1, later.2.trans first.2⟩

theorem first_four_other (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (block warp t : Nat) (s : State α) (ht : t ∉ cohortThreads block warp 64) :
    (firstFourState p ops input block warp s).pc t = s.pc t ∧
    (firstFourState p ops input block warp s).indices t = s.indices t ∧
    (firstFourState p ops input block warp s).regs t = s.regs t := by
  have preparedFrame := prepare_fold_other ops input (cohortThreads block warp 64) t s ht
  have stageFrame := first_stages_other p ops input block warp 0 4 t
    (prepareFold ops input (cohortThreads block warp 64) s) ht
  have allIndices := (first_four_preserves p ops input block warp s).2.1
  exact ⟨stageFrame.1.trans preparedFrame.1, (congrFun allIndices t).trans preparedFrame.2.1,
    stageFrame.2.trans preparedFrame.2.2⟩

theorem fifth_snapshot_other (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (block warp t : Nat) (s : State α) (ht : t ∉ cohortThreads block warp 64) :
    (fifthSnapshot p ops input block warp s).pc t = s.pc t ∧
    (fifthSnapshot p ops input block warp s).indices t = s.indices t ∧
    (fifthSnapshot p ops input block warp s).regs t = s.regs t := by
  have prefixFrame := first_four_other p ops input block warp t s ht
  have snapshotFrame := xor_shuffled_other p block warp 64 1 9 t (waveValues ops input block warp 4)
    (firstFourState p ops input block warp s) ht
  exact ⟨snapshotFrame.1.trans prefixFrame.1, prefixFrame.2.1, snapshotFrame.2.trans prefixFrame.2.2⟩

theorem normal_wave_other (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (block warp t : Nat) (s : State α) (ht : t ∉ cohortThreads block warp 64) :
    (normalWaveState p ops input block warp s).pc t = s.pc t ∧
    (normalWaveState p ops input block warp s).indices t = s.indices t ∧
    (normalWaveState p ops input block warp s).regs t = s.regs t := by
  have sf := fifth_snapshot_other p ops input block warp t s ht
  have nf := normal_fold_other ops input (reductionA ops input block warp) (reductionB ops input block warp)
    (cohortThreads block warp 64) t (fifthSnapshot p ops input block warp s) ht
  exact ⟨nf.1.trans sf.1, nf.2.1.trans sf.2.1, nf.2.2.trans sf.2.2⟩

#print axioms xor_step_other
#print axioms first_stages_other
#print axioms first_four_other
#print axioms fifth_snapshot_other
#print axioms normal_wave_other
end LarkNativeQKNormRope
