import Lark.NativeFusedRmsNormFirstWave

/-! Frames for composing the physical waves. Each first-wave execution changes
only its members' controls, their owned residual/unrounded cells, and the two
partial cells whose unique writers belong to that wave.
-/
namespace LarkNativeFusedRmsNorm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem xor_step_other (p : Shape) (ops : Ops α) (row warp active pc mask t : Nat)
    (values : Nat → α) (s : State α) (ht : t ∉ cohortThreads row warp active) :
    (xorStep p ops row warp active pc mask values s).pc t = s.pc t ∧
    (xorStep p ops row warp active pc mask values s).regs t = s.regs t := by
  have h := add_fold_other ops (pc + 1)
    (fun u => values (LarkPartitionCollective.nativeLane (geometry p) u))
    (fun u => values (xorPeer32 (LarkPartitionCollective.nativeLane (geometry p) u) mask))
    (cohortThreads row warp active) t (LarkCollective.shuffleUpdates 1 (xorSnapshot p row warp active mask values) s) ht
  have hs := xor_shuffled_other p row warp active mask t values s ht
  exact ⟨h.1.trans hs.1, h.2.trans hs.2⟩

theorem first_stages_other (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp n remaining t : Nat) (s : State α) (ht : t ∉ cohortThreads row warp 64) :
    (firstStages p ops input row warp n remaining s).pc t = s.pc t ∧
    (firstStages p ops input row warp n remaining s).regs t = s.regs t := by
  induction remaining generalizing n s with
  | zero => exact ⟨rfl, rfl⟩
  | succ remaining ih =>
      have h := ih (n + 1) (xorStep p ops row warp 64 (23 + 2 * n) (xorMask n) (waveValues ops input row warp n) s)
      have step := xor_step_other p ops row warp 64 (23 + 2 * n) (xorMask n) t (waveValues ops input row warp n) s ht
      exact ⟨h.1.trans step.1, h.2.trans step.2⟩

theorem last_wave_other (p : Shape) (ops : Ops α) (row warp t : Nat) (values : Nat → α)
    (s : State α) (ht : t ∉ cohortThreads row warp 64) :
    (lastWave p ops row warp values s).pc t = s.pc t ∧
    (lastWave p ops row warp values s).regs t = s.regs t := by
  have h := last_fold_other ops (waveLeft p values) (waveRight p values) (cohortThreads row warp 64) t
    (LarkCollective.shuffleUpdates 1 (xorSnapshot p row warp 64 1 values) s) ht
  have hs := xor_shuffled_other p row warp 64 1 t values s ht
  exact ⟨h.1.trans hs.1, h.2.trans hs.2⟩

theorem first_wave_indices_eq (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp : Nat) (s : State α) :
    (firstWave p ops input row warp s).indices = (prefixFold ops input (cohortThreads row warp 64) s).indices :=
  (last_wave_preserves p ops row warp (waveValues ops input row warp 4) _).1.trans
    (first_stages_preserves p ops input row warp 0 4 _).2.1

theorem first_wave_other (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp t : Nat) (s : State α) (ht : t ∉ cohortThreads row warp 64) :
    (firstWave p ops input row warp s).pc t = s.pc t ∧
    (firstWave p ops input row warp s).indices t = s.indices t ∧
    (firstWave p ops input row warp s).regs t = s.regs t := by
  have h0 := prefix_fold_other ops input (cohortThreads row warp 64) t s ht
  have h1 := first_stages_other p ops input row warp 0 4 t (prefixFold ops input (cohortThreads row warp 64) s) ht
  have h2 := last_wave_other p ops row warp t (waveValues ops input row warp 4)
    (firstStages p ops input row warp 0 4 (prefixFold ops input (cohortThreads row warp 64) s)) ht
  exact ⟨h2.1.trans (h1.1.trans h0.1),
    (congrFun (first_wave_indices_eq p ops input row warp s) t).trans h0.2.1,
    h2.2.trans (h1.2.trans h0.2.2)⟩

theorem first_wave_memory_frame (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp : Nat) (s : State α) (l : Location)
    (ho : ∀ t ∈ cohortThreads row warp 64, ¬ Owns t l)
    (hp : ∀ t ∈ cohortThreads row warp 64, ¬ PartialWrites t l) :
    (firstWave p ops input row warp s).memory l = s.memory l := by
  have h0 := prefix_fold_frame p ops input (cohortThreads row warp 64) s l ho
  have h1 := (first_stages_preserves p ops input row warp 0 4 (prefixFold ops input (cohortThreads row warp 64) s)).1
  have h2 := last_fold_memory_other ops (waveLeft p (waveValues ops input row warp 4))
    (waveRight p (waveValues ops input row warp 4)) (cohortThreads row warp 64)
    (LarkCollective.shuffleUpdates 1 (xorSnapshot p row warp 64 1 (waveValues ops input row warp 4))
      (firstStages p ops input row warp 0 4 (prefixFold ops input (cohortThreads row warp 64) s))) l hp
  exact h2.trans ((congrFun h1 l).trans h0)

theorem global_not_partial (t buffer offset : Nat) : ¬ PartialWrites t (globalCell buffer offset) := by
  intro h
  have hs := congrArg Location.space h.2
  simp [globalCell, partialCell] at hs

theorem owned_not_partial (t u : Nat) (l : Location) (ho : Owns t l) : ¬ PartialWrites u l := by
  intro h
  have hb : l.buffer = 1 := by rcases ho with ho | ho <;> exact ho.2.2.1
  have hz : l.buffer = 0 := by simpa only [partialCell] using congrArg Location.buffer h.2
  omega

theorem partial_not_owned (t u : Nat) (l : Location) (hp : PartialWrites t l) : ¬ Owns u l := by
  intro ho
  exact owned_not_partial u t l ho hp

theorem first_wave_input_frame (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp buffer offset : Nat) (s : State α) (hb : buffer = 0 ∨ buffer = 2) :
    (firstWave p ops input row warp s).memory (globalCell buffer offset) = s.memory (globalCell buffer offset) :=
  first_wave_memory_frame p ops input row warp s _
    (by intro t ht; exact global_input_unowned t buffer offset hb)
    (by intro t ht; exact global_not_partial t buffer offset)

theorem first_wave_owned_other (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp t : Nat) (s : State α) (l : Location) (ht : t ∉ cohortThreads row warp 64) (ho : Owns t l) :
    (firstWave p ops input row warp s).memory l = s.memory l := by
  apply first_wave_memory_frame p ops input row warp s l
  · intro u hu hou
    have he := owns_unique t u l ho hou
    exact ht (he ▸ hu)
  · intro u hu; exact owned_not_partial t u l ho

theorem first_wave_partial_other (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp t : Nat) (s : State α) (l : Location) (ht : t ∉ cohortThreads row warp 64) (hp : PartialWrites t l) :
    (firstWave p ops input row warp s).memory l = s.memory l := by
  apply first_wave_memory_frame p ops input row warp s l
  · intro u hu; exact partial_not_owned t u l hp
  · intro u hu hpu
    have he := partial_writes_unique t u l hp hpu
    exact ht (he ▸ hu)

theorem first_wave_pending_other (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp t ordinal : Nat) (s : State α) (ht : t ∉ cohortThreads row warp 64)
    (pending : Pending input (t / 1024) (t % 1024) ordinal s) :
    Pending input (t / 1024) (t % 1024) ordinal (firstWave p ops input row warp s) := by
  constructor
  · intro j hj
    exact (first_wave_input_frame p ops input row warp 0 _ s (Or.inl rfl)).trans (pending.1 j hj)
  · intro j hk hj
    exact (first_wave_owned_other p ops input row warp t s _ ht (residual_owned p t j hj)).trans (pending.2 j hk hj)

theorem first_wave_completed_other (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp t ordinal : Nat) (s : State α) (ht : t ∉ cohortThreads row warp 64) (ho : ordinal ≤ 16)
    (done : Completed ops input (t / 1024) (t % 1024) t ordinal s) :
    Completed ops input (t / 1024) (t % 1024) t ordinal (firstWave p ops input row warp s) := by
  intro j hj
  exact ⟨(first_wave_owned_other p ops input row warp t s _ ht (residual_owned p t j (by omega))).trans (done j hj).1,
    (first_wave_owned_other p ops input row warp t s _ ht (shared_owned t j (by omega))).trans (done j hj).2⟩

structure FirstDone (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) : Prop where
  pc : s.pc t = 35
  indices : NativeIndices t s
  pending : Pending input (t / 1024) (t % 1024) 16 s
  completed : Completed ops input (t / 1024) (t % 1024) t 16 s

theorem first_wave_done (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp : Nat) (s : State α) (hr : row < p.rows) (hw : warp < 16)
    (pending : ∀ t ∈ cohortThreads row warp 64, Pending input (t / 1024) (t % 1024) 0 s)
    (good : ∀ a ∈ s.trace, Good a) (t : Nat) (ht : t ∈ cohortThreads row warp 64) :
    FirstDone ops input t (firstWave p ops input row warp s) := by
  obtain ⟨lane, hl, he⟩ := (cohort_mem row warp 64 t).mp ht
  have pref := prefix_fold_member p ops input _ s (cohort_nodup row warp 64)
    (cohort_bound p row warp 64 hr hw (by decide)) pending good t ht
  have cells := first_wave_cells p ops input row warp s hr hw pending good t ht
  exact {
    pc := he ▸ first_wave_pc p ops input row warp s lane hl
    indices := by simpa only [NativeIndices, first_wave_indices_eq p ops input row warp s] using pref.indices
    pending := cells.1
    completed := cells.2 }

theorem first_done_other (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp t : Nat) (s : State α) (ht : t ∉ cohortThreads row warp 64) (done : FirstDone ops input t s) :
    FirstDone ops input t (firstWave p ops input row warp s) := by
  have h := first_wave_other p ops input row warp t s ht
  exact {
    pc := h.1.trans done.pc
    indices := by simpa only [NativeIndices, h.2.1] using done.indices
    pending := first_wave_pending_other p ops input row warp t 16 s ht done.pending
    completed := first_wave_completed_other p ops input row warp t 16 s ht (by decide) done.completed }

#print axioms xor_step_other
#print axioms first_stages_other
#print axioms first_wave_other
#print axioms first_wave_memory_frame
#print axioms first_wave_input_frame
#print axioms first_wave_owned_other
#print axioms first_wave_partial_other
#print axioms first_wave_pending_other
#print axioms first_wave_completed_other
#print axioms first_wave_done
#print axioms first_done_other
end LarkNativeFusedRmsNorm
