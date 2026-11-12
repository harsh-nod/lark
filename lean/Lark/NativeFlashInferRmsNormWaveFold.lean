import Lark.NativeFlashInferRmsNormWaveFrame

/-! The exact sequential native-wave fold in the first block phase. Its entry
invariant retains read-only input operands for every wave; both shared
partials of earlier waves survive later executions.
-/
namespace LarkNativeFlashInferRmsNorm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem cohort_disjoint (row a b lane : Nat) (hl : lane < 64) (hne : a ≠ b) :
    cohortBase row a + lane ∉ cohortThreads row b 64 := by
  intro ht
  obtain ⟨peer, hp, he⟩ := (cohort_mem row b 64 _).mp ht
  unfold cohortBase at he
  omega

theorem cohorts_disjoint (row a b t : Nat) (hne : a ≠ b) (ht : t ∈ cohortThreads row a 64) :
    t ∉ cohortThreads row b 64 := by
  obtain ⟨lane, hl, rfl⟩ := (cohort_mem row a 64 t).mp ht
  exact cohort_disjoint row a b lane hl hne

theorem cohort_partial_writer (row warp half : Nat) (hw : warp < 16) (hh : half < 2) :
    PartialWrites (cohortBase row warp + half * 32) ⟨.shared, row, 0, warp * 2 + half⟩ := by
  have coords := cohort_arithmetic row warp (half * 32) hw (by omega)
  constructor
  · rewrite [coords.2.1]; omega
  · unfold partialCell
    rewrite [coords.1, coords.2.1]
    have he : (warp * 64 + half * 32) / 32 = warp * 2 + half := by omega
    rewrite [he]
    rfl

structure WaveEntry (input : Nat → Nat → α) (row : Nat) (ws : List Nat) (s : State α) : Prop where
  pc : ∀ w ∈ ws, ∀ t ∈ cohortThreads row w 64, s.pc t = 0
  inputs : ∀ w ∈ ws, ∀ t ∈ cohortThreads row w 64, InputReady input (t / 1024) (t % 1024) s
  epoch : ∀ w ∈ ws, ∀ t ∈ cohortThreads row w 64, (s.epochs t).block = 0
  good : ∀ a ∈ s.trace, Good a

def waveFold (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row : Nat)
    (ws : List Nat) (s : State α) : State α := ws.foldl (fun s w => firstWave p ops input row w s) s

theorem wave_entry_tail (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row w : Nat) (ws : List Nat) (s : State α) (hr : row < p.rows) (hw : w < 16)
    (hn : w ∉ ws) (entry : WaveEntry input row (w :: ws) s) :
    WaveEntry input row ws (firstWave p ops input row w s) := by
  have hne : ∀ u ∈ ws, u ≠ w := by intro u hu he; subst u; exact hn hu
  exact {
    pc := by
      intro u hu t ht
      exact (first_wave_other p ops input row w t s (cohorts_disjoint row u w t (hne u hu) ht)).1.trans
        (entry.pc u (by simp [hu]) t ht)
    inputs := by
      intro u hu t ht
      exact first_wave_inputs p ops input row w (t / 1024) (t % 1024) s
        (entry.inputs u (by simp [hu]) t ht)
    epoch := by
      intro u hu t ht
      exact (congrArg (fun epochs => (epochs t).block) (first_wave_epochs p ops input row w s)).trans
        (entry.epoch u (by simp [hu]) t ht)
    good := first_wave_good p ops input row w s hr hw (entry.inputs w (by simp))
      (entry.epoch w (by simp)) entry.good }

theorem wave_fold_epochs (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ws : List Nat) (s : State α) : (waveFold p ops input row ws s).epochs = s.epochs := by
  induction ws generalizing s with
  | nil => rfl
  | cons w ws ih => exact (ih (firstWave p ops input row w s)).trans (first_wave_epochs p ops input row w s)

theorem wave_fold_input_frame (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ws : List Nat) (buffer offset : Nat) (s : State α) :
    (waveFold p ops input row ws s).memory (globalCell buffer offset) = s.memory (globalCell buffer offset) := by
  induction ws generalizing s with
  | nil => rfl
  | cons w ws ih =>
      exact (ih (firstWave p ops input row w s)).trans
        (first_wave_input_frame p ops input row w buffer offset s)

theorem wave_fold_other (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ws : List Nat) (t : Nat) (s : State α) (ht : ∀ w ∈ ws, t ∉ cohortThreads row w 64) :
    (waveFold p ops input row ws s).pc t = s.pc t ∧
    (waveFold p ops input row ws s).indices t = s.indices t ∧
    (waveFold p ops input row ws s).regs t = s.regs t := by
  induction ws generalizing s with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons w ws ih =>
      have h := ih (firstWave p ops input row w s) (by intro u hu; exact ht u (by simp [hu]))
      have h1 := first_wave_other p ops input row w t s (ht w (by simp))
      exact ⟨h.1.trans h1.1, h.2.1.trans h1.2.1, h.2.2.trans h1.2.2⟩

theorem wave_fold_done_other (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ws : List Nat) (t : Nat) (s : State α) (ht : ∀ w ∈ ws, t ∉ cohortThreads row w 64)
    (done : FirstDone ops input t s) : FirstDone ops input t (waveFold p ops input row ws s) := by
  induction ws generalizing s with
  | nil => exact done
  | cons w ws ih =>
      exact ih (firstWave p ops input row w s) (by intro u hu; exact ht u (by simp [hu]))
        (first_done_other p ops input row w t s (ht w (by simp)) done)

theorem wave_fold_partial_other (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ws : List Nat) (t : Nat) (s : State α) (l : Location)
    (ht : ∀ w ∈ ws, t ∉ cohortThreads row w 64) (hp : PartialWrites t l) :
    (waveFold p ops input row ws s).memory l = s.memory l := by
  induction ws generalizing s with
  | nil => rfl
  | cons w ws ih =>
      exact (ih (firstWave p ops input row w s) (by intro u hu; exact ht u (by simp [hu]))).trans
        (first_wave_partial_other p ops input row w t s l (ht w (by simp)) hp)

/-- The actual `foldlM runWarp` used by the block scheduler. -/
theorem wave_fold_run (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ws : List Nat) (s : State α) (hr : row < p.rows) (hn : ws.Nodup)
    (hb : ∀ w ∈ ws, w < 16) (entry : WaveEntry input row ws s) :
    ws.foldlM (fun s w => LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel program
      (warpThreads (geometry p) row w) fuel.warp s) s = some (waveFold p ops input row ws s) := by
  induction ws generalizing s with
  | nil => rfl
  | cons w ws ih =>
      obtain ⟨hnot, hnodup⟩ := List.nodup_cons.mp hn
      rewrite [List.foldlM_cons, first_wave_run p ops input row w s hr (hb w (by simp))
        (entry.pc w (by simp)) (entry.inputs w (by simp)) entry.good]
      simp only [bind, Option.some_bind]
      exact ih _ hnodup (by intro u hu; exact hb u (by simp [hu]))
        (wave_entry_tail p ops input row w ws s hr (hb w (by simp)) hnot entry)

theorem wave_fold_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ws : List Nat) (s : State α) (hr : row < p.rows) (hn : ws.Nodup)
    (hb : ∀ w ∈ ws, w < 16) (entry : WaveEntry input row ws s) :
    ∀ a ∈ (waveFold p ops input row ws s).trace, Good a := by
  induction ws generalizing s with
  | nil => exact entry.good
  | cons w ws ih =>
      obtain ⟨hnot, hnodup⟩ := List.nodup_cons.mp hn
      exact ih _ hnodup (by intro u hu; exact hb u (by simp [hu]))
        (wave_entry_tail p ops input row w ws s hr (hb w (by simp)) hnot entry)

theorem wave_fold_member (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ws : List Nat) (s : State α) (hr : row < p.rows) (hn : ws.Nodup)
    (hb : ∀ w ∈ ws, w < 16) (entry : WaveEntry input row ws s)
    (warp t : Nat) (hw : warp ∈ ws) (ht : t ∈ cohortThreads row warp 64) :
    FirstDone ops input t (waveFold p ops input row ws s) := by
  induction ws generalizing s with
  | nil => simp at hw
  | cons w ws ih =>
      obtain ⟨hnot, hnodup⟩ := List.nodup_cons.mp hn
      rcases List.mem_cons.mp hw with he | hm
      · subst warp
        apply wave_fold_done_other p ops input row ws t (firstWave p ops input row w s)
        · intro u hu
          exact cohorts_disjoint row w u t (by intro he; subst u; exact hnot hu) ht
        · exact first_wave_done p ops input row w s hr (hb w (by simp)) (entry.inputs w (by simp)) entry.good t ht
      · exact ih (firstWave p ops input row w s) hnodup (by intro u hu; exact hb u (by simp [hu]))
          (wave_entry_tail p ops input row w ws s hr (hb w (by simp)) hnot entry) hm

theorem wave_fold_partial (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ws : List Nat) (s : State α) (hn : ws.Nodup) (hb : ∀ w ∈ ws, w < 16)
    (warp half : Nat) (hw : warp ∈ ws) (hh : half < 2) :
    (waveFold p ops input row ws s).memory ⟨.shared, row, 0, warp * 2 + half⟩ =
      some (waveValues ops input row warp 5 (half * 32)) := by
  induction ws generalizing s with
  | nil => simp at hw
  | cons w ws ih =>
      obtain ⟨hnot, hnodup⟩ := List.nodup_cons.mp hn
      rcases List.mem_cons.mp hw with he | hm
      · subst warp
        have hframe := wave_fold_partial_other p ops input row ws (cohortBase row w + half * 32)
          (firstWave p ops input row w s) ⟨.shared, row, 0, w * 2 + half⟩
          (by intro u hu; exact cohort_disjoint row w u (half * 32) (by omega) (by intro he; subst u; exact hnot hu))
          (cohort_partial_writer row w half (hb w (by simp)) hh)
        exact hframe.trans (first_wave_partial p ops input row w half s (hb w (by simp)) hh)
      · exact ih (firstWave p ops input row w s) hnodup (by intro u hu; exact hb u (by simp [hu])) hm

#print axioms cohort_partial_writer
#print axioms wave_entry_tail
#print axioms wave_fold_epochs
#print axioms wave_fold_input_frame
#print axioms wave_fold_other
#print axioms wave_fold_done_other
#print axioms wave_fold_partial_other
#print axioms wave_fold_run
#print axioms wave_fold_good
#print axioms wave_fold_member
#print axioms wave_fold_partial
end LarkNativeFlashInferRmsNorm
