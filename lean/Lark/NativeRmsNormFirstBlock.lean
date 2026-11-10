import Lark.NativeRmsNormWaveFrame

/-! Compose native wave executions during the first block phase.
Later barrier resumes, scale reduction and output remain separate obligations.
-/
namespace LarkNativeRmsNorm
open LarkNonlinear
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem cohort_disjoint (row a b lane : Nat) (hl : lane < 64) (hne : a ≠ b) :
    cohortBase row a + lane ∉ cohortThreads row b 64 := by
  intro ht
  obtain ⟨peer, hp, he⟩ := (cohort_mem row b 64 _).mp ht
  unfold cohortBase at he
  omega

theorem partial_cells_ne (row a b : Nat) (hne : a ≠ b) :
    partialCell (cohortBase row a) a ≠ partialCell (cohortBase row b) b := by
  intro he
  exact hne (congrArg Location.offset he)

def waveFold (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row : Nat)
    (ws : List Nat) (s : State α) : State α := ws.foldl (fun s warp => firstWave p ops input row warp s) s

theorem wave_fold_epochs (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ws : List Nat) (s : State α) : (waveFold p ops input row ws s).epochs = s.epochs := by
  induction ws generalizing s with
  | nil => rfl
  | cons w ws ih => exact (ih (firstWave p ops input row w s)).trans (first_wave_epochs p ops input row w s)

theorem wave_fold_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ws : List Nat) (s : State α) (reads : Reads p input s) :
    Reads p input (waveFold p ops input row ws s) := by
  induction ws generalizing s with
  | nil => exact reads
  | cons w ws ih => exact ih _ (first_wave_reads p ops input row w s reads)

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
      have hi := first_wave_indices_other p ops input row w t s (ht w (by simp))
      exact ⟨h.1.trans h1.1, h.2.1.trans hi, h.2.2.trans h1.2⟩

theorem wave_fold_memory_other (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ws : List Nat) (s : State α) (hb : ∀ w ∈ ws, w < 16)
    (l : Location) (hl : ∀ w ∈ ws, l ≠ partialCell (cohortBase row w) w) :
    (waveFold p ops input row ws s).memory l = s.memory l := by
  induction ws generalizing s with
  | nil => rfl
  | cons w ws ih =>
      have h := ih (firstWave p ops input row w s) (by intro u hu; exact hb u (by simp [hu]))
        (by intro u hu; exact hl u (by simp [hu]))
      exact h.trans (first_wave_memory_other p ops input row w s (hb w (by simp)) l (hl w (by simp)))

theorem wave_fold_member (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ws : List Nat) (s : State α) (hn : ws.Nodup) (hb : ∀ w ∈ ws, w < 16)
    (warp lane : Nat) (hw : warp ∈ ws) (hl : lane < 64) :
    (waveFold p ops input row ws s).pc (cohortBase row warp + lane) = 38 ∧
    NativeIndices (cohortBase row warp + lane) (waveFold p ops input row ws s) := by
  induction ws generalizing s with
  | nil => simp at hw
  | cons w ws ih =>
      rcases List.nodup_cons.mp hn with ⟨hnot, hnodup⟩
      rcases List.mem_cons.mp hw with he | hm
      · subst warp
        have ht : ∀ u ∈ ws, cohortBase row w + lane ∉ cohortThreads row u 64 := by
          intro u hu
          exact cohort_disjoint row w u lane hl (by intro he; subst u; exact hnot hu)
        have hf := wave_fold_other p ops input row ws (cohortBase row w + lane) (firstWave p ops input row w s) ht
        refine ⟨hf.1.trans (first_wave_pc p ops input row w s (hb w (by simp)) lane hl), ?_⟩
        have hi := first_wave_indices p ops input row w (cohortBase row w + lane) s
          ((cohort_mem row w 64 _).mpr ⟨lane, hl, rfl⟩)
        change NativeIndices _ (waveFold p ops input row ws (firstWave p ops input row w s))
        simpa only [NativeIndices, hf.2.1] using hi
      · exact ih (firstWave p ops input row w s) hnodup (by intro u hu; exact hb u (by simp [hu])) hm

theorem wave_fold_partial (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ws : List Nat) (s : State α) (hn : ws.Nodup) (hb : ∀ w ∈ ws, w < 16)
    (warp : Nat) (hw : warp ∈ ws) :
    (waveFold p ops input row ws s).memory (partialCell (cohortBase row warp) warp) =
      some (warpSum ops input row warp) := by
  induction ws generalizing s with
  | nil => simp at hw
  | cons w ws ih =>
      rcases List.nodup_cons.mp hn with ⟨hnot, hnodup⟩
      rcases List.mem_cons.mp hw with he | hm
      · subst warp
        have hframe := wave_fold_memory_other p ops input row ws (firstWave p ops input row w s)
          (by intro u hu; exact hb u (by simp [hu])) (partialCell (cohortBase row w) w)
          (by intro u hu; exact partial_cells_ne row w u (by intro he; subst u; exact hnot hu))
        exact hframe.trans (first_wave_partial p ops input row w s (hb w (by simp)))
      · exact ih (firstWave p ops input row w s) hnodup (by intro u hu; exact hb u (by simp [hu])) hm

/-- Actual sequential `runWarp` calls, preserving each not-yet-run wave's entry PC. -/
theorem wave_fold_run (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ws : List Nat) (s : State α) (hr : row < p.rows) (hn : ws.Nodup)
    (hb : ∀ w ∈ ws, w < 16) (reads : Reads p input s)
    (hp : ∀ w ∈ ws, ∀ lane, lane < 64 → s.pc (cohortBase row w + lane) = 0) :
    ws.foldlM (fun s w => LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel program
      (warpThreads (geometry p) row w) fuel.warp s) s = some (waveFold p ops input row ws s) := by
  induction ws generalizing s with
  | nil => rfl
  | cons w ws ih =>
      rcases List.nodup_cons.mp hn with ⟨hnot, hnodup⟩
      have hpc : ∀ u ∈ ws, ∀ lane, lane < 64 → (firstWave p ops input row w s).pc (cohortBase row u + lane) = 0 := by
        intro u hu lane hl
        have ht := cohort_disjoint row u w lane hl (by intro he; subst u; exact hnot hu)
        exact (first_wave_other p ops input row w _ s ht).1.trans (hp u (by simp [hu]) lane hl)
      rewrite [List.foldlM_cons, first_wave_run p ops input row w s hr (hb w (by simp)) reads (hp w (by simp))]
      simp only [bind, Option.some_bind]
      exact ih _ hnodup (by intro u hu; exact hb u (by simp [hu]))
        (first_wave_reads p ops input row w s reads) hpc

theorem wave_fold_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ws : List Nat) (s : State α) (hb : ∀ w ∈ ws, w < 16)
    (he : ∀ w ∈ ws, ∀ lane, lane < 64 → (s.epochs (cohortBase row w + lane)).block = 0)
    (good : ∀ access ∈ s.trace, LarkReductionFootprint.Good (traversal p) 0 access) :
    ∀ access ∈ (waveFold p ops input row ws s).trace, LarkReductionFootprint.Good (traversal p) 0 access := by
  induction ws generalizing s with
  | nil => exact good
  | cons w ws ih =>
      have h := first_wave_epochs p ops input row w s
      apply ih (firstWave p ops input row w s) (by intro u hu; exact hb u (by simp [hu]))
      · intro u hu lane hl
        exact (congrArg (fun epochs => (epochs (cohortBase row u + lane)).block) h).trans (he u (by simp [hu]) lane hl)
      · exact first_wave_good p ops input row w s (hb w (by simp)) (he w (by simp)) good

def firstBlock (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row : Nat) (s : State α) : State α :=
  waveFold p ops input row (List.range 16) s

theorem partial_cohort_cell (row warp : Nat) (hw : warp < 16) :
    partialCell (cohortBase row warp) warp = ⟨.shared, row, 0, warp⟩ := by
  have hr : cohortBase row warp / 1024 = row := by
    simpa only [Nat.add_zero] using (cohort_arithmetic row warp 0 hw (by decide)).1
  simp only [partialCell, hr]

theorem first_block_member (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid : Nat) (s : State α) (ht : tid < 1024) :
    (firstBlock p ops input row s).pc (row * 1024 + tid) = 38 ∧
    NativeIndices (row * 1024 + tid) (firstBlock p ops input row s) := by
  have hw : tid / 64 < 16 := by omega
  have hl : tid % 64 < 64 := Nat.mod_lt _ (by decide)
  have he : cohortBase row (tid / 64) + tid % 64 = row * 1024 + tid := by
    unfold cohortBase
    have hd := Nat.div_add_mod tid 64
    omega
  have h := wave_fold_member p ops input row (List.range 16) s List.nodup_range
    (fun w hw => List.mem_range.mp hw) (tid / 64) (tid % 64) (List.mem_range.mpr hw) hl
  simpa only [he] using h

theorem first_block_partial (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp : Nat) (s : State α) (hw : warp < 16) :
    (firstBlock p ops input row s).memory ⟨.shared, row, 0, warp⟩ = some (warpSum ops input row warp) := by
  have h := wave_fold_partial p ops input row (List.range 16) s List.nodup_range
    (fun w hw => List.mem_range.mp hw) warp (List.mem_range.mpr hw)
  rewrite [partial_cohort_cell row warp hw] at h
  exact h

theorem first_block_cut (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row : Nat) (s : State α) :
    LarkCollective.converged program (blockThreads (geometry p) row) (firstBlock p ops input row s) = some .block := by
  have hthreads : blockThreads (geometry p) row = cohortThreads row 0 1024 := by
    simp [blockThreads, geometry, cohortThreads, cohortBase]
  rewrite [hthreads]
  apply (cohort_first_barrier row 0 1024 _ (by decide) ?_).2
  intro tid ht
  simpa only [cohortBase, Nat.zero_mul, Nat.add_zero] using (first_block_member p ops input row tid s ht).1

/-- The exact first warp fold appearing in `runBlock`, at native 1024/64 geometry. -/
theorem first_block_fold_run (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) (hr : row < p.rows) (reads : Reads p input s)
    (hp : ∀ tid, tid < 1024 → s.pc (row * 1024 + tid) = 0) :
    (List.range (((geometry p).block + (geometry p).warp - 1) / (geometry p).warp)).foldlM
      (fun s w => LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel program
        (warpThreads (geometry p) row w) fuel.warp s) s = some (firstBlock p ops input row s) := by
  have hcount : ((geometry p).block + (geometry p).warp - 1) / (geometry p).warp = 16 := by
    change (1024 + 64 - 1) / 64 = 16
    decide
  rewrite [hcount]
  apply wave_fold_run p ops input row (List.range 16) s hr List.nodup_range
    (fun w hw => List.mem_range.mp hw) reads
  intro warp hw lane hl
  have hw := List.mem_range.mp hw
  simpa only [cohortBase, Nat.add_assoc] using hp (warp * 64 + lane) (by omega)

/-- Every input and initial outside memory: all 16 native waves complete the
first block phase, produce the intended partials, retain native indices and
read-only inputs, and have a race-free actual access trace at block epoch zero.
The remaining block phases and full launch are not asserted here. -/
theorem first_block_from_initial (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row : Nat) (hr : row < p.rows) :
    ∃ final,
      (List.range (((geometry p).block + (geometry p).warp - 1) / (geometry p).warp)).foldlM
        (fun s w => LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel program
          (warpThreads (geometry p) row w) fuel.warp s) (initial (layout p) input outside) = some final ∧
      LarkCollective.converged program (blockThreads (geometry p) row) final = some .block ∧
      (∀ tid, tid < 1024 → final.pc (row * 1024 + tid) = 38 ∧ NativeIndices (row * 1024 + tid) final) ∧
      (∀ warp, warp < 16 → final.memory ⟨.shared, row, 0, warp⟩ = some (warpSum ops input row warp)) ∧
      Reads p input final ∧ final.epochs = (initial (layout p) input outside).epochs ∧
      raceFree (geometry p) final.trace = true := by
  let start := initial (layout p) input outside
  have hread := initial_reads p input outside
  have hgood : ∀ access ∈ (firstBlock p ops input row start).trace,
      LarkReductionFootprint.Good (traversal p) 0 access :=
    wave_fold_good p ops input row (List.range 16) start (fun w hw => List.mem_range.mp hw)
      (by intro w hw lane hl; rfl) (by intro access ha; cases ha)
  refine ⟨firstBlock p ops input row start,
    first_block_fold_run p ops input row start hr hread (by intro tid ht; rfl),
    first_block_cut p ops input row start, ?_, ?_, wave_fold_reads p ops input row (List.range 16) start hread,
    wave_fold_epochs p ops input row (List.range 16) start, ?_⟩
  · intro tid ht; exact first_block_member p ops input row tid start ht
  · intro warp hw; exact first_block_partial p ops input row warp start hw
  · exact LarkReductionFootprint.race_free (traversal p) 0 _ hgood

#print axioms wave_fold_run
#print axioms wave_fold_partial
#print axioms wave_fold_member
#print axioms wave_fold_good
#print axioms first_block_from_initial
end LarkNativeRmsNorm
