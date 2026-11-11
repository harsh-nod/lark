import Lark.NativeSoftmaxExpWaveFrame

/-! Actual sequential native-wave fold of the scalar exp and logical32 XOR sum
phase. Pending lanes retain the proved maximum entry, and earlier partials and
completed lane controls survive later waves. No barrier is resumed here. -/
namespace LarkNativeSoftmax
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

structure ExpWaveEntry (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ws : List Nat) (s : State α) : Prop where
  valid : row<p.rows
  pc : ∀ w ∈ ws, ∀ t ∈ cohortThreads row w 64, s.pc t=43
  native : ∀ w ∈ ws, ∀ t ∈ cohortThreads row w 64, MaxNativeIndices t s
  maximum : s.memory ⟨.shared,row,0,0⟩=some (rowMaximum ops input row)
  reads : Reads p input s
  epoch : ∀ w ∈ ws, ∀ t ∈ cohortThreads row w 64, (s.epochs t).block=2
  good : ∀ a ∈ s.trace, Good a

theorem exp_wave_entry_cohort (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row w : Nat) (ws : List Nat) (s : State α) (entry : ExpWaveEntry p ops input row ws s) (hw : w ∈ ws) :
    ExpCohortEntry p ops input row (cohortThreads row w 64) s :=
  ⟨entry.valid,entry.pc w hw,entry.native w hw,entry.maximum,entry.reads,entry.epoch w hw,entry.good⟩

theorem exp_wave_entry_tail (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row w : Nat) (ws : List Nat) (s : State α) (hw : w<16) (hn : w ∉ ws)
    (entry : ExpWaveEntry p ops input row (w::ws) s) :
    ExpWaveEntry p ops input row ws (expWave p ops input row w s) := by
  have hne : ∀ u ∈ ws, u ≠ w := by intro u hu he; subst u; exact hn hu
  exact {
    valid := entry.valid
    pc := by
      intro u hu t ht
      exact (exp_wave_other p ops input row w t s hw (cohorts_disjoint row u w t (hne u hu) ht)).1.trans
        (entry.pc u (by simp [hu]) t ht)
    native := by
      intro u hu t ht
      exact exp_wave_native p ops input row w t s hw (entry.native u (by simp [hu]) t ht)
    maximum := (exp_wave_maximum_frame p ops input row w s).trans entry.maximum
    reads := exp_wave_reads p ops input row w s entry.reads
    epoch := by
      intro u hu t ht
      exact (congrArg (fun epochs => (epochs t).block) (exp_wave_epochs p ops input row w s)).trans
        (entry.epoch u (by simp [hu]) t ht)
    good := exp_wave_good p ops input row w s hw (exp_wave_entry_cohort p ops input row w (w::ws) s entry (by simp)) }

def expWaveFold (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row : Nat)
    (ws : List Nat) (s : State α) : State α := ws.foldl (fun s w => expWave p ops input row w s) s

theorem exp_wave_fold_epochs (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ws : List Nat) (s : State α) : (expWaveFold p ops input row ws s).epochs=s.epochs := by
  induction ws generalizing s with
  | nil => rfl
  | cons w ws ih => exact (ih (expWave p ops input row w s)).trans (exp_wave_epochs p ops input row w s)

theorem exp_wave_fold_other (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ws : List Nat) (t : Nat) (s : State α) (hb : ∀ w ∈ ws, w<16)
    (ht : ∀ w ∈ ws, t ∉ cohortThreads row w 64) : OtherThread t t s (expWaveFold p ops input row ws s) := by
  induction ws generalizing s with
  | nil => exact ⟨rfl,rfl,rfl⟩
  | cons w ws ih =>
    exact other_thread_trans t t _ _ _ (exp_wave_other p ops input row w t s (hb w (by simp)) (ht w (by simp)))
      (ih (expWave p ops input row w s) (by intro u hu; exact hb u (by simp [hu]))
        (by intro u hu; exact ht u (by simp [hu])))

theorem exp_wave_fold_partial_other (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ws : List Nat) (t : Nat) (s : State α) (l : Location)
    (ht : ∀ w ∈ ws, t ∉ cohortThreads row w 64) (hp : SumPartialWrites t l) :
    (expWaveFold p ops input row ws s).memory l=s.memory l := by
  induction ws generalizing s with
  | nil => rfl
  | cons w ws ih =>
    exact (ih (expWave p ops input row w s) (by intro u hu; exact ht u (by simp [hu]))).trans
      (exp_wave_partial_other p ops input row w t s l (ht w (by simp)) hp)

theorem exp_wave_fold_run (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ws : List Nat) (s : State α) (hn : ws.Nodup) (hb : ∀ w ∈ ws, w<16)
    (entry : ExpWaveEntry p ops input row ws s) :
    ws.foldlM (fun s w => LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel (program guarded)
      (warpThreads (geometry p) row w) fuel.warp s) s=some (expWaveFold p ops input row ws s) := by
  induction ws generalizing s with
  | nil => rfl
  | cons w ws ih =>
    obtain ⟨hnot,htail⟩ := List.nodup_cons.mp hn
    rewrite [List.foldlM_cons,exp_wave_run p guarded ops input row w s (hb w (by simp))
      (exp_wave_entry_cohort p ops input row w (w::ws) s entry (by simp))]
    simp only [bind,Option.some_bind]
    exact ih _ htail (by intro u hu; exact hb u (by simp [hu]))
      (exp_wave_entry_tail p ops input row w ws s (hb w (by simp)) hnot entry)

theorem exp_wave_fold_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ws : List Nat) (s : State α) (hn : ws.Nodup) (hb : ∀ w ∈ ws, w<16)
    (entry : ExpWaveEntry p ops input row ws s) : ∀ a ∈ (expWaveFold p ops input row ws s).trace, Good a := by
  induction ws generalizing s with
  | nil => exact entry.good
  | cons w ws ih =>
    obtain ⟨hnot,htail⟩ := List.nodup_cons.mp hn
    exact ih _ htail (by intro u hu; exact hb u (by simp [hu]))
      (exp_wave_entry_tail p ops input row w ws s (hb w (by simp)) hnot entry)

theorem exp_wave_fold_member_pc (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ws : List Nat) (s : State α) (hn : ws.Nodup) (hb : ∀ w ∈ ws, w<16)
    (warp lane : Nat) (hw : warp ∈ ws) (hl : lane<64) :
    (expWaveFold p ops input row ws s).pc (cohortBase row warp+lane)=82 := by
  induction ws generalizing s with
  | nil => simp at hw
  | cons w ws ih =>
    obtain ⟨hnot,htail⟩ := List.nodup_cons.mp hn
    rcases List.mem_cons.mp hw with he | hm
    · subst warp
      have h := exp_wave_fold_other p ops input row ws (cohortBase row w+lane) (expWave p ops input row w s)
        (by intro u hu; exact hb u (by simp [hu]))
        (by intro u hu; exact cohort_disjoint row w u lane hl (by intro h; subst u; exact hnot hu))
      exact h.1.trans (exp_wave_pc p ops input row w lane s hl)
    · exact ih (expWave p ops input row w s) htail (by intro u hu; exact hb u (by simp [hu])) hm

theorem exp_cohort_partial_writer (row warp half : Nat) (hw : warp<16) (hh : half<2) :
    SumPartialWrites (cohortBase row warp+half*32) ⟨.shared,row,1,warp*2+half⟩ := by
  have hc := cohort_arithmetic row warp (half*32) hw (by omega)
  constructor
  · rewrite [hc.2.1]; omega
  · unfold sumPartialCell
    rewrite [hc.1,hc.2.1,show (warp*64+half*32)/32=warp*2+half by omega]
    rfl

theorem exp_wave_fold_partial (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ws : List Nat) (s : State α) (hn : ws.Nodup) (hb : ∀ w ∈ ws, w<16)
    (warp half : Nat) (hw : warp ∈ ws) (hh : half<2) :
    (expWaveFold p ops input row ws s).memory ⟨.shared,row,1,warp*2+half⟩=
      some (sumWaveValues ops input row warp 5 (half*32)) := by
  induction ws generalizing s with
  | nil => simp at hw
  | cons w ws ih =>
    obtain ⟨hnot,htail⟩ := List.nodup_cons.mp hn
    rcases List.mem_cons.mp hw with he | hm
    · subst warp
      have h := exp_wave_fold_partial_other p ops input row ws (cohortBase row w+half*32)
        (expWave p ops input row w s) ⟨.shared,row,1,w*2+half⟩
        (by intro u hu; exact cohort_disjoint row w u (half*32) (by omega) (by intro h; subst u; exact hnot hu))
        (exp_cohort_partial_writer row w half (hb w (by simp)) hh)
      exact h.trans (exp_wave_partial p ops input row w half s (hb w (by simp)) hh)
    · exact ih (expWave p ops input row w s) htail (by intro u hu; exact hb u (by simp [hu])) hm

theorem exp_wave_fold_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ws : List Nat) (s : State α) (reads : Reads p input s) : Reads p input (expWaveFold p ops input row ws s) := by
  induction ws generalizing s with
  | nil => exact reads
  | cons w ws ih => exact ih (expWave p ops input row w s) (exp_wave_reads p ops input row w s reads)

theorem exp_wave_fold_native (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ws : List Nat) (u : Nat) (s : State α) (hb : ∀ w ∈ ws, w<16)
    (hi : MaxNativeIndices u s) : MaxNativeIndices u (expWaveFold p ops input row ws s) := by
  induction ws generalizing s with
  | nil => exact hi
  | cons w ws ih =>
    exact ih (expWave p ops input row w s) (by intro v hv; exact hb v (by simp [hv]))
      (exp_wave_native p ops input row w u s (hb w (by simp)) hi)

#print axioms exp_wave_fold_reads
#print axioms exp_wave_fold_native
#print axioms exp_wave_entry_cohort
#print axioms exp_wave_entry_tail
#print axioms exp_wave_fold_epochs
#print axioms exp_wave_fold_other
#print axioms exp_wave_fold_partial_other
#print axioms exp_wave_fold_run
#print axioms exp_wave_fold_good
#print axioms exp_wave_fold_member_pc
#print axioms exp_cohort_partial_writer
#print axioms exp_wave_fold_partial
end LarkNativeSoftmax
