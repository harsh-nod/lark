import Lark.NativeSoftmaxMaxWaveTree

/-! Frames for composing the physical waves. Each first-wave execution changes
only its members' controls and the two
partial cells whose unique writers belong to that wave.
-/
namespace LarkNativeSoftmax
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem max_fold_other (ops : Ops α) (input : Nat → Nat → α) (ts : List Nat)
    (t : Nat) (s : State α) (ht : t ∉ ts) :
    (maxPrefixFold ops input ts s).pc t = s.pc t ∧
    (maxPrefixFold ops input ts s).indices t = s.indices t ∧
    (maxPrefixFold ops input ts s).regs t = s.regs t := by
  induction ts generalizing s with
  | nil => exact ⟨rfl,rfl,rfl⟩
  | cons u ts ih =>
    have hu : t ≠ u := by intro he; subst t; simp at ht
    have hn : t ∉ ts := by intro hm; exact ht (by simp [hm])
    have tail := ih (maxPrefixState ops input u s) hn
    have head := max_prefix_other ops input u t s hu
    exact ⟨tail.1.trans head.1,tail.2.1.trans head.2.1,tail.2.2.trans head.2.2⟩

theorem down_step_other (p : Shape) (ops : Ops α) (row warp active pc distance t : Nat)
    (values : Nat → α) (s : State α) (ht : t ∉ cohortThreads row warp active) :
    (downStep p ops row warp active pc distance values s).pc t = s.pc t ∧
    (downStep p ops row warp active pc distance values s).regs t = s.regs t := by
  have h := combine_fold_other ops (pc + 1)
    (fun u => values (LarkPartitionCollective.nativeLane (geometry p) u))
    (fun u => values (downPeer32 (LarkPartitionCollective.nativeLane (geometry p) u) distance))
    (cohortThreads row warp active) t (LarkCollective.shuffleUpdates 2 (downSnapshot p row warp active distance values) s) ht
  have hs := down_shuffled_other p row warp active distance t values s ht
  exact ⟨h.1.trans hs.1, h.2.trans hs.2⟩

theorem first_stages_other (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp n remaining t : Nat) (s : State α) (ht : t ∉ cohortThreads row warp 64) :
    (firstStages p ops input row warp n remaining s).pc t = s.pc t ∧
    (firstStages p ops input row warp n remaining s).regs t = s.regs t := by
  induction remaining generalizing n s with
  | zero => exact ⟨rfl, rfl⟩
  | succ remaining ih =>
      have h := ih (n + 1) (downStep p ops row warp 64 (20 + 2 * n) (downDistance n) (waveValues ops input row warp n) s)
      have step := down_step_other p ops row warp 64 (20 + 2 * n) (downDistance n) t (waveValues ops input row warp n) s ht
      exact ⟨h.1.trans step.1, h.2.trans step.2⟩

theorem last_wave_other (p : Shape) (ops : Ops α) (row warp t : Nat) (values : Nat → α)
    (s : State α) (ht : t ∉ cohortThreads row warp 64) :
    (lastWave p ops row warp values s).pc t = s.pc t ∧
    (lastWave p ops row warp values s).regs t = s.regs t := by
  have h := last_fold_other ops (waveLeft p values) (waveRight p values) (cohortThreads row warp 64) t
    (LarkCollective.shuffleUpdates 2 (downSnapshot p row warp 64 1 values) s) ht
  have hs := down_shuffled_other p row warp 64 1 t values s ht
  exact ⟨h.1.trans hs.1, h.2.trans hs.2⟩

theorem first_wave_indices_eq (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp : Nat) (s : State α) :
    (firstWave p ops input row warp s).indices = (maxPrefixFold ops input (cohortThreads row warp 64) s).indices :=
  (last_wave_preserves p ops row warp (waveValues ops input row warp 4) _).1.trans
    (first_stages_preserves p ops input row warp 0 4 _).2.1

theorem first_wave_other (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp t : Nat) (s : State α) (ht : t ∉ cohortThreads row warp 64) :
    (firstWave p ops input row warp s).pc t = s.pc t ∧
    (firstWave p ops input row warp s).indices t = s.indices t ∧
    (firstWave p ops input row warp s).regs t = s.regs t := by
  have h0 := max_fold_other ops input (cohortThreads row warp 64) t s ht
  have h1 := first_stages_other p ops input row warp 0 4 t (maxPrefixFold ops input (cohortThreads row warp 64) s) ht
  have h2 := last_wave_other p ops row warp t (waveValues ops input row warp 4)
    (firstStages p ops input row warp 0 4 (maxPrefixFold ops input (cohortThreads row warp 64) s)) ht
  exact ⟨h2.1.trans (h1.1.trans h0.1),
    (congrFun (first_wave_indices_eq p ops input row warp s) t).trans h0.2.1,
    h2.2.trans (h1.2.trans h0.2.2)⟩

theorem last_wave_partial_frame (p : Shape) (ops : Ops α) (row warp : Nat)
    (values : Nat → α) (s : State α) (l : Location)
    (hp : ∀ t ∈ cohortThreads row warp 64, ¬ PartialWrites t l) :
    (lastWave p ops row warp values s).memory l = s.memory l :=
  last_fold_memory_other ops (waveLeft p values) (waveRight p values) (cohortThreads row warp 64)
    (LarkCollective.shuffleUpdates 2 (downSnapshot p row warp 64 1 values) s) l hp

theorem first_wave_partial_frame (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp : Nat) (s : State α) (l : Location)
    (hp : ∀ t ∈ cohortThreads row warp 64, ¬ PartialWrites t l) :
    (firstWave p ops input row warp s).memory l = s.memory l := by
  have h0 := congrFun (max_fold_frames ops input (cohortThreads row warp 64) s).1 l
  have h1 := (first_stages_preserves p ops input row warp 0 4
    (maxPrefixFold ops input (cohortThreads row warp 64) s)).1
  have h2 := last_wave_partial_frame p ops row warp (waveValues ops input row warp 4)
    (firstStages p ops input row warp 0 4 (maxPrefixFold ops input (cohortThreads row warp 64) s)) l hp
  exact h2.trans ((congrFun h1 l).trans h0)

theorem first_wave_partial_other (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp t : Nat) (s : State α) (l : Location)
    (ht : t ∉ cohortThreads row warp 64) (hp : PartialWrites t l) :
    (firstWave p ops input row warp s).memory l = s.memory l := by
  apply first_wave_partial_frame p ops input row warp s l
  intro u hu hpu
  have he := partial_writes_unique t u l hp hpu
  exact ht (he ▸ hu)

theorem last_wave_accumulator (p : Shape) (ops : Ops α) (row warp lane : Nat)
    (values : Nat → α) (s : State α) (hw : warp < 16) (hl : lane < 64) :
    (lastWave p ops row warp values s).regs (cohortBase row warp+lane) 0 =
      some (ops.max (values lane) (values (downPeer32 lane 1))) := by
  have h := (last_fold_member ops (waveLeft p values) (waveRight p values)
    (cohortThreads row warp 64) (LarkCollective.shuffleUpdates 2 (downSnapshot p row warp 64 1 values) s)
    (cohort_nodup row warp 64) _ ((cohort_mem row warp 64 _).mpr ⟨lane,hl,rfl⟩)).2
  simpa only [waveLeft,waveRight,(cohort_coords p row warp lane hw hl).2] using h

theorem first_wave_accumulator (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp lane : Nat) (s : State α) (hw : warp < 16) (hl : lane < 64) :
    (firstWave p ops input row warp s).regs (cohortBase row warp+lane) 0 =
      some (waveValues ops input row warp 5 lane) :=
  last_wave_accumulator p ops row warp lane (waveValues ops input row warp 4) _ hw hl

structure FirstDone (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) : Prop where
  pc : s.pc t = 32
  accumulator : s.regs t 0 = some (waveValues ops input (t/1024) (t%1024/64) 5 (t%1024%64))
  indices : MaxNativeIndices t s

theorem first_wave_done (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp : Nat) (s : State α) (hw : warp < 16)
    (reads : Reads p input s) (good : ∀ a ∈ s.trace, Good a)
    (t : Nat) (ht : t ∈ cohortThreads row warp 64) :
    FirstDone ops input t (firstWave p ops input row warp s) := by
  obtain ⟨lane,hl,rfl⟩ := (cohort_mem row warp 64 t).mp ht
  have coords := cohort_arithmetic row warp lane hw hl
  have hi := (native_prefix_ready p ops input row warp s reads good lane hl).indices
  exact {
    pc := first_wave_pc p ops input row warp s lane hl
    accumulator := by
      have h := first_wave_accumulator p ops input row warp lane s hw hl
      simpa only [coords.1,coords.2.1,show (warp*64+lane)/64=warp by omega,
        show (warp*64+lane)%64=lane by omega] using h
    indices := by simpa only [MaxNativeIndices,first_wave_indices_eq] using hi }

theorem first_done_other (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp t : Nat) (s : State α) (ht : t ∉ cohortThreads row warp 64)
    (done : FirstDone ops input t s) : FirstDone ops input t (firstWave p ops input row warp s) := by
  have h := first_wave_other p ops input row warp t s ht
  exact ⟨h.1.trans done.pc,(congrFun h.2.2 0).trans done.accumulator,
    by simpa only [MaxNativeIndices,h.2.1] using done.indices⟩

#print axioms last_wave_accumulator
#print axioms first_wave_accumulator
#print axioms first_wave_done
#print axioms first_done_other
#print axioms max_fold_other
#print axioms down_step_other
#print axioms first_stages_other
#print axioms last_wave_other
#print axioms first_wave_indices_eq
#print axioms first_wave_other
#print axioms first_wave_partial_frame
#print axioms first_wave_partial_other
#print axioms last_wave_partial_frame
end LarkNativeSoftmax
