import Lark.NativeSoftmaxSumSerialWave

/-! Compose actual serial-phase native waves. Old partials are retained only
while physical wave zero is pending; its result is preserved by every later wave. -/
namespace LarkNativeSoftmax
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

structure SumSerialWavesEntry (values : Nat → α) (row : Nat) (ws : List Nat) (s : State α) : Prop where
  pc : ∀ w ∈ ws, ∀ t ∈ cohortThreads row w 64, s.pc t=83
  native : ∀ w ∈ ws, ∀ t ∈ cohortThreads row w 64, MaxNativeIndices t s
  pending : 0 ∈ ws → SumSerialReads values (row*1024) s
  epoch : ∀ w ∈ ws, ∀ t ∈ cohortThreads row w 64, (s.epochs t).block=3
  good : ∀ a ∈ s.trace, Good a

theorem sum_serial_wave_entry (values : Nat → α) (row : Nat) (ws : List Nat) (s : State α)
    (entry : SumSerialWavesEntry values row ws s) (w : Nat) (hw : w ∈ ws) :
    SumSerialEntry values row (cohortThreads row w 64) s := by
  exact ⟨entry.pc w hw,entry.native w hw,by
    intro hm
    have hz := (sum_serial_cohort_leader row w).mp hm
    subst w
    exact entry.pending hw,entry.epoch w hw,entry.good⟩

theorem sum_serial_waves_entry_tail (ops : Ops α) (values : Nat → α) (row w : Nat) (ws : List Nat)
    (s : State α) (hn : w ∉ ws) (entry : SumSerialWavesEntry values row (w::ws) s) :
    SumSerialWavesEntry values row ws (sumSerialWave ops values row w s) := by
  exact {
    pc := by
      intro u hu t ht
      have hne : u ≠ w := by intro h; subst u; exact hn hu
      exact (sum_serial_fold_other ops values row _ t s (cohorts_disjoint row u w t hne ht)).trans
        (entry.pc u (by simp [hu]) t ht)
    native := by
      intro u hu t ht
      exact sum_serial_fold_native ops values row _ t s (entry.native u (by simp [hu]) t ht)
    pending := by
      intro hm slot hs
      have hw : w ≠ 0 := by intro h; subst w; exact hn hm
      rewrite [sum_serial_wave_no_leader ops values row w s hw]
      exact entry.pending (by simp [hm]) slot hs
    epoch := by
      intro u hu t ht
      exact (congrArg (fun epochs => (epochs t).block) (sum_serial_wave_epochs ops values row w s)).trans
        (entry.epoch u (by simp [hu]) t ht)
    good := sum_serial_fold_good ops values row _ s (cohort_nodup row w 64)
      (sum_serial_wave_entry values row (w::ws) s entry w (by simp)) }

def sumSerialWaves (ops : Ops α) (values : Nat → α) (row : Nat) (ws : List Nat) (s : State α) : State α :=
  ws.foldl (fun s w => sumSerialWave ops values row w s) s

theorem sum_serial_waves_run (p : Shape) (guarded : Bool) (ops : Ops α) (values : Nat → α)
    (row : Nat) (ws : List Nat) (s : State α) (hn : ws.Nodup) (hb : ∀ w ∈ ws, w<16)
    (entry : SumSerialWavesEntry values row ws s) :
    ws.foldlM (fun s w => LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel (program guarded)
      (warpThreads (geometry p) row w) fuel.warp s) s = some (sumSerialWaves ops values row ws s) := by
  induction ws generalizing s with
  | nil => rfl
  | cons w ws ih =>
    obtain ⟨hnot,htail⟩ := List.nodup_cons.mp hn
    rewrite [List.foldlM_cons,sum_serial_wave_run p guarded ops values row w s (hb w (by simp))
      (sum_serial_wave_entry values row (w::ws) s entry w (by simp))]
    simp only [bind,Option.some_bind]
    exact ih _ htail (by intro u hu; exact hb u (by simp [hu]))
      (sum_serial_waves_entry_tail ops values row w ws s hnot entry)

theorem sum_serial_waves_epochs (ops : Ops α) (values : Nat → α) (row : Nat) (ws : List Nat) (s : State α) :
    (sumSerialWaves ops values row ws s).epochs=s.epochs := by
  induction ws generalizing s with
  | nil => rfl
  | cons w ws ih => exact (ih (sumSerialWave ops values row w s)).trans (sum_serial_wave_epochs ops values row w s)

theorem sum_serial_waves_native (ops : Ops α) (values : Nat → α) (row : Nat) (ws : List Nat)
    (t : Nat) (s : State α) (hi : MaxNativeIndices t s) : MaxNativeIndices t (sumSerialWaves ops values row ws s) := by
  induction ws generalizing s with
  | nil => exact hi
  | cons w ws ih => exact ih _ (sum_serial_fold_native ops values row _ t s hi)

theorem sum_serial_waves_other (ops : Ops α) (values : Nat → α) (row : Nat) (ws : List Nat)
    (t : Nat) (s : State α) (ht : ∀ w ∈ ws, t ∉ cohortThreads row w 64) :
    (sumSerialWaves ops values row ws s).pc t=s.pc t := by
  induction ws generalizing s with
  | nil => rfl
  | cons w ws ih =>
    exact (ih (sumSerialWave ops values row w s) (by intro u hu; exact ht u (by simp [hu]))).trans
      (sum_serial_fold_other ops values row _ t s (ht w (by simp)))

theorem sum_serial_waves_member_pc (ops : Ops α) (values : Nat → α) (row : Nat) (ws : List Nat)
    (s : State α) (hn : ws.Nodup) (w t : Nat) (hw : w ∈ ws) (ht : t ∈ cohortThreads row w 64) :
    (sumSerialWaves ops values row ws s).pc t=92 := by
  induction ws generalizing s with
  | nil => simp at hw
  | cons u ws ih =>
    obtain ⟨hnot,htail⟩ := List.nodup_cons.mp hn
    rcases List.mem_cons.mp hw with he | hm
    · subst w
      exact (sum_serial_waves_other ops values row ws t (sumSerialWave ops values row u s) (by
        intro v hv
        exact cohorts_disjoint row u v t (by intro h; subst v; exact hnot hv) ht)).trans
        (sum_serial_fold_member_pc ops values row _ s (cohort_nodup row u 64) t ht)
    · exact ih (sumSerialWave ops values row u s) htail hm

theorem sum_serial_waves_memory_other (ops : Ops α) (values : Nat → α) (row : Nat) (ws : List Nat)
    (s : State α) (l : Location) (hl : l ≠ sumPartialCell (row*1024) 0) :
    (sumSerialWaves ops values row ws s).memory l=s.memory l := by
  induction ws generalizing s with
  | nil => rfl
  | cons w ws ih =>
    exact (ih (sumSerialWave ops values row w s)).trans (sum_serial_fold_memory_other ops values row _ s l hl)

theorem sum_serial_waves_preserves_value (ops : Ops α) (values : Nat → α) (row : Nat) (ws : List Nat) (s : State α)
    (hv : s.memory (sumPartialCell (row*1024) 0)=some (sumSerialTotal ops values)) :
    (sumSerialWaves ops values row ws s).memory (sumPartialCell (row*1024) 0)=some (sumSerialTotal ops values) := by
  induction ws generalizing s with
  | nil => exact hv
  | cons w ws ih => exact ih _ (sum_serial_fold_preserves_value ops values row _ s hv)

theorem sum_serial_waves_value (ops : Ops α) (values : Nat → α) (row : Nat) (ws : List Nat)
    (s : State α) (hm : 0 ∈ ws) :
    (sumSerialWaves ops values row ws s).memory (sumPartialCell (row*1024) 0)=some (sumSerialTotal ops values) := by
  induction ws generalizing s with
  | nil => simp at hm
  | cons w ws ih =>
    rcases List.mem_cons.mp hm with he | hm
    · subst w
      exact sum_serial_waves_preserves_value ops values row ws _
        (sum_serial_fold_value ops values row _ s ((sum_serial_cohort_leader row 0).mpr rfl))
    · exact ih (sumSerialWave ops values row w s) hm

theorem sum_serial_waves_trace_length (ops : Ops α) (values : Nat → α) (row : Nat) (ws : List Nat) (s : State α) :
    (sumSerialWaves ops values row ws s).trace.length=s.trace.length+33*(ws.countP (fun w => w==0)) := by
  induction ws generalizing s with
  | nil => simp [sumSerialWaves]
  | cons w ws ih =>
    change (sumSerialWaves ops values row ws (sumSerialWave ops values row w s)).trace.length = _
    rewrite [ih,sum_serial_wave_trace_length]
    simp only [List.countP_cons,beq_iff_eq]
    by_cases hw : w=0 <;> simp only [hw,↓reduceIte] <;> omega

theorem sum_serial_waves_good (ops : Ops α) (values : Nat → α) (row : Nat) (ws : List Nat)
    (s : State α) (hn : ws.Nodup) (entry : SumSerialWavesEntry values row ws s) :
    ∀ a ∈ (sumSerialWaves ops values row ws s).trace, Good a := by
  induction ws generalizing s with
  | nil => exact entry.good
  | cons w ws ih =>
    obtain ⟨hnot,htail⟩ := List.nodup_cons.mp hn
    exact ih _ htail (sum_serial_waves_entry_tail ops values row w ws s hnot entry)

#print axioms sum_serial_wave_entry
#print axioms sum_serial_waves_entry_tail
#print axioms sum_serial_waves_run
#print axioms sum_serial_waves_epochs
#print axioms sum_serial_waves_native
#print axioms sum_serial_waves_other
#print axioms sum_serial_waves_member_pc
#print axioms sum_serial_waves_memory_other
#print axioms sum_serial_waves_preserves_value
#print axioms sum_serial_waves_value
#print axioms sum_serial_waves_trace_length
#print axioms sum_serial_waves_good
end LarkNativeSoftmax
