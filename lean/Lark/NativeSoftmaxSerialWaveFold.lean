import Lark.NativeSoftmaxSerialWave

/-! Compose actual serial-phase native waves. Old partials are retained only
while physical wave zero is pending; its result is preserved by every later wave. -/
namespace LarkNativeSoftmax
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

structure SerialWavesEntry (values : Nat → α) (row : Nat) (ws : List Nat) (s : State α) : Prop where
  pc : ∀ w ∈ ws, ∀ t ∈ cohortThreads row w 64, s.pc t=33
  native : ∀ w ∈ ws, ∀ t ∈ cohortThreads row w 64, MaxNativeIndices t s
  pending : 0 ∈ ws → SerialReads values (row*1024) s
  epoch : ∀ w ∈ ws, ∀ t ∈ cohortThreads row w 64, (s.epochs t).block=1
  good : ∀ a ∈ s.trace, Good a

theorem serial_wave_entry (values : Nat → α) (row : Nat) (ws : List Nat) (s : State α)
    (entry : SerialWavesEntry values row ws s) (w : Nat) (hw : w ∈ ws) :
    SerialEntry values row (cohortThreads row w 64) s := by
  exact ⟨entry.pc w hw,entry.native w hw,by
    intro hm
    have hz := (serial_cohort_leader row w).mp hm
    subst w
    exact entry.pending hw,entry.epoch w hw,entry.good⟩

theorem serial_waves_entry_tail (ops : Ops α) (values : Nat → α) (row w : Nat) (ws : List Nat)
    (s : State α) (hn : w ∉ ws) (entry : SerialWavesEntry values row (w::ws) s) :
    SerialWavesEntry values row ws (serialWave ops values row w s) := by
  exact {
    pc := by
      intro u hu t ht
      have hne : u ≠ w := by intro h; subst u; exact hn hu
      exact (serial_fold_other ops values row _ t s (cohorts_disjoint row u w t hne ht)).trans
        (entry.pc u (by simp [hu]) t ht)
    native := by
      intro u hu t ht
      exact serial_fold_native ops values row _ t s (entry.native u (by simp [hu]) t ht)
    pending := by
      intro hm slot hs
      have hw : w ≠ 0 := by intro h; subst w; exact hn hm
      rewrite [serial_wave_no_leader ops values row w s hw]
      exact entry.pending (by simp [hm]) slot hs
    epoch := by
      intro u hu t ht
      exact (congrArg (fun epochs => (epochs t).block) (serial_wave_epochs ops values row w s)).trans
        (entry.epoch u (by simp [hu]) t ht)
    good := serial_fold_good ops values row _ s (cohort_nodup row w 64)
      (serial_wave_entry values row (w::ws) s entry w (by simp)) }

def serialWaves (ops : Ops α) (values : Nat → α) (row : Nat) (ws : List Nat) (s : State α) : State α :=
  ws.foldl (fun s w => serialWave ops values row w s) s

theorem serial_waves_run (p : Shape) (guarded : Bool) (ops : Ops α) (values : Nat → α)
    (row : Nat) (ws : List Nat) (s : State α) (hn : ws.Nodup) (hb : ∀ w ∈ ws, w<16)
    (entry : SerialWavesEntry values row ws s) :
    ws.foldlM (fun s w => LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel (program guarded)
      (warpThreads (geometry p) row w) fuel.warp s) s = some (serialWaves ops values row ws s) := by
  induction ws generalizing s with
  | nil => rfl
  | cons w ws ih =>
    obtain ⟨hnot,htail⟩ := List.nodup_cons.mp hn
    rewrite [List.foldlM_cons,serial_wave_run p guarded ops values row w s (hb w (by simp))
      (serial_wave_entry values row (w::ws) s entry w (by simp))]
    simp only [bind,Option.some_bind]
    exact ih _ htail (by intro u hu; exact hb u (by simp [hu]))
      (serial_waves_entry_tail ops values row w ws s hnot entry)

theorem serial_waves_epochs (ops : Ops α) (values : Nat → α) (row : Nat) (ws : List Nat) (s : State α) :
    (serialWaves ops values row ws s).epochs=s.epochs := by
  induction ws generalizing s with
  | nil => rfl
  | cons w ws ih => exact (ih (serialWave ops values row w s)).trans (serial_wave_epochs ops values row w s)

theorem serial_waves_native (ops : Ops α) (values : Nat → α) (row : Nat) (ws : List Nat)
    (t : Nat) (s : State α) (hi : MaxNativeIndices t s) : MaxNativeIndices t (serialWaves ops values row ws s) := by
  induction ws generalizing s with
  | nil => exact hi
  | cons w ws ih => exact ih _ (serial_fold_native ops values row _ t s hi)

theorem serial_waves_other (ops : Ops α) (values : Nat → α) (row : Nat) (ws : List Nat)
    (t : Nat) (s : State α) (ht : ∀ w ∈ ws, t ∉ cohortThreads row w 64) :
    (serialWaves ops values row ws s).pc t=s.pc t := by
  induction ws generalizing s with
  | nil => rfl
  | cons w ws ih =>
    exact (ih (serialWave ops values row w s) (by intro u hu; exact ht u (by simp [hu]))).trans
      (serial_fold_other ops values row _ t s (ht w (by simp)))

theorem serial_waves_member_pc (ops : Ops α) (values : Nat → α) (row : Nat) (ws : List Nat)
    (s : State α) (hn : ws.Nodup) (w t : Nat) (hw : w ∈ ws) (ht : t ∈ cohortThreads row w 64) :
    (serialWaves ops values row ws s).pc t=42 := by
  induction ws generalizing s with
  | nil => simp at hw
  | cons u ws ih =>
    obtain ⟨hnot,htail⟩ := List.nodup_cons.mp hn
    rcases List.mem_cons.mp hw with he | hm
    · subst w
      exact (serial_waves_other ops values row ws t (serialWave ops values row u s) (by
        intro v hv
        exact cohorts_disjoint row u v t (by intro h; subst v; exact hnot hv) ht)).trans
        (serial_fold_member_pc ops values row _ s (cohort_nodup row u 64) t ht)
    · exact ih (serialWave ops values row u s) htail hm

theorem serial_waves_memory_other (ops : Ops α) (values : Nat → α) (row : Nat) (ws : List Nat)
    (s : State α) (l : Location) (hl : l ≠ partialCell (row*1024) 0) :
    (serialWaves ops values row ws s).memory l=s.memory l := by
  induction ws generalizing s with
  | nil => rfl
  | cons w ws ih =>
    exact (ih (serialWave ops values row w s)).trans (serial_fold_memory_other ops values row _ s l hl)

theorem serial_waves_preserves_value (ops : Ops α) (values : Nat → α) (row : Nat) (ws : List Nat) (s : State α)
    (hv : s.memory (partialCell (row*1024) 0)=some (serialMaximum ops values)) :
    (serialWaves ops values row ws s).memory (partialCell (row*1024) 0)=some (serialMaximum ops values) := by
  induction ws generalizing s with
  | nil => exact hv
  | cons w ws ih => exact ih _ (serial_fold_preserves_value ops values row _ s hv)

theorem serial_waves_value (ops : Ops α) (values : Nat → α) (row : Nat) (ws : List Nat)
    (s : State α) (hm : 0 ∈ ws) :
    (serialWaves ops values row ws s).memory (partialCell (row*1024) 0)=some (serialMaximum ops values) := by
  induction ws generalizing s with
  | nil => simp at hm
  | cons w ws ih =>
    rcases List.mem_cons.mp hm with he | hm
    · subst w
      exact serial_waves_preserves_value ops values row ws _
        (serial_fold_value ops values row _ s ((serial_cohort_leader row 0).mpr rfl))
    · exact ih (serialWave ops values row w s) hm

theorem serial_waves_trace_length (ops : Ops α) (values : Nat → α) (row : Nat) (ws : List Nat) (s : State α) :
    (serialWaves ops values row ws s).trace.length=s.trace.length+33*(ws.countP (fun w => w==0)) := by
  induction ws generalizing s with
  | nil => simp [serialWaves]
  | cons w ws ih =>
    change (serialWaves ops values row ws (serialWave ops values row w s)).trace.length = _
    rewrite [ih,serial_wave_trace_length]
    simp only [List.countP_cons,beq_iff_eq]
    by_cases hw : w=0 <;> simp only [hw,↓reduceIte] <;> omega

theorem serial_waves_good (ops : Ops α) (values : Nat → α) (row : Nat) (ws : List Nat)
    (s : State α) (hn : ws.Nodup) (entry : SerialWavesEntry values row ws s) :
    ∀ a ∈ (serialWaves ops values row ws s).trace, Good a := by
  induction ws generalizing s with
  | nil => exact entry.good
  | cons w ws ih =>
    obtain ⟨hnot,htail⟩ := List.nodup_cons.mp hn
    exact ih _ htail (serial_waves_entry_tail ops values row w ws s hnot entry)

#print axioms serial_wave_entry
#print axioms serial_waves_entry_tail
#print axioms serial_waves_run
#print axioms serial_waves_epochs
#print axioms serial_waves_native
#print axioms serial_waves_other
#print axioms serial_waves_member_pc
#print axioms serial_waves_memory_other
#print axioms serial_waves_preserves_value
#print axioms serial_waves_value
#print axioms serial_waves_trace_length
#print axioms serial_waves_good
end LarkNativeSoftmax
