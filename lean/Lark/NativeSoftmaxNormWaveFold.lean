import Lark.NativeSoftmaxNormWave

/-! Actual sequential fold of normalization waves. Earlier outputs and halt
controls survive later waves; pending waves retain their entry preconditions.
Both bound sources keep the original native64 scheduler and all fuel limits. -/
namespace LarkNativeSoftmax
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def NormWaveEntry (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ws : List Nat) (s : State α) : Prop :=
  ∀ w ∈ ws, NormCohortEntry p ops input row (cohortThreads row w 64) s

theorem norm_wave_entry_tail (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row w : Nat) (ws : List Nat) (s : State α) (hw : w<16) (hn : w ∉ ws) (hb : ∀ u ∈ ws, u<16)
    (entry : NormWaveEntry p ops input row (w::ws) s) :
    NormWaveEntry p ops input row ws (normWave guarded ops input row w s) := by
  intro u hu t ht
  have hne : u ≠ w := by intro he; subst u; exact hn hu
  exact norm_wave_entry_other p guarded ops input row w t s hw (cohorts_disjoint row u w t hne ht)
    (exp_cohort_row row u (hb u hu) t ht) (entry w (by simp)) (entry u (by simp [hu]) t ht)

def normWaveFold (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ws : List Nat) (s : State α) : State α := ws.foldl (fun s w => normWave guarded ops input row w s) s

theorem norm_wave_fold_run (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ws : List Nat) (s : State α) (hn : ws.Nodup) (hb : ∀ w ∈ ws, w<16)
    (entry : NormWaveEntry p ops input row ws s) :
    ws.foldlM (fun s w => LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel (program guarded)
      (warpThreads (geometry p) row w) fuel.warp s) s=some (normWaveFold guarded ops input row ws s) := by
  induction ws generalizing s with
  | nil => rfl
  | cons w ws ih =>
    obtain ⟨hnot,htail⟩ := List.nodup_cons.mp hn
    rewrite [List.foldlM_cons,norm_wave_run p guarded ops input row w s (hb w (by simp)) (entry w (by simp))]
    simp only [bind,Option.some_bind]
    exact ih _ htail (by intro u hu; exact hb u (by simp [hu]))
      (norm_wave_entry_tail p guarded ops input row w ws s (hb w (by simp)) hnot
        (by intro u hu; exact hb u (by simp [hu])) entry)

theorem norm_wave_fold_other (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ws : List Nat) (t : Nat) (s : State α) (hb : ∀ w ∈ ws, w<16)
    (ht : ∀ w ∈ ws, t ∉ cohortThreads row w 64) : OtherThread t t s (normWaveFold guarded ops input row ws s) := by
  induction ws generalizing s with
  | nil => exact ⟨rfl,rfl,rfl⟩
  | cons w ws ih =>
    exact other_thread_trans t t _ _ _ (norm_wave_other guarded ops input row w t s (hb w (by simp)) (ht w (by simp)))
      (ih _ (by intro u hu; exact hb u (by simp [hu])) (by intro u hu; exact ht u (by simp [hu])))

theorem norm_wave_fold_member_pc (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ws : List Nat) (s : State α) (hn : ws.Nodup) (hb : ∀ w ∈ ws, w<16)
    (w lane : Nat) (hw : w ∈ ws) (hl : lane<64) :
    (normWaveFold guarded ops input row ws s).pc (cohortBase row w+lane)=normPc guarded 115 := by
  induction ws generalizing s with
  | nil => simp at hw
  | cons u ws ih =>
    obtain ⟨hnot,htail⟩ := List.nodup_cons.mp hn
    have hbs : ∀ v ∈ ws, v<16 := by intro v hv; exact hb v (by simp [hv])
    rcases List.mem_cons.mp hw with he | hm
    · subst w
      have ht : ∀ v ∈ ws, cohortBase row u+lane ∉ cohortThreads row v 64 := by
        intro v hv
        apply cohorts_disjoint row u v _ (by intro he; subst v; exact hnot hv)
        exact (cohort_mem row u 64 _).mpr ⟨lane,hl,rfl⟩
      exact (norm_wave_fold_other guarded ops input row ws _ (normWave guarded ops input row u s) hbs ht).1.trans
        (norm_wave_pc guarded ops input row u lane s (hb u (by simp)) hl)
    · exact ih _ htail hbs hm

theorem norm_wave_fold_epochs (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ws : List Nat) (s : State α) : (normWaveFold guarded ops input row ws s).epochs=s.epochs := by
  induction ws generalizing s with
  | nil => rfl
  | cons w ws ih => exact (ih _).trans (norm_wave_epochs guarded ops input row w s)

theorem norm_wave_fold_output_other (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ws : List Nat) (offset : Nat) (s : State α) (hb : ∀ w ∈ ws, w<16)
    (ho : ∀ w ∈ ws, writer offset ∉ cohortThreads row w 64) :
    (normWaveFold guarded ops input row ws s).memory (globalCell 0 offset)=s.memory (globalCell 0 offset) := by
  induction ws generalizing s with
  | nil => rfl
  | cons w ws ih =>
    exact (ih _ (by intro u hu; exact hb u (by simp [hu])) (by intro u hu; exact ho u (by simp [hu]))).trans
      (norm_wave_output_other guarded ops input row w offset s (hb w (by simp)) (ho w (by simp)))

theorem norm_wave_fold_output_value (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ws : List Nat) (s : State α) (hn : ws.Nodup) (hb : ∀ w ∈ ws, w<16)
    (w t iteration component : Nat) (hw : w ∈ ws) (ht : t ∈ cohortThreads row w 64) (hi : iteration<7) (hc : component<8)
    (hcol : column (t%1024) iteration component<50257) :
    (normWaveFold guarded ops input row ws s).memory (globalCell 0 (address row (column (t%1024) iteration component)))=
      some (normOutputValue ops input row (column (t%1024) iteration component)) := by
  induction ws generalizing s with
  | nil => simp at hw
  | cons u ws ih =>
    obtain ⟨hnot,htail⟩ := List.nodup_cons.mp hn
    have hbs : ∀ v ∈ ws, v<16 := by intro v hv; exact hb v (by simp [hv])
    rcases List.mem_cons.mp hw with he | hm
    · subst w
      have hrow := exp_cohort_row row u (hb u (by simp)) t ht
      have he : row*1024+t%1024=t := by omega
      have ho : writer (address row (column (t%1024) iteration component))=t :=
        (address_writer row (t%1024) iteration component (Nat.mod_lt _ (by decide)) hcol).trans he
      exact (norm_wave_fold_output_other guarded ops input row ws _ (normWave guarded ops input row u s) hbs (by
        intro v hv; rewrite [ho]; exact cohorts_disjoint row u v t (by intro he; subst v; exact hnot hv) ht)).trans
        (norm_wave_output_value guarded ops input row u t iteration component s (hb u (by simp)) ht hi hc hcol)
    · exact ih _ htail hbs hm

theorem norm_wave_fold_fixed_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ws : List Nat) (s : State α) (hn : ws.Nodup) (hb : ∀ w ∈ ws, w<16)
    (entry : NormWaveEntry p ops input row ws s) (good : ∀ a ∈ s.trace, Good a) :
    ∀ a ∈ (normWaveFold true ops input row ws s).trace, Good a := by
  induction ws generalizing s with
  | nil => exact good
  | cons w ws ih =>
    obtain ⟨hnot,htail⟩ := List.nodup_cons.mp hn
    exact ih _ htail (by intro u hu; exact hb u (by simp [hu]))
      (norm_wave_entry_tail p true ops input row w ws s (hb w (by simp)) hnot (by intro u hu; exact hb u (by simp [hu])) entry)
      (norm_wave_fixed_good p ops input row w s (hb w (by simp)) (entry w (by simp)) good)

def normWaveFoldAccesses (guarded : Bool) (row : Nat) (ws : List Nat) : Nat :=
  (ws.map fun w => normScalarAccesses guarded (cohortThreads row w 64)).sum

theorem norm_wave_fold_trace_length (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ws : List Nat) (s : State α) :
    (normWaveFold guarded ops input row ws s).trace.length=s.trace.length+normWaveFoldAccesses guarded row ws := by
  induction ws generalizing s with
  | nil => simp [normWaveFold,normWaveFoldAccesses]
  | cons w ws ih =>
    change (normWaveFold guarded ops input row ws (normWave guarded ops input row w s)).trace.length=_
    rewrite [ih,norm_wave_trace_length]
    simp only [normWaveFoldAccesses,List.map_cons,List.sum_cons]
    omega

#print axioms norm_wave_entry_tail
#print axioms norm_wave_fold_run
#print axioms norm_wave_fold_other
#print axioms norm_wave_fold_member_pc
#print axioms norm_wave_fold_epochs
#print axioms norm_wave_fold_output_other
#print axioms norm_wave_fold_output_value
#print axioms norm_wave_fold_fixed_good
#print axioms norm_wave_fold_trace_length
end LarkNativeSoftmax
