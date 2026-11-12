import Lark.NativeSglangRmsNormWaveSecond

/-! Values and frames for the second reduction's completed native wave.
The exact read/write trace remains attached to the arbitrary incoming trace.
-/
namespace LarkNativeSglangRmsNorm
open LarkNonlinear LarkCollective
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
attribute [local irreducible] prefixFold reductionSnapshot partialFold firstBlockFold secondFold regAddFold inverseFold secondSnapshot

theorem wave_second_snapshot_preserves (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) :
    (waveSecondSnapshot p ops input row s).memory=s.memory ∧
    (waveSecondSnapshot p ops input row s).indices=s.indices ∧
    (waveSecondSnapshot p ops input row s).epochs=s.epochs ∧
    (waveSecondSnapshot p ops input row s).trace=(secondPrepared ops input row s).trace := by
  have h := second_snapshot_preserves p ops row 4 (blockPartialValue ops input row) (secondPrepared ops input row s)
  have hs := second_fold_preserves ops input (cohortThreads row 0 64) s
  exact ⟨h.1.trans hs.1,h.2.1.trans hs.2.1,h.2.2.1.trans hs.2.2,h.2.2.2⟩

theorem wave_second_indices_epochs (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) :
    (waveSecond p ops input row s).indices=s.indices ∧ (waveSecond p ops input row s).epochs=s.epochs := by
  have h := inverse_fold_indices_epochs ops (waveSecondA p ops input row) (waveSecondB p ops input row)
    (cohortThreads row 0 32) (waveSecondSnapshot p ops input row s)
  have hs := wave_second_snapshot_preserves p ops input row s
  exact ⟨h.1.trans hs.2.1,h.2.trans hs.2.2.1⟩

theorem wave_second_all_pc (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) :
    ∀ t∈cohortThreads row 0 64,(waveSecond p ops input row s).pc t=76 :=
  inverse_full_pc ops _ _ row (waveSecondSnapshot p ops input row s)
    (fun lane hl => wave_second_snapshot_inactive p ops input row lane s hl)

theorem wave_second_other (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row t : Nat) (s : State α) (ht : t∉cohortThreads row 0 64) :
    (waveSecond p ops input row s).pc t=s.pc t ∧ (waveSecond p ops input row s).regs t=s.regs t := by
  have ha : t∉cohortThreads row 0 32 := by
    intro hm
    rw [cohort_split] at ht
    exact ht (List.mem_append_left _ hm)
  have h := inverse_fold_other ops (waveSecondA p ops input row) (waveSecondB p ops input row)
    (cohortThreads row 0 32) t (waveSecondSnapshot p ops input row s) ha
  have hx := second_snapshot_other p ops row 4 t (blockPartialValue ops input row) (secondPrepared ops input row s) ha
  have hs := second_fold_other ops input (cohortThreads row 0 64) t s ht
  exact ⟨h.1.trans (hx.1.trans hs.1),h.2.trans (hx.2.trans hs.2)⟩

theorem wave_second_memory (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) (l : Location)
    (outside : ∀ t∈cohortThreads row 0 32,l≠partialSlot t (t%1024)) :
    (waveSecond p ops input row s).memory l=s.memory l := by
  change (inverseFold ops _ _ _ _).memory l=_
  rw [inverse_fold_memory ops _ _ _ _ l outside]
  rw [(wave_second_snapshot_preserves p ops input row s).1]

theorem wave_second_outside_shared (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) (l : Location) (hl : l.space≠.shared) :
    (waveSecond p ops input row s).memory l=s.memory l := by
  apply wave_second_memory
  intro t _ he
  exact hl (congrArg Location.space he)

def blockInverseValue (ops : Ops α) (input : Nat → Nat → α) (row lane : Nat) : α :=
  secondInverseValue ops (reductionValues ops (blockPartialValue ops input row) 5 lane)

theorem inverse_slots_injective (u v : Nat)
    (he : partialSlot u (u%1024)=partialSlot v (v%1024)) : u=v := by
  have ho := congrArg Location.owner he
  have hi := congrArg Location.offset he
  change u/1024=v/1024 at ho
  change u%1024=v%1024 at hi
  omega

theorem wave_second_shared_value (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row lane : Nat) (s : State α) (hl : lane<32) :
    (waveSecond p ops input row s).memory ⟨.shared,row,0,lane⟩=some (blockInverseValue ops input row lane) := by
  have hc := cohort_arithmetic row 0 lane (by decide) (by omega)
  have h := inverse_fold_written_value ops (waveSecondA p ops input row) (waveSecondB p ops input row)
    (cohortThreads row 0 32) (waveSecondSnapshot p ops input row s) (cohort_nodup row 0 32)
    (fun u _ v _ he => inverse_slots_injective u v he) _ ((cohort_mem row 0 32 _).mpr ⟨lane,hl,rfl⟩)
  have hm : (cohortBase row 0+lane)%1024=lane := by simpa only [Nat.zero_mul,Nat.zero_add] using hc.2.1
  simpa only [waveSecond,partialSlot,hc.1,hm,waveSecondA,waveSecondB,
    (cohort_coords p row 0 lane (by decide) (by omega)).2,blockInverseValue] using h

theorem wave_second_trace (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) :
    (waveSecond p ops input row s).trace=
      inverseEvents s.epochs (cohortThreads row 0 32) ++ secondEvents s.epochs (cohortThreads row 0 64) ++ s.trace := by
  change (inverseFold ops _ _ _ _).trace=_
  rw [inverse_fold_trace,(wave_second_snapshot_preserves p ops input row s).2.2.1,
    (wave_second_snapshot_preserves p ops input row s).2.2.2]
  change inverseEvents s.epochs (cohortThreads row 0 32) ++ (secondFold ops input _ s).trace=_
  rw [second_fold_trace]
  simp only [List.append_assoc]

theorem wave_second_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) (epochs : ∀ t∈cohortThreads row 0 64,(s.epochs t).block=1)
    (good : ∀ event∈s.trace,Good event) :
    ∀ event∈(waveSecond p ops input row s).trace,Good event := by
  apply inverse_fold_good
  · intro t ht
    rw [(wave_second_snapshot_preserves p ops input row s).2.2.1]
    exact epochs t (by rw [cohort_split]; exact List.mem_append_left _ ht)
  · rw [(wave_second_snapshot_preserves p ops input row s).2.2.2]
    exact second_fold_good ops input (cohortThreads row 0 64) s epochs good

#print axioms wave_second_snapshot_preserves
#print axioms wave_second_indices_epochs
#print axioms wave_second_all_pc
#print axioms wave_second_other
#print axioms wave_second_memory
#print axioms wave_second_outside_shared
#print axioms inverse_slots_injective
#print axioms wave_second_shared_value
#print axioms wave_second_trace
#print axioms wave_second_good
end LarkNativeSglangRmsNorm
