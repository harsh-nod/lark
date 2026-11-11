import Lark.NativeSoftmaxSumPartial

/-! Sequential final-lane tails, with one distinct partial writer per logical
group. A store by the second group preserves the first group's partial value.
-/
namespace LarkNativeSoftmax
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def SumPartialWrites (t : Nat) (l : Location) : Prop :=
  (t % 1024) % 32 = 0 ∧ l = sumPartialCell t ((t % 1024) / 32)

theorem sum_partial_writes_unique (t u : Nat) (l : Location)
    (ht : SumPartialWrites t l) (hu : SumPartialWrites u l) : t = u := by
  have he := ht.2.symm.trans hu.2
  have ho := congrArg Location.owner he
  have hi := congrArg Location.offset he
  change t / 1024 = u / 1024 at ho
  change t % 1024 / 32 = u % 1024 / 32 at hi
  have ht := ht.1
  have hu := hu.1
  omega

theorem sum_last_memory_other (ops : Ops α) (t : Nat) (a b : α) (s : State α)
    (l : Location) (hl : ¬ SumPartialWrites t l) :
    (sumLastAfter ops t a b s).memory l = s.memory l := by
  by_cases hz : (t % 1024) % 32 = 0
  · have hn : l ≠ sumPartialCell t ((t % 1024) / 32) := by intro he; exact hl ⟨hz, he⟩
    exact sum_partial_memory_other t _ _ _ _ l hn
  · simp only [sumLastAfter, sumPartialAfter, hz, ↓reduceIte, advance, sumCombineAfter, LarkReduction.setReg]

theorem sum_last_value (ops : Ops α) (t : Nat) (a b : α) (s : State α)
    (ht : (t % 1024) % 32 = 0) :
    (sumLastAfter ops t a b s).memory (sumPartialCell t ((t % 1024) / 32)) = some (ops.add a b) := by
  simpa only [sumLastAfter, ht] using
    sum_partial_value t ((t % 1024) / 32) (ops.add a b) (sumCombineAfter ops t 79 a b s)

def sumLastFold (ops : Ops α) (a b : Nat → α) (ts : List Nat) (s : State α) : State α :=
  ts.foldl (fun s t => sumLastAfter ops t (a t) (b t) s) s

theorem sum_last_fold_other (ops : Ops α) (a b : Nat → α) (ts : List Nat)
    (t : Nat) (s : State α) (ht : t ∉ ts) :
    (sumLastFold ops a b ts s).pc t = s.pc t ∧ (sumLastFold ops a b ts s).regs t = s.regs t := by
  induction ts generalizing s with
  | nil => exact ⟨rfl, rfl⟩
  | cons u ts ih =>
      have hne : t ≠ u := by intro he; subst t; simp at ht
      have hn : t ∉ ts := by intro hm; exact ht (by simp [hm])
      have h := ih (sumLastAfter ops u (a u) (b u) s) hn
      have h1 := sum_last_other ops u t (a u) (b u) s hne
      exact ⟨h.1.trans h1.1, h.2.trans h1.2⟩

theorem sum_last_fold_preserves (ops : Ops α) (a b : Nat → α) (ts : List Nat) (s : State α) :
    (sumLastFold ops a b ts s).indices = s.indices ∧ (sumLastFold ops a b ts s).epochs = s.epochs := by
  induction ts generalizing s with
  | nil => exact ⟨rfl, rfl⟩
  | cons t ts ih =>
      have h := ih (sumLastAfter ops t (a t) (b t) s)
      have h1 := sum_last_fields ops t (a t) (b t) s
      exact ⟨h.1.trans h1.2.2.1, h.2.trans h1.2.2.2⟩

theorem sum_last_fold_memory_other (ops : Ops α) (a b : Nat → α) (ts : List Nat)
    (s : State α) (l : Location) (hl : ∀ t ∈ ts, ¬ SumPartialWrites t l) :
    (sumLastFold ops a b ts s).memory l = s.memory l := by
  induction ts generalizing s with
  | nil => rfl
  | cons t ts ih =>
      exact (ih (sumLastAfter ops t (a t) (b t) s) (by intro u hu; exact hl u (by simp [hu]))).trans
        (sum_last_memory_other ops t (a t) (b t) s l (hl t (by simp)))

theorem sum_last_fold_member (ops : Ops α) (a b : Nat → α) (ts : List Nat) (s : State α)
    (hn : ts.Nodup) (t : Nat) (ht : t ∈ ts) :
    (sumLastFold ops a b ts s).pc t = 82 ∧
    (sumLastFold ops a b ts s).regs t 6 = some (ops.add (a t) (b t)) := by
  induction ts generalizing s with
  | nil => simp at ht
  | cons u ts ih =>
      obtain ⟨hnot, hnodup⟩ := List.nodup_cons.mp hn
      rcases List.mem_cons.mp ht with he | hm
      · subst t
        have h := sum_last_fold_other ops a b ts u (sumLastAfter ops u (a u) (b u) s) hnot
        have h1 := sum_last_fields ops u (a u) (b u) s
        exact ⟨h.1.trans h1.1, (congrFun h.2 6).trans h1.2.1⟩
      · exact ih (sumLastAfter ops u (a u) (b u) s) hnodup hm

theorem sum_last_fold_value (ops : Ops α) (a b : Nat → α) (ts : List Nat) (s : State α)
    (hn : ts.Nodup) (t : Nat) (ht : t ∈ ts) (hz : (t % 1024) % 32 = 0) :
    (sumLastFold ops a b ts s).memory (sumPartialCell t ((t % 1024) / 32)) = some (ops.add (a t) (b t)) := by
  induction ts generalizing s with
  | nil => simp at ht
  | cons u ts ih =>
      obtain ⟨hnot, hnodup⟩ := List.nodup_cons.mp hn
      rcases List.mem_cons.mp ht with he | hm
      · subst t
        have hno : ∀ v ∈ ts, ¬ SumPartialWrites v (sumPartialCell u ((u % 1024) / 32)) := by
          intro v hv hw
          have eq := sum_partial_writes_unique u v _ ⟨hz, rfl⟩ hw
          exact hnot (eq ▸ hv)
        exact (sum_last_fold_memory_other ops a b ts (sumLastAfter ops u (a u) (b u) s) _ hno).trans
          (sum_last_value ops u (a u) (b u) s hz)
      · exact ih (sumLastAfter ops u (a u) (b u) s) hnodup hm

theorem sum_last_fold_good (ops : Ops α) (a b : Nat → α) (ts : List Nat) (s : State α)
    (he : ∀ t ∈ ts, (s.epochs t).block = 2) (good : ∀ access ∈ s.trace, Good access) :
    ∀ access ∈ (sumLastFold ops a b ts s).trace, Good access := by
  induction ts generalizing s with
  | nil => exact good
  | cons t ts ih =>
      have hp := sum_last_fields ops t (a t) (b t) s
      apply ih (sumLastAfter ops t (a t) (b t) s)
      · intro u hu
        exact (congrArg (fun epochs => (epochs u).block) hp.2.2.2).trans (he u (by simp [hu]))
      · exact sum_last_good ops t (a t) (b t) s (he t (by simp)) good

theorem sum_last_fold_run (p : Shape) (guarded : Bool) (ops : Ops α) (a b : Nat → α) (ts : List Nat)
    (s : State α) (hn : ts.Nodup) (hi : ∀ t ∈ ts, MaxNativeIndices t s)
    (hp : ∀ t ∈ ts, s.pc t = 79) (ha : ∀ t ∈ ts, s.regs t 6 = some (a t))
    (hb : ∀ t ∈ ts, s.regs t 9 = some (b t)) :
    ts.foldlM (fun s t => LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t fuel.lane s) s =
      some (sumLastFold ops a b ts s) := by
  induction ts generalizing s with
  | nil => rfl
  | cons t ts ih =>
      obtain ⟨hnot, hnodup⟩ := List.nodup_cons.mp hn
      have hp1 := sum_last_fields ops t (a t) (b t) s
      have hother : ∀ u ∈ ts, u ≠ t := by intro u hu he; subst u; exact hnot hu
      rewrite [List.foldlM_cons, sum_last_lane p guarded ops t (a t) (b t) s
        (hi t (by simp)) (ha t (by simp)) (hb t (by simp)) (hp t (by simp))]
      simp only [bind, Option.some_bind]
      apply ih (sumLastAfter ops t (a t) (b t) s) hnodup
      · intro u hu; simpa only [MaxNativeIndices, hp1.2.2.1] using hi u (by simp [hu])
      · intro u hu
        exact (sum_last_other ops t u (a t) (b t) s (hother u hu)).1.trans (hp u (by simp [hu]))
      · intro u hu
        exact (congrFun (sum_last_other ops t u (a t) (b t) s (hother u hu)).2 6).trans (ha u (by simp [hu]))
      · intro u hu
        exact (congrFun (sum_last_other ops t u (a t) (b t) s (hother u hu)).2 9).trans (hb u (by simp [hu]))

#print axioms sum_partial_writes_unique
#print axioms sum_last_memory_other
#print axioms sum_last_value
#print axioms sum_last_fold_other
#print axioms sum_last_fold_preserves
#print axioms sum_last_fold_memory_other
#print axioms sum_last_fold_member
#print axioms sum_last_fold_value
#print axioms sum_last_fold_good
#print axioms sum_last_fold_run
end LarkNativeSoftmax
