import Lark.NativeFlashInferRmsNormTopPartial

/-! Sequential final block-reduction tails. Only tid zero writes the final
shared total, and its value survives every later lane visit.
-/
namespace LarkNativeFlashInferRmsNorm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def TopWrites (t : Nat) (l : Location) : Prop :=
  t % 1024 = 0 ∧ l = topCell t

theorem top_writes_unique (t u : Nat) (l : Location)
    (ht : TopWrites t l) (hu : TopWrites u l) : t = u := by
  have he := ht.2.symm.trans hu.2
  have ho := congrArg Location.owner he
  change t / 1024 = u / 1024 at ho
  have ht := ht.1
  have hu := hu.1
  omega

theorem second_last_memory_other (ops : Ops α) (t : Nat) (a b : α) (s : State α)
    (l : Location) (hl : ¬ TopWrites t l) :
    (secondLastAfter ops t a b s).memory l = s.memory l := by
  by_cases hz : t % 1024 = 0
  · have hn : l ≠ topCell t := by intro he; exact hl ⟨hz, he⟩
    exact top_memory_other t _ _ _ l hn
  · simp only [secondLastAfter, topAfter, hz, ↓reduceIte, advance, addAfter, LarkReduction.setReg]

theorem second_last_value (ops : Ops α) (t : Nat) (a b : α) (s : State α)
    (ht : t % 1024 = 0) :
    (secondLastAfter ops t a b s).memory (topCell t) = some (ops.add a b) := by
  simpa only [secondLastAfter, ht] using
    top_value t (ops.add a b) (addAfter ops t 43 a b s)

def topFold (ops : Ops α) (a b : Nat → α) (ts : List Nat) (s : State α) : State α :=
  ts.foldl (fun s t => secondLastAfter ops t (a t) (b t) s) s

theorem top_fold_other (ops : Ops α) (a b : Nat → α) (ts : List Nat)
    (t : Nat) (s : State α) (ht : t ∉ ts) :
    (topFold ops a b ts s).pc t = s.pc t ∧ (topFold ops a b ts s).regs t = s.regs t := by
  induction ts generalizing s with
  | nil => exact ⟨rfl, rfl⟩
  | cons u ts ih =>
      have hne : t ≠ u := by intro he; subst t; simp at ht
      have hn : t ∉ ts := by intro hm; exact ht (by simp [hm])
      have h := ih (secondLastAfter ops u (a u) (b u) s) hn
      have h1 := second_last_other ops u t (a u) (b u) s hne
      exact ⟨h.1.trans h1.1, h.2.trans h1.2⟩

theorem top_fold_preserves (ops : Ops α) (a b : Nat → α) (ts : List Nat) (s : State α) :
    (topFold ops a b ts s).indices = s.indices ∧ (topFold ops a b ts s).epochs = s.epochs := by
  induction ts generalizing s with
  | nil => exact ⟨rfl, rfl⟩
  | cons t ts ih =>
      have h := ih (secondLastAfter ops t (a t) (b t) s)
      have h1 := second_last_fields ops t (a t) (b t) s
      exact ⟨h.1.trans h1.2.2.1, h.2.trans h1.2.2.2⟩

theorem top_fold_memory_other (ops : Ops α) (a b : Nat → α) (ts : List Nat)
    (s : State α) (l : Location) (hl : ∀ t ∈ ts, ¬ TopWrites t l) :
    (topFold ops a b ts s).memory l = s.memory l := by
  induction ts generalizing s with
  | nil => rfl
  | cons t ts ih =>
      exact (ih (secondLastAfter ops t (a t) (b t) s) (by intro u hu; exact hl u (by simp [hu]))).trans
        (second_last_memory_other ops t (a t) (b t) s l (hl t (by simp)))

theorem top_fold_member (ops : Ops α) (a b : Nat → α) (ts : List Nat) (s : State α)
    (hn : ts.Nodup) (t : Nat) (ht : t ∈ ts) :
    (topFold ops a b ts s).pc t = 46 ∧
    (topFold ops a b ts s).regs t 0 = some (ops.add (a t) (b t)) := by
  induction ts generalizing s with
  | nil => simp at ht
  | cons u ts ih =>
      obtain ⟨hnot, hnodup⟩ := List.nodup_cons.mp hn
      rcases List.mem_cons.mp ht with he | hm
      · subst t
        have h := top_fold_other ops a b ts u (secondLastAfter ops u (a u) (b u) s) hnot
        have h1 := second_last_fields ops u (a u) (b u) s
        exact ⟨h.1.trans h1.1, (congrFun h.2 0).trans h1.2.1⟩
      · exact ih (secondLastAfter ops u (a u) (b u) s) hnodup hm

theorem top_fold_value (ops : Ops α) (a b : Nat → α) (ts : List Nat) (s : State α)
    (hn : ts.Nodup) (t : Nat) (ht : t ∈ ts) (hz : t % 1024 = 0) :
    (topFold ops a b ts s).memory (topCell t) = some (ops.add (a t) (b t)) := by
  induction ts generalizing s with
  | nil => simp at ht
  | cons u ts ih =>
      obtain ⟨hnot, hnodup⟩ := List.nodup_cons.mp hn
      rcases List.mem_cons.mp ht with he | hm
      · subst t
        have hno : ∀ v ∈ ts, ¬ TopWrites v (topCell u) := by
          intro v hv hw
          have eq := top_writes_unique u v _ ⟨hz, rfl⟩ hw
          exact hnot (eq ▸ hv)
        exact (top_fold_memory_other ops a b ts (secondLastAfter ops u (a u) (b u) s) _ hno).trans
          (second_last_value ops u (a u) (b u) s hz)
      · exact ih (secondLastAfter ops u (a u) (b u) s) hnodup hm

theorem top_fold_good (ops : Ops α) (a b : Nat → α) (ts : List Nat) (s : State α)
    (he : ∀ t ∈ ts, (s.epochs t).block = 1) (good : ∀ access ∈ s.trace, Good access) :
    ∀ access ∈ (topFold ops a b ts s).trace, Good access := by
  induction ts generalizing s with
  | nil => exact good
  | cons t ts ih =>
      have hp := second_last_fields ops t (a t) (b t) s
      apply ih (secondLastAfter ops t (a t) (b t) s)
      · intro u hu
        exact (congrArg (fun epochs => (epochs u).block) hp.2.2.2).trans (he u (by simp [hu]))
      · exact second_last_good ops t (a t) (b t) s (he t (by simp)) good

theorem top_fold_run (p : Shape) (ops : Ops α) (a b : Nat → α) (ts : List Nat)
    (s : State α) (hn : ts.Nodup) (hi : ∀ t ∈ ts, NativeIndices t s)
    (hp : ∀ t ∈ ts, s.pc t = 43) (ha : ∀ t ∈ ts, s.regs t 0 = some (a t))
    (hb : ∀ t ∈ ts, s.regs t 1 = some (b t)) :
    ts.foldlM (fun s t => LarkCollective.runLane ops (layout p) (geometry p) program t fuel.lane s) s =
      some (topFold ops a b ts s) := by
  induction ts generalizing s with
  | nil => rfl
  | cons t ts ih =>
      obtain ⟨hnot, hnodup⟩ := List.nodup_cons.mp hn
      have hp1 := second_last_fields ops t (a t) (b t) s
      have hother : ∀ u ∈ ts, u ≠ t := by intro u hu he; subst u; exact hnot hu
      rewrite [List.foldlM_cons, second_last_lane p ops t (a t) (b t) s
        (hi t (by simp)) (ha t (by simp)) (hb t (by simp)) (hp t (by simp))]
      simp only [bind, Option.some_bind]
      apply ih (secondLastAfter ops t (a t) (b t) s) hnodup
      · intro u hu; simpa only [NativeIndices, hp1.2.2.1] using hi u (by simp [hu])
      · intro u hu
        exact (second_last_other ops t u (a t) (b t) s (hother u hu)).1.trans (hp u (by simp [hu]))
      · intro u hu
        exact (congrFun (second_last_other ops t u (a t) (b t) s (hother u hu)).2 0).trans (ha u (by simp [hu]))
      · intro u hu
        exact (congrFun (second_last_other ops t u (a t) (b t) s (hother u hu)).2 1).trans (hb u (by simp [hu]))

#print axioms top_writes_unique
#print axioms second_last_memory_other
#print axioms second_last_value
#print axioms top_fold_other
#print axioms top_fold_preserves
#print axioms top_fold_memory_other
#print axioms top_fold_member
#print axioms top_fold_value
#print axioms top_fold_good
#print axioms top_fold_run
end LarkNativeFlashInferRmsNorm
