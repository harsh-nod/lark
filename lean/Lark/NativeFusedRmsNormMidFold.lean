import Lark.NativeFusedRmsNormMidEntry

/-! Actual sequential entry fold for active lower32 and parked native threads.
Shared memory and synchronization epochs are retained across every lane call.
-/
namespace LarkNativeFusedRmsNorm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def midEntryFold (row : Nat) (values : Nat → α) (ts : List Nat) (s : State α) : State α :=
  ts.foldl (fun s t => midEntered t row (t % 1024) (values (t % 1024)) s) s

theorem mid_fold_preserves (row : Nat) (values : Nat → α) (ts : List Nat) (s : State α) :
    (midEntryFold row values ts s).memory = s.memory ∧
    (midEntryFold row values ts s).indices = s.indices ∧ (midEntryFold row values ts s).epochs = s.epochs := by
  induction ts generalizing s with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons t ts ih =>
      have h := ih (midEntered t row (t % 1024) (values (t % 1024)) s)
      have h1 := mid_entry_preserves t row (t % 1024) (values (t % 1024)) s
      exact ⟨h.1.trans h1.1, h.2.1.trans h1.2.1, h.2.2.trans h1.2.2⟩

theorem mid_fold_other (row : Nat) (values : Nat → α) (ts : List Nat) (t : Nat)
    (s : State α) (ht : t ∉ ts) :
    (midEntryFold row values ts s).pc t = s.pc t ∧ (midEntryFold row values ts s).regs t = s.regs t := by
  induction ts generalizing s with
  | nil => exact ⟨rfl, rfl⟩
  | cons u ts ih =>
      have hne : t ≠ u := by intro he; subst t; simp at ht
      have hn : t ∉ ts := by intro hm; exact ht (by simp [hm])
      have h := ih (midEntered u row (u % 1024) (values (u % 1024)) s) hn
      have h1 := mid_entry_other u t row (u % 1024) (values (u % 1024)) s hne
      exact ⟨h.1.trans h1.1, h.2.trans h1.2⟩

theorem mid_fold_pc (row : Nat) (values : Nat → α) (ts : List Nat) (s : State α)
    (hn : ts.Nodup) (t : Nat) (ht : t ∈ ts) :
    (midEntryFold row values ts s).pc t = if t % 1024 < 32 then 38 else 50 := by
  induction ts generalizing s with
  | nil => simp at ht
  | cons u ts ih =>
      obtain ⟨hnot, hnodup⟩ := List.nodup_cons.mp hn
      rcases List.mem_cons.mp ht with he | hm
      · subst t
        exact (mid_fold_other row values ts u (midEntered u row (u % 1024) (values (u % 1024)) s) hnot).1.trans
          (mid_entry_pc u row (u % 1024) (values (u % 1024)) s)
      · exact ih (midEntered u row (u % 1024) (values (u % 1024)) s) hnodup hm

theorem mid_fold_acc (row : Nat) (values : Nat → α) (ts : List Nat) (s : State α)
    (hn : ts.Nodup) (t : Nat) (ht : t ∈ ts) (ha : t % 1024 < 32) :
    (midEntryFold row values ts s).regs t 0 = some (values (t % 1024)) := by
  induction ts generalizing s with
  | nil => simp at ht
  | cons u ts ih =>
      obtain ⟨hnot, hnodup⟩ := List.nodup_cons.mp hn
      rcases List.mem_cons.mp ht with he | hm
      · subst t
        exact (congrFun (mid_fold_other row values ts u
          (midEntered u row (u % 1024) (values (u % 1024)) s) hnot).2 0).trans
          (mid_entry_acc u row (u % 1024) (values (u % 1024)) s ha)
      · exact ih (midEntered u row (u % 1024) (values (u % 1024)) s) hnodup hm

theorem mid_fold_run (p : Shape) (ops : Ops α) (row : Nat) (values : Nat → α)
    (ts : List Nat) (s : State α) (hn : ts.Nodup)
    (hr : ∀ t ∈ ts, t / 1024 = row) (hi : ∀ t ∈ ts, s.indices t 1 = some ((t % 1024 : Nat) : Int))
    (hx : ∀ t ∈ ts, t % 1024 < 32 → s.memory (partialSlot row (t % 1024)) = some (values (t % 1024)))
    (hp : ∀ t ∈ ts, s.pc t = 36) :
    ts.foldlM (fun s t => LarkCollective.runLane ops (layout p) (geometry p) program t fuel.lane s) s =
      some (midEntryFold row values ts s) := by
  induction ts generalizing s with
  | nil => rfl
  | cons t ts ih =>
      obtain ⟨hnot, hnodup⟩ := List.nodup_cons.mp hn
      let next := midEntered t row (t % 1024) (values (t % 1024)) s
      have hp1 := mid_entry_preserves t row (t % 1024) (values (t % 1024)) s
      rewrite [List.foldlM_cons, mid_entered_run p ops t row (t % 1024) (values (t % 1024)) s
        (hr t (by simp)) (hi t (by simp)) (hx t (by simp)) (hp t (by simp))]
      simp only [bind, Option.some_bind]
      apply ih next hnodup
      · intro u hu; exact hr u (by simp [hu])
      · intro u hu
        exact (congrFun (congrFun hp1.2.1 u) 1).trans (hi u (by simp [hu]))
      · intro u hu ha; exact (congrFun hp1.1 _).trans (hx u (by simp [hu]) ha)
      · intro u hu
        exact (mid_entry_other t u row (t % 1024) (values (t % 1024)) s
          (by intro he; subst u; exact hnot hu)).1.trans (hp u (by simp [hu]))

theorem mid_fold_good (row : Nat) (values : Nat → α) (ts : List Nat) (s : State α)
    (hr : ∀ t ∈ ts, t / 1024 = row) (he : ∀ t ∈ ts, (s.epochs t).block = 1)
    (good : ∀ a ∈ s.trace, Good a) : ∀ a ∈ (midEntryFold row values ts s).trace, Good a := by
  induction ts generalizing s with
  | nil => exact good
  | cons t ts ih =>
      have hp := (mid_entry_preserves t row (t % 1024) (values (t % 1024)) s).2.2
      apply ih (midEntered t row (t % 1024) (values (t % 1024)) s) (by intro u hu; exact hr u (by simp [hu]))
      · intro u hu
        exact (congrArg (fun epochs => (epochs u).block) hp).trans (he u (by simp [hu]))
      · exact mid_entry_good t row (t % 1024) (values (t % 1024)) s (hr t (by simp)) rfl (he t (by simp)) good

#print axioms mid_fold_run
#print axioms mid_fold_preserves
#print axioms mid_fold_pc
#print axioms mid_fold_acc
#print axioms mid_fold_other
#print axioms mid_fold_good
end LarkNativeFusedRmsNorm
