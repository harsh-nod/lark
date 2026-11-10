import Lark.NativeRmsNormMidEntry

/-! Actual sequential scale-entry lane fold. Physical cohorts remain wave64;
only the first sixteen native threads load a shared partial.
-/
namespace LarkNativeRmsNorm
open LarkNonlinear
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def midEntryFold (row : Nat) (tid lane : Nat → Nat) (value : Nat → α) (ts : List Nat) (s : State α) : State α :=
  ts.foldl (fun s t => midEntered t row (tid t) (lane t) (value t) s) s

theorem mid_fold_preserves (row : Nat) (tid lane : Nat → Nat) (value : Nat → α) (ts : List Nat) (s : State α) :
    (midEntryFold row tid lane value ts s).memory = s.memory ∧
    (midEntryFold row tid lane value ts s).indices = s.indices ∧
    (midEntryFold row tid lane value ts s).epochs = s.epochs := by
  induction ts generalizing s with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons t ts ih =>
      have h := ih (midEntered t row (tid t) (lane t) (value t) s)
      have h1 := mid_entry_preserves t row (tid t) (lane t) (value t) s
      exact ⟨h.1.trans h1.1, h.2.1.trans h1.2.1, h.2.2.trans h1.2.2⟩

theorem mid_fold_other (row : Nat) (tid lane : Nat → Nat) (value : Nat → α) (ts : List Nat)
    (t : Nat) (s : State α) (ht : t ∉ ts) :
    (midEntryFold row tid lane value ts s).pc t = s.pc t ∧
    (midEntryFold row tid lane value ts s).regs t = s.regs t := by
  induction ts generalizing s with
  | nil => exact ⟨rfl, rfl⟩
  | cons u ts ih =>
      have hne : t ≠ u := by intro he; subst t; simp at ht
      have hn : t ∉ ts := by intro hm; exact ht (by simp [hm])
      have h := ih (midEntered u row (tid u) (lane u) (value u) s) hn
      have h1 := mid_entry_other u t row (tid u) (lane u) (value u) s hne
      exact ⟨h.1.trans h1.1, h.2.trans h1.2⟩

theorem mid_fold_pc (row : Nat) (tid lane : Nat → Nat) (value : Nat → α) (ts : List Nat)
    (s : State α) (hn : ts.Nodup) (t : Nat) (ht : t ∈ ts) :
    (midEntryFold row tid lane value ts s).pc t = if tid t < 16 then 41 else 55 := by
  induction ts generalizing s with
  | nil => simp at ht
  | cons u ts ih =>
      rcases List.nodup_cons.mp hn with ⟨hnot, hnodup⟩
      rcases List.mem_cons.mp ht with he | hm
      · subst t
        have h := (mid_fold_other row tid lane value ts u (midEntered u row (tid u) (lane u) (value u) s) hnot).1
        exact h.trans (mid_entry_pc u row (tid u) (lane u) (value u) s)
      · exact ih (midEntered u row (tid u) (lane u) (value u) s) hnodup hm

theorem mid_fold_acc (row : Nat) (tid lane : Nat → Nat) (value : Nat → α) (ts : List Nat)
    (s : State α) (hn : ts.Nodup) (t : Nat) (ht : t ∈ ts) (ha : tid t < 16) :
    (midEntryFold row tid lane value ts s).regs t 0 = some (value t) := by
  induction ts generalizing s with
  | nil => simp at ht
  | cons u ts ih =>
      rcases List.nodup_cons.mp hn with ⟨hnot, hnodup⟩
      rcases List.mem_cons.mp ht with he | hm
      · subst t
        have h := (mid_fold_other row tid lane value ts u (midEntered u row (tid u) (lane u) (value u) s) hnot).2
        exact (congrFun h 0).trans (mid_entry_acc u row (tid u) (lane u) (value u) s ha)
      · exact ih (midEntered u row (tid u) (lane u) (value u) s) hnodup hm

/-- Fold actual lane calls, including all parked inactive native threads. -/
theorem mid_fold_run (p : Shape) (ops : Ops α) (row : Nat) (tid lane : Nat → Nat) (value : Nat → α)
    (ts : List Nat) (s : State α) (hn : ts.Nodup)
    (hr : ∀ t ∈ ts, t / 1024 = row) (hl : ∀ t ∈ ts, tid t < 16 → lane t < 16)
    (hi1 : ∀ t ∈ ts, s.indices t 1 = some (tid t : Int))
    (hi2 : ∀ t ∈ ts, s.indices t 2 = some (lane t : Int))
    (hx : ∀ t ∈ ts, tid t < 16 → s.memory (partialSlot row (lane t)) = some (value t))
    (hp : ∀ t ∈ ts, s.pc t = 39) :
    ts.foldlM (fun s t => LarkCollective.runLane ops (layout p) (geometry p) program t fuel.lane s) s =
      some (midEntryFold row tid lane value ts s) := by
  induction ts generalizing s with
  | nil => rfl
  | cons t ts ih =>
      rcases List.nodup_cons.mp hn with ⟨hnot, hnodup⟩
      let next := midEntered t row (tid t) (lane t) (value t) s
      have hpres := mid_entry_preserves t row (tid t) (lane t) (value t) s
      have hother : ∀ u ∈ ts, next.pc u = s.pc u := by
        intro u hu
        exact (mid_entry_other t u row (tid t) (lane t) (value t) s
          (by intro he; subst u; exact hnot hu)).1
      rewrite [List.foldlM_cons, mid_entered_run p ops t row (tid t) (lane t) (value t) s
        (hr t (by simp)) (hl t (by simp)) (hi1 t (by simp)) (hi2 t (by simp)) (hx t (by simp)) (hp t (by simp))]
      simp only [bind, Option.some_bind]
      apply ih next hnodup
      · intro u hu; exact hr u (by simp [hu])
      · intro u hu; exact hl u (by simp [hu])
      · intro u hu; exact (congrFun (congrFun hpres.2.1 u) 1).trans (hi1 u (by simp [hu]))
      · intro u hu; exact (congrFun (congrFun hpres.2.1 u) 2).trans (hi2 u (by simp [hu]))
      · intro u hu ha; exact (congrFun hpres.1 _).trans (hx u (by simp [hu]) ha)
      · intro u hu; exact (hother u hu).trans (hp u (by simp [hu]))

theorem mid_fold_good (p : Shape) (row : Nat) (tid lane : Nat → Nat) (value : Nat → α)
    (ts : List Nat) (s : State α) (hr : ∀ t ∈ ts, t / 1024 = row)
    (he : ∀ t ∈ ts, (s.epochs t).block = 1)
    (good : ∀ access ∈ s.trace, LarkReductionFootprint.Good (traversal p) 0 access) :
    ∀ access ∈ (midEntryFold row tid lane value ts s).trace, LarkReductionFootprint.Good (traversal p) 0 access := by
  induction ts generalizing s with
  | nil => exact good
  | cons t ts ih =>
      have hp := (mid_entry_preserves t row (tid t) (lane t) (value t) s).2.2
      apply ih (midEntered t row (tid t) (lane t) (value t) s) (by intro u hu; exact hr u (by simp [hu]))
      · intro u hu
        exact (congrArg (fun epochs => (epochs u).block) hp).trans (he u (by simp [hu]))
      · exact mid_entry_good p t row (tid t) (lane t) (value t) s (hr t (by simp)) (he t (by simp)) good

#print axioms mid_fold_run
#print axioms mid_fold_acc
#print axioms mid_fold_good
end LarkNativeRmsNorm
