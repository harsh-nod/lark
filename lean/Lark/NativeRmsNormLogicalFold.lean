import Lark.NativeRmsNormLogicalLast

/-! Sequential final logical-stage lane calls and their scale-store frames. -/
namespace LarkNativeRmsNorm
open LarkNonlinear
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def logicalLastFold (ops : Ops α) (row : Nat) (tid lane : Nat → Nat) (a b : Nat → α)
    (ts : List Nat) (s : State α) : State α :=
  ts.foldl (fun s t => logicalLastAfter ops t row (tid t) (lane t) (a t) (b t) s) s

theorem logical_fold_preserves (ops : Ops α) (row : Nat) (tid lane : Nat → Nat) (a b : Nat → α)
    (ts : List Nat) (s : State α) :
    (logicalLastFold ops row tid lane a b ts s).indices = s.indices ∧
    (logicalLastFold ops row tid lane a b ts s).epochs = s.epochs := by
  induction ts generalizing s with
  | nil => exact ⟨rfl, rfl⟩
  | cons t ts ih =>
      have h := ih (logicalLastAfter ops t row (tid t) (lane t) (a t) (b t) s)
      have h1 := logical_last_fields ops t row (tid t) (lane t) (a t) (b t) s
      exact ⟨h.1.trans h1.2.1, h.2.trans h1.2.2⟩

theorem logical_fold_other (ops : Ops α) (row : Nat) (tid lane : Nat → Nat) (a b : Nat → α)
    (ts : List Nat) (t : Nat) (s : State α) (ht : t ∉ ts) :
    (logicalLastFold ops row tid lane a b ts s).pc t = s.pc t ∧
    (logicalLastFold ops row tid lane a b ts s).regs t = s.regs t := by
  induction ts generalizing s with
  | nil => exact ⟨rfl, rfl⟩
  | cons u ts ih =>
      have hne : t ≠ u := by intro he; subst t; simp at ht
      have hn : t ∉ ts := by intro hm; exact ht (by simp [hm])
      have h := ih (logicalLastAfter ops u row (tid u) (lane u) (a u) (b u) s) hn
      have h1 := logical_last_other ops u t row (tid u) (lane u) (a u) (b u) s hne
      exact ⟨h.1.trans h1.1, h.2.trans h1.2⟩

theorem logical_fold_pc (ops : Ops α) (row : Nat) (tid lane : Nat → Nat) (a b : Nat → α)
    (ts : List Nat) (s : State α) (hn : ts.Nodup) (t : Nat) (ht : t ∈ ts) :
    (logicalLastFold ops row tid lane a b ts s).pc t = 55 := by
  induction ts generalizing s with
  | nil => simp at ht
  | cons u ts ih =>
      rcases List.nodup_cons.mp hn with ⟨hnot, hnodup⟩
      rcases List.mem_cons.mp ht with he | hm
      · subst t
        exact (logical_fold_other ops row tid lane a b ts u
          (logicalLastAfter ops u row (tid u) (lane u) (a u) (b u) s) hnot).1.trans
          (logical_last_fields ops u row (tid u) (lane u) (a u) (b u) s).1
      · exact ih (logicalLastAfter ops u row (tid u) (lane u) (a u) (b u) s) hnodup hm

theorem logical_fold_run (p : Shape) (ops : Ops α) (row : Nat) (tid lane : Nat → Nat) (a b : Nat → α)
    (ts : List Nat) (s : State α) (hn : ts.Nodup)
    (hr : ∀ t ∈ ts, t / 1024 = row) (hl : ∀ t ∈ ts, lane t < 16)
    (hi1 : ∀ t ∈ ts, s.indices t 1 = some (tid t : Int))
    (hi2 : ∀ t ∈ ts, s.indices t 2 = some (lane t : Int))
    (ha : ∀ t ∈ ts, s.regs t 0 = some (a t)) (hb : ∀ t ∈ ts, s.regs t 1 = some (b t))
    (hp : ∀ t ∈ ts, s.pc t = 51) :
    ts.foldlM (fun s t => LarkCollective.runLane ops (layout p) (geometry p) program t fuel.lane s) s =
      some (logicalLastFold ops row tid lane a b ts s) := by
  induction ts generalizing s with
  | nil => rfl
  | cons t ts ih =>
      rcases List.nodup_cons.mp hn with ⟨hnot, hnodup⟩
      let next := logicalLastAfter ops t row (tid t) (lane t) (a t) (b t) s
      have hpres := logical_last_fields ops t row (tid t) (lane t) (a t) (b t) s
      have hother : ∀ u ∈ ts, next.pc u = s.pc u ∧ next.regs u = s.regs u := by
        intro u hu
        exact logical_last_other ops t u row (tid t) (lane t) (a t) (b t) s
          (by intro he; subst u; exact hnot hu)
      rewrite [List.foldlM_cons, logical_last_lane p ops t row (tid t) (lane t) (a t) (b t) s
        (hr t (by simp)) (hl t (by simp)) (hi1 t (by simp)) (hi2 t (by simp))
        (ha t (by simp)) (hb t (by simp)) (hp t (by simp))]
      simp only [bind, Option.some_bind]
      apply ih next hnodup
      · intro u hu; exact hr u (by simp [hu])
      · intro u hu; exact hl u (by simp [hu])
      · intro u hu; exact (congrFun (congrFun hpres.2.1 u) 1).trans (hi1 u (by simp [hu]))
      · intro u hu; exact (congrFun (congrFun hpres.2.1 u) 2).trans (hi2 u (by simp [hu]))
      · intro u hu; exact (congrFun (hother u hu).2 0).trans (ha u (by simp [hu]))
      · intro u hu; exact (congrFun (hother u hu).2 1).trans (hb u (by simp [hu]))
      · intro u hu; exact (hother u hu).1.trans (hp u (by simp [hu]))

theorem logical_fold_memory_nonzero (ops : Ops α) (row : Nat) (tid lane : Nat → Nat) (a b : Nat → α)
    (ts : List Nat) (s : State α) (ht : ∀ t ∈ ts, tid t ≠ 0) :
    (logicalLastFold ops row tid lane a b ts s).memory = s.memory := by
  induction ts generalizing s with
  | nil => rfl
  | cons t ts ih =>
      exact (ih (logicalLastAfter ops t row (tid t) (lane t) (a t) (b t) s)
        (by intro u hu; exact ht u (by simp [hu]))).trans
        (logical_last_memory_nonzero ops t row (tid t) (lane t) (a t) (b t) s (ht t (by simp)))

theorem logical_fold_memory_other (ops : Ops α) (row : Nat) (tid lane : Nat → Nat) (a b : Nat → α)
    (ts : List Nat) (s : State α) (l : Location) (hl : l ≠ scaleSlot row) :
    (logicalLastFold ops row tid lane a b ts s).memory l = s.memory l := by
  induction ts generalizing s with
  | nil => rfl
  | cons t ts ih =>
      exact (ih (logicalLastAfter ops t row (tid t) (lane t) (a t) (b t) s)).trans
        (logical_last_memory_other ops t row (tid t) (lane t) (a t) (b t) s l hl)

theorem logical_fold_good (p : Shape) (ops : Ops α) (row : Nat) (tid lane : Nat → Nat) (a b : Nat → α)
    (ts : List Nat) (s : State α) (hr : ∀ t ∈ ts, t / 1024 = row)
    (ht : ∀ t ∈ ts, tid t = t % 1024) (he : ∀ t ∈ ts, (s.epochs t).block = 1)
    (good : ∀ access ∈ s.trace, LarkReductionFootprint.Good (traversal p) 0 access) :
    ∀ access ∈ (logicalLastFold ops row tid lane a b ts s).trace,
      LarkReductionFootprint.Good (traversal p) 0 access := by
  induction ts generalizing s with
  | nil => exact good
  | cons t ts ih =>
      have hp := (logical_last_fields ops t row (tid t) (lane t) (a t) (b t) s).2.2
      apply ih (logicalLastAfter ops t row (tid t) (lane t) (a t) (b t) s)
        (by intro u hu; exact hr u (by simp [hu])) (by intro u hu; exact ht u (by simp [hu]))
      · intro u hu
        exact (congrArg (fun epochs => (epochs u).block) hp).trans (he u (by simp [hu]))
      · exact logical_last_good p ops t row (tid t) (lane t) (a t) (b t) s
          (hr t (by simp)) (ht t (by simp)) (he t (by simp)) good

#print axioms logical_fold_run
#print axioms logical_fold_pc
#print axioms logical_fold_good
end LarkNativeRmsNorm
