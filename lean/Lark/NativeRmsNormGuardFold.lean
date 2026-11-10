import Lark.NativeRmsNormGuard

/-! Execute the actual scalar lane fold between two shuffle snapshots. -/
namespace LarkNativeRmsNorm
open LarkNonlinear
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem guarded_lane (p : Shape) (ops : Ops α) (t pc lane distance valid : Nat)
    (bound : Index) (a b : α) (s : State α) (hl : lane < 64) (hd : distance ≤ 32)
    (hi : s.indices t 2 = some (lane : Int)) (hv : evalIndex (geometry p) t s bound = some (valid : Int))
    (ha : s.regs t 0 = some a) (hb : s.regs t 1 = some b) (hp : s.pc t = pc + 1)
    (hbranch : program[pc + 1]? = some (.scalar (.branch
      (.lt (.add (.ivar 2) (.const (distance : Int))) bound) (pc + 3))))
    (hadd : program[pc + 2]? = some (.scalar (.assign 0 (.bin .add (.reg 0) (.reg 1)))))
    (cut : LarkCollective.Cut)
    (hcut : LarkCollective.parked program (guardedAfter ops t pc lane distance valid a b s) t = some cut) :
    LarkCollective.runLane ops (layout p) (geometry p) program t fuel.lane s =
      some (guardedAfter ops t pc lane distance valid a b s) := by
  by_cases h : lane + distance < valid
  · rewrite [show fuel.lane = 254 + 2 by decide,
      guarded_true_eq p ops t pc lane distance valid 254 bound a b s hl hd hi hv ha hb hp hbranch hadd h]
    change LarkCollective.runLane ops (layout p) (geometry p) program t (253 + 1) _ = _
    rewrite [LarkCollective.runLane, hcut]
    rfl
  · rewrite [show fuel.lane = 255 + 1 by decide,
      guarded_false_eq p ops t pc lane distance valid 255 bound a b s hl hd hi hv hp hbranch h]
    rewrite [LarkCollective.runLane, hcut]
    rfl

def guardedFold (ops : Ops α) (pc distance valid : Nat) (lane : Nat → Nat) (a b : Nat → α)
    (ts : List Nat) (s : State α) : State α :=
  ts.foldl (fun s t => guardedAfter ops t pc (lane t) distance valid (a t) (b t) s) s

theorem guarded_fold_preserves (ops : Ops α) (pc distance valid : Nat) (lane : Nat → Nat)
    (a b : Nat → α) (ts : List Nat) (s : State α) :
    (guardedFold ops pc distance valid lane a b ts s).indices = s.indices ∧
    (guardedFold ops pc distance valid lane a b ts s).memory = s.memory ∧
    (guardedFold ops pc distance valid lane a b ts s).epochs = s.epochs ∧
    (guardedFold ops pc distance valid lane a b ts s).trace = s.trace := by
  induction ts generalizing s with
  | nil => exact ⟨rfl, rfl, rfl, rfl⟩
  | cons t ts ih =>
      have h := ih (guardedAfter ops t pc (lane t) distance valid (a t) (b t) s)
      have h1 := guarded_preserves ops t pc (lane t) distance valid (a t) (b t) s
      exact ⟨h.1.trans h1.1, h.2.1.trans h1.2.1, h.2.2.1.trans h1.2.2.1, h.2.2.2.trans h1.2.2.2⟩

theorem guarded_fold_other (ops : Ops α) (pc distance valid : Nat) (lane : Nat → Nat)
    (a b : Nat → α) (ts : List Nat) (t : Nat) (s : State α) (ht : t ∉ ts) :
    (guardedFold ops pc distance valid lane a b ts s).pc t = s.pc t ∧
    (guardedFold ops pc distance valid lane a b ts s).regs t = s.regs t := by
  induction ts generalizing s with
  | nil => exact ⟨rfl, rfl⟩
  | cons u ts ih =>
      have hne : t ≠ u := by intro he; subst t; simp at ht
      have hn : t ∉ ts := by intro hm; exact ht (by simp [hm])
      have h := ih (guardedAfter ops u pc (lane u) distance valid (a u) (b u) s) hn
      have h1 := guarded_other ops u t pc (lane u) distance valid (a u) (b u) s hne
      exact ⟨h.1.trans h1.1, h.2.trans h1.2⟩

theorem guarded_fold_member (ops : Ops α) (pc distance valid : Nat) (lane : Nat → Nat)
    (a b : Nat → α) (ts : List Nat) (s : State α) (hn : ts.Nodup) (t : Nat)
    (ht : t ∈ ts) (ha : s.regs t 0 = some (a t)) :
    (guardedFold ops pc distance valid lane a b ts s).pc t = pc + 3 ∧
    (guardedFold ops pc distance valid lane a b ts s).regs t 0 =
      some (if lane t + distance < valid then ops.add (a t) (b t) else a t) := by
  induction ts generalizing s with
  | nil => simp at ht
  | cons u ts ih =>
      rcases List.nodup_cons.mp hn with ⟨hnot, hnodup⟩
      rcases List.mem_cons.mp ht with he | hm
      · subst t
        have h := guarded_fold_other ops pc distance valid lane a b ts u
          (guardedAfter ops u pc (lane u) distance valid (a u) (b u) s) hnot
        exact ⟨h.1.trans (guarded_pc ops u pc (lane u) distance valid (a u) (b u) s),
          (congrFun h.2 0).trans (guarded_acc ops u pc (lane u) distance valid (a u) (b u) s ha)⟩
      · have hne : t ≠ u := by intro he; subst t; exact hnot hm
        have hr := guarded_other ops u t pc (lane u) distance valid (a u) (b u) s hne
        exact ih (guardedAfter ops u pc (lane u) distance valid (a u) (b u) s) hnodup hm
          ((congrFun hr.2 0).trans ha)

theorem index_of_indices (g : Geometry) (t : Nat) (s u : State α) (e : Index)
    (hi : s.indices t = u.indices t) : evalIndex g t s e = evalIndex g t u e := by
  induction e <;> simp [evalIndex, hi, *]

/-- Fold the actual machine's lane calls; all peer registers still refer to the
same pre-shuffle snapshot because another lane's guarded update cannot alter them. -/
theorem guarded_fold_run (p : Shape) (ops : Ops α) (pc distance valid : Nat)
    (bound : Index) (lane : Nat → Nat) (a b : Nat → α) (ts : List Nat) (s : State α)
    (hn : ts.Nodup) (hd : distance ≤ 32)
    (hl : ∀ t ∈ ts, lane t < 64)
    (hi : ∀ t ∈ ts, s.indices t 2 = some (lane t : Int))
    (hv : ∀ t ∈ ts, evalIndex (geometry p) t s bound = some (valid : Int))
    (ha : ∀ t ∈ ts, s.regs t 0 = some (a t)) (hb : ∀ t ∈ ts, s.regs t 1 = some (b t))
    (hp : ∀ t ∈ ts, s.pc t = pc + 1)
    (hbranch : program[pc + 1]? = some (.scalar (.branch
      (.lt (.add (.ivar 2) (.const (distance : Int))) bound) (pc + 3))))
    (hadd : program[pc + 2]? = some (.scalar (.assign 0 (.bin .add (.reg 0) (.reg 1)))))
    (cut : LarkCollective.Cut)
    (hcut : ∀ (u : State α) t, u.pc t = pc + 3 → LarkCollective.parked program u t = some cut) :
    ts.foldlM (fun s t => LarkCollective.runLane ops (layout p) (geometry p) program t fuel.lane s) s =
      some (guardedFold ops pc distance valid lane a b ts s) := by
  induction ts generalizing s with
  | nil => rfl
  | cons t ts ih =>
      rcases List.nodup_cons.mp hn with ⟨hnot, hnodup⟩
      let next := guardedAfter ops t pc (lane t) distance valid (a t) (b t) s
      have hpres := guarded_preserves ops t pc (lane t) distance valid (a t) (b t) s
      have hother : ∀ u ∈ ts, next.pc u = s.pc u ∧ next.regs u = s.regs u := by
        intro u hu
        exact guarded_other ops t u pc (lane t) distance valid (a t) (b t) s
          (by intro he; subst u; exact hnot hu)
      rewrite [List.foldlM_cons, guarded_lane p ops t pc (lane t) distance valid bound (a t) (b t) s
        (hl t (by simp)) hd (hi t (by simp)) (hv t (by simp)) (ha t (by simp)) (hb t (by simp))
        (hp t (by simp)) hbranch hadd cut (hcut next t (guarded_pc ops t pc (lane t) distance valid (a t) (b t) s))]
      simp only [bind, Option.some_bind]
      apply ih next hnodup
      · intro u hu; exact hl u (by simp [hu])
      · intro u hu; exact (congrFun (congrFun hpres.1 u) 2).trans (hi u (by simp [hu]))
      · intro u hu
        exact (index_of_indices (geometry p) u next s bound (congrFun hpres.1 u)).trans (hv u (by simp [hu]))
      · intro u hu; exact (congrFun (hother u hu).2 0).trans (ha u (by simp [hu]))
      · intro u hu; exact (congrFun (hother u hu).2 1).trans (hb u (by simp [hu]))
      · intro u hu; exact (hother u hu).1.trans (hp u (by simp [hu]))

#print axioms guarded_lane
#print axioms guarded_fold_member
#print axioms guarded_fold_run
end LarkNativeRmsNorm
