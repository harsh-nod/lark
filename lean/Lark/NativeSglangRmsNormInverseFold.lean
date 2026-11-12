import Lark.NativeSglangRmsNormSecondInverse

/-! Actual final-add/normalization/store fold for logical32. All shared writes,
their distinct locations, source-ordered values, and earlier trace remain.
-/
namespace LarkNativeSglangRmsNorm
open LarkNonlinear LarkCollective
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def inverseFold (ops : Ops α) (a b : Nat → α) (ts : List Nat) (s : State α) : State α :=
  ts.foldl (fun s t => inverseTail ops t (t%1024) (a t) (b t) s) s

theorem inverse_fold_cons (ops : Ops α) (a b : Nat → α) (t : Nat) (ts : List Nat) (s : State α) :
    inverseFold ops a b (t::ts) s=inverseFold ops a b ts (inverseTail ops t (t%1024) (a t) (b t) s) := rfl

theorem inverse_fold_indices_epochs (ops : Ops α) (a b : Nat → α) (ts : List Nat) (s : State α) :
    (inverseFold ops a b ts s).indices=s.indices ∧ (inverseFold ops a b ts s).epochs=s.epochs := by
  induction ts generalizing s with
  | nil => exact ⟨rfl,rfl⟩
  | cons t ts ih =>
      have h := ih (inverseTail ops t (t%1024) (a t) (b t) s)
      have hs := inverse_tail_fields ops t (t%1024) (a t) (b t) s
      exact ⟨h.1.trans hs.2.2.2.1,h.2.trans hs.2.2.2.2⟩

theorem inverse_fold_other (ops : Ops α) (a b : Nat → α) (ts : List Nat) (t : Nat)
    (s : State α) (ht : t∉ts) :
    (inverseFold ops a b ts s).pc t=s.pc t ∧ (inverseFold ops a b ts s).regs t=s.regs t := by
  induction ts generalizing s with
  | nil => exact ⟨rfl,rfl⟩
  | cons u ts ih =>
      have hne : t≠u := by intro he; subst t; simp at ht
      have hn : t∉ts := by intro hm; exact ht (by simp [hm])
      have h := ih (inverseTail ops u (u%1024) (a u) (b u) s) hn
      have hs := inverse_tail_other ops u (u%1024) t (a u) (b u) s hne
      exact ⟨h.1.trans hs.1,h.2.trans hs.2⟩

theorem inverse_fold_member (ops : Ops α) (a b : Nat → α) (ts : List Nat) (s : State α)
    (hn : ts.Nodup) (t : Nat) (ht : t∈ts) :
    (inverseFold ops a b ts s).pc t=76 ∧
    (inverseFold ops a b ts s).regs t 7=some (ops.add (a t) (b t)) ∧
    (inverseFold ops a b ts s).regs t 11=some (secondInverseValue ops (ops.add (a t) (b t))) := by
  induction ts generalizing s with
  | nil => simp at ht
  | cons u ts ih =>
      obtain ⟨hnot,hnodup⟩ := List.nodup_cons.mp hn
      rcases List.mem_cons.mp ht with he | hm
      · subst t
        have h := inverse_fold_other ops a b ts u (inverseTail ops u (u%1024) (a u) (b u) s) hnot
        have hs := inverse_tail_fields ops u (u%1024) (a u) (b u) s
        exact ⟨h.1.trans hs.1,(congrFun h.2 7).trans hs.2.1,(congrFun h.2 11).trans hs.2.2.1⟩
      · exact ih (inverseTail ops u (u%1024) (a u) (b u) s) hnodup hm

theorem inverse_fold_run (p : Shape) (ops : Ops α) (a b : Nat → α) (ts : List Nat) (s : State α)
    (hn : ts.Nodup) (bound : ∀ t∈ts,t%1024<32)
    (hi : ∀ t∈ts,s.indices t 1=some ((t%1024 : Nat) : Int))
    (hp : ∀ t∈ts,s.pc t=71) (ha : ∀ t∈ts,s.regs t 7=some (a t))
    (hb : ∀ t∈ts,s.regs t 8=some (b t)) :
    ts.foldlM (fun u t => LarkCollective.runLane ops (layout p) (geometry p) (program true) t fuel.lane u) s=
      some (inverseFold ops a b ts s) := by
  induction ts generalizing s with
  | nil => rfl
  | cons t ts ih =>
      obtain ⟨hnot,hnodup⟩ := List.nodup_cons.mp hn
      have hne : ∀ u∈ts,u≠t := by intro u hu he; subst u; exact hnot hu
      have lane : LarkCollective.runLane ops (layout p) (geometry p) (program true) t fuel.lane s=
          some (inverseTail ops t (t%1024) (a t) (b t) s) :=
        inverse_tail_lane p ops t (t%1024) 506 (a t) (b t) s (bound t (by simp))
          (hi t (by simp)) (hp t (by simp)) (ha t (by simp)) (hb t (by simp))
      rw [List.foldlM_cons,lane]
      apply ih (inverseTail ops t (t%1024) (a t) (b t) s) hnodup
      · intro u hu; exact bound u (by simp [hu])
      · intro u hu
        rw [(inverse_tail_fields ops t (t%1024) (a t) (b t) s).2.2.2.1]
        exact hi u (by simp [hu])
      · intro u hu
        exact (inverse_tail_other ops t (t%1024) u (a t) (b t) s (hne u hu)).1.trans (hp u (by simp [hu]))
      · intro u hu
        exact (congrFun (inverse_tail_other ops t (t%1024) u (a t) (b t) s (hne u hu)).2 7).trans (ha u (by simp [hu]))
      · intro u hu
        exact (congrFun (inverse_tail_other ops t (t%1024) u (a t) (b t) s (hne u hu)).2 8).trans (hb u (by simp [hu]))

theorem inverse_fold_memory (ops : Ops α) (a b : Nat → α) (ts : List Nat) (s : State α) (l : Location)
    (outside : ∀ t∈ts,l≠partialSlot t (t%1024)) :
    (inverseFold ops a b ts s).memory l=s.memory l := by
  induction ts generalizing s with
  | nil => rfl
  | cons t ts ih =>
      exact (ih (inverseTail ops t (t%1024) (a t) (b t) s) (fun u hu => outside u (by simp [hu]))).trans
        (inverse_tail_memory ops t (t%1024) (a t) (b t) s l (outside t (by simp)))

theorem inverse_fold_written_value (ops : Ops α) (a b : Nat → α) (ts : List Nat) (s : State α)
    (hn : ts.Nodup) (distinct : ∀ u∈ts,∀ v∈ts,partialSlot u (u%1024)=partialSlot v (v%1024) → u=v)
    (t : Nat) (ht : t∈ts) :
    (inverseFold ops a b ts s).memory (partialSlot t (t%1024))=
      some (secondInverseValue ops (ops.add (a t) (b t))) := by
  induction ts generalizing s with
  | nil => simp at ht
  | cons u ts ih =>
      obtain ⟨hnot,hnodup⟩ := List.nodup_cons.mp hn
      rcases List.mem_cons.mp ht with he | hm
      · subst t
        rw [inverse_fold_cons,inverse_fold_memory]
        · exact inverse_tail_written_value ops u (u%1024) (a u) (b u) s
        · intro v hv he
          have huv := distinct u (by simp) v (by simp [hv]) he
          exact hnot (huv ▸ hv)
      · rw [inverse_fold_cons]
        exact ih (inverseTail ops u (u%1024) (a u) (b u) s) hnodup
          (fun v hv w hw he => distinct v (by simp [hv]) w (by simp [hw]) he) hm

def inverseEvents (epochs : Nat → Epoch) : List Nat → List Access
  | [] => []
  | t::ts => inverseEvents epochs ts ++ [⟨t,partialSlot t (t%1024),true,epochs t⟩]

theorem inverse_fold_trace (ops : Ops α) (a b : Nat → α) (ts : List Nat) (s : State α) :
    (inverseFold ops a b ts s).trace=inverseEvents s.epochs ts ++ s.trace := by
  induction ts generalizing s with
  | nil => rfl
  | cons t ts ih =>
      rw [inverse_fold_cons,ih,(inverse_tail_fields ops t (t%1024) (a t) (b t) s).2.2.2.2,inverse_tail_trace]
      simp only [inverseEvents,List.append_assoc,List.singleton_append]

theorem inverse_events_length (epochs : Nat → Epoch) (ts : List Nat) :
    (inverseEvents epochs ts).length=ts.length := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [inverseEvents,ih]

theorem inverse_fold_good (ops : Ops α) (a b : Nat → α) (ts : List Nat) (s : State α)
    (epochs : ∀ t∈ts,(s.epochs t).block=1) (good : ∀ event∈s.trace,Good event) :
    ∀ event∈(inverseFold ops a b ts s).trace,Good event := by
  induction ts generalizing s with
  | nil => exact good
  | cons t ts ih =>
      apply ih (inverseTail ops t (t%1024) (a t) (b t) s)
      · intro u hu
        rw [(inverse_tail_fields ops t (t%1024) (a t) (b t) s).2.2.2.2]
        exact epochs u (by simp [hu])
      · exact inverse_tail_good ops t (a t) (b t) s (epochs t (by simp)) good

#print axioms inverse_fold_cons
#print axioms inverse_fold_indices_epochs
#print axioms inverse_fold_other
#print axioms inverse_fold_member
#print axioms inverse_fold_run
#print axioms inverse_fold_memory
#print axioms inverse_fold_written_value
#print axioms inverse_fold_trace
#print axioms inverse_events_length
#print axioms inverse_fold_good
end LarkNativeSglangRmsNorm
