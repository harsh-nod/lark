import Lark.NativeSglangRmsNormPartialStore

/-! Sequential last-add/store execution for a noduplicated thread cohort.
Original writes and their epochs remain explicit even when values coincide.
-/
namespace LarkNativeSglangRmsNorm
open LarkNonlinear LarkCollective
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def partialFold (repaired : Bool) (ops : Ops α) (a b : Nat → α)
    (ts : List Nat) (s : State α) : State α :=
  ts.foldl (fun s t => lastPartial repaired ops t (a t) (b t) s) s

theorem partial_fold_indices_epochs (repaired : Bool) (ops : Ops α) (a b : Nat → α)
    (ts : List Nat) (s : State α) :
    (partialFold repaired ops a b ts s).indices=s.indices ∧
    (partialFold repaired ops a b ts s).epochs=s.epochs := by
  induction ts generalizing s with
  | nil => exact ⟨rfl,rfl⟩
  | cons t ts ih =>
      have h := ih (lastPartial repaired ops t (a t) (b t) s)
      have hf := last_partial_fields repaired ops t (a t) (b t) s
      exact ⟨h.1.trans hf.2.1,h.2.trans hf.2.2.2⟩

theorem partial_fold_other (repaired : Bool) (ops : Ops α) (a b : Nat → α)
    (ts : List Nat) (t : Nat) (s : State α) (ht : t∉ts) :
    (partialFold repaired ops a b ts s).pc t=s.pc t ∧
    (partialFold repaired ops a b ts s).regs t=s.regs t := by
  induction ts generalizing s with
  | nil => exact ⟨rfl,rfl⟩
  | cons u ts ih =>
      have hn : t∉ts := by intro hm; exact ht (by simp [hm])
      have he : t≠u := by intro he; subst t; simp at ht
      have h := ih (lastPartial repaired ops u (a u) (b u) s) hn
      have hf := last_partial_other repaired ops u t (a u) (b u) s he
      exact ⟨h.1.trans hf.1,h.2.trans hf.2⟩

theorem partial_fold_member (repaired : Bool) (ops : Ops α) (a b : Nat → α)
    (ts : List Nat) (s : State α) (hn : ts.Nodup) (t : Nat) (ht : t∈ts) :
    (partialFold repaired ops a b ts s).pc t=firstBarrier repaired ∧
    (partialFold repaired ops a b ts s).regs t 0=some (ops.add (a t) (b t)) := by
  induction ts generalizing s with
  | nil => simp at ht
  | cons u ts ih =>
      obtain ⟨hnot,hnodup⟩ := List.nodup_cons.mp hn
      rcases List.mem_cons.mp ht with he | hm
      · subst t
        have h := partial_fold_other repaired ops a b ts u (lastPartial repaired ops u (a u) (b u) s) hnot
        exact ⟨h.1.trans (last_partial_fields repaired ops u (a u) (b u) s).1,
          (congrFun h.2 0).trans (last_partial_regs repaired ops u (a u) (b u) s)⟩
      · exact ih (lastPartial repaired ops u (a u) (b u) s) hnodup hm

theorem partial_fold_memory (repaired : Bool) (ops : Ops α) (a b : Nat → α)
    (ts : List Nat) (s : State α) (l : Location)
    (outside : ∀ t∈ts,l≠partialSlot t ((t%1024)/32)) :
    (partialFold repaired ops a b ts s).memory l=s.memory l := by
  induction ts generalizing s with
  | nil => rfl
  | cons t ts ih =>
      exact (ih (lastPartial repaired ops t (a t) (b t) s)
        (fun u hu => outside u (by simp [hu]))).trans
        (last_partial_memory repaired ops t (a t) (b t) s l (outside t (by simp)))

theorem partial_fold_outside_shared (repaired : Bool) (ops : Ops α) (a b : Nat → α)
    (ts : List Nat) (s : State α) (l : Location) (hl : l.space≠.shared) :
    (partialFold repaired ops a b ts s).memory l=s.memory l := by
  apply partial_fold_memory
  intro t _ he
  exact hl (congrArg Location.space he)

theorem partial_fold_reads (p : Shape) (repaired : Bool) (ops : Ops α) (a b : Nat → α)
    (ts : List Nat) (s : State α) (reads : Reads p input s) :
    Reads p input (partialFold repaired ops a b ts s) := by
  constructor
  · intro offset hi
    rw [partial_fold_outside_shared repaired ops a b ts s (globalCell 1 offset) (by simp [globalCell])]
    exact reads.1 offset hi
  · intro offset hi
    rw [partial_fold_outside_shared repaired ops a b ts s (globalCell 2 offset) (by simp [globalCell])]
    exact reads.2 offset hi

theorem partial_fold_caches (repaired : Bool) (ops : Ops α) (a b : Nat → α)
    (ts : List Nat) (s : State α) (input : Nat → Nat → α) (row tid t : Nat)
    (hi : InputPrefix input row tid 16 t s) (hw : WeightPrefix input tid 16 t s) :
    InputPrefix input row tid 16 t (partialFold repaired ops a b ts s) ∧
    WeightPrefix input tid 16 t (partialFold repaired ops a b ts s) := by
  constructor
  · intro k hk
    rw [partial_fold_outside_shared repaired ops a b ts s (privateCell t 0 k) (by simp [privateCell])]
    exact hi k hk
  · intro k hk
    rw [partial_fold_outside_shared repaired ops a b ts s (privateCell t 1 k) (by simp [privateCell])]
    exact hw k hk

theorem partial_fold_run (p : Shape) (repaired : Bool) (ops : Ops α) (a b : Nat → α)
    (ts : List Nat) (s : State α) (hn : ts.Nodup)
    (hi : ∀ t∈ts,NativeIndices t s) (hp : ∀ t∈ts,s.pc t=53)
    (ha : ∀ t∈ts,s.regs t 0=some (a t)) (hb : ∀ t∈ts,s.regs t 1=some (b t)) :
    ts.foldlM (fun u t => LarkCollective.runLane ops (layout p) (geometry p) (program repaired) t fuel.lane u) s =
      some (partialFold repaired ops a b ts s) := by
  induction ts generalizing s with
  | nil => rfl
  | cons t ts ih =>
      obtain ⟨hnot,hnodup⟩ := List.nodup_cons.mp hn
      have hne : ∀ u∈ts,u≠t := by intro u hu he; subst u; exact hnot hu
      rw [List.foldlM_cons,last_partial_lane p repaired ops t (a t) (b t) s
        (hi t (by simp)) (hp t (by simp)) (ha t (by simp)) (hb t (by simp))]
      apply ih (lastPartial repaired ops t (a t) (b t) s) hnodup
      · intro u hu
        simpa only [NativeIndices,(last_partial_fields repaired ops t (a t) (b t) s).2.1] using hi u (by simp [hu])
      · intro u hu
        exact (last_partial_other repaired ops t u (a t) (b t) s (hne u hu)).1.trans (hp u (by simp [hu]))
      · intro u hu
        exact (congrFun (last_partial_other repaired ops t u (a t) (b t) s (hne u hu)).2 0).trans (ha u (by simp [hu]))
      · intro u hu
        exact (congrFun (last_partial_other repaired ops t u (a t) (b t) s (hne u hu)).2 1).trans (hb u (by simp [hu]))

def partialEvents (repaired : Bool) (epochs : Nat → Epoch) : List Nat → List Access
  | [] => []
  | t::ts => partialEvents repaired epochs ts ++
      (if repaired ∧ (t%1024)%32≠0 then [] else [⟨t,partialSlot t ((t%1024)/32),true,epochs t⟩])

theorem partial_fold_trace (repaired : Bool) (ops : Ops α) (a b : Nat → α)
    (ts : List Nat) (s : State α) :
    (partialFold repaired ops a b ts s).trace=partialEvents repaired s.epochs ts ++ s.trace := by
  induction ts generalizing s with
  | nil => rfl
  | cons t ts ih =>
      change (partialFold repaired ops a b ts (lastPartial repaired ops t (a t) (b t) s)).trace = _
      rw [ih,(last_partial_fields repaired ops t (a t) (b t) s).2.2.2,last_partial_trace]
      simp only [partialEvents,List.append_assoc]

theorem original_partial_events_length (epochs : Nat → Epoch) (ts : List Nat) :
    (partialEvents false epochs ts).length=ts.length := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [partialEvents,ih]

theorem original_partial_events_member (epochs : Nat → Epoch) (ts : List Nat) (t : Nat) (ht : t∈ts) :
    ⟨t,partialSlot t ((t%1024)/32),true,epochs t⟩∈partialEvents false epochs ts := by
  induction ts with
  | nil => simp at ht
  | cons u ts ih =>
      rcases List.mem_cons.mp ht with he | hm
      · subst t; simp [partialEvents]
      · exact List.mem_append_left _ (ih hm)

theorem fixed_last_partial_good (ops : Ops α) (t : Nat) (a b : α) (s : State α)
    (epoch : (s.epochs t).block=0) (good : ∀ event∈s.trace,Good event) :
    ∀ event∈(lastPartial true ops t a b s).trace,Good event := by
  intro event he
  rw [last_partial_trace] at he
  by_cases hz : (t%1024)%32=0
  · simp only [hz,ne_eq,not_true_eq_false,and_false,↓reduceIte,List.singleton_append,List.mem_cons] at he
    rcases he with rfl | he
    · apply Good.partialStore rfl rfl rfl (by change t%1024=(t%1024)/32*32; omega) epoch rfl
    · exact good event he
  · have guard : true=true ∧ (t%1024)%32≠0 := ⟨rfl,hz⟩
    rw [if_pos guard,List.nil_append] at he
    exact good event he

theorem fixed_partial_fold_good (ops : Ops α) (a b : Nat → α) (ts : List Nat) (s : State α)
    (epochs : ∀ t∈ts,(s.epochs t).block=0) (good : ∀ event∈s.trace,Good event) :
    ∀ event∈(partialFold true ops a b ts s).trace,Good event := by
  induction ts generalizing s with
  | nil => exact good
  | cons t ts ih =>
      apply ih (lastPartial true ops t (a t) (b t) s)
      · intro u hu
        rw [(last_partial_fields true ops t (a t) (b t) s).2.2.2]
        exact epochs u (by simp [hu])
      · exact fixed_last_partial_good ops t (a t) (b t) s (epochs t (by simp)) good

#print axioms partial_fold_indices_epochs
#print axioms partial_fold_other
#print axioms partial_fold_member
#print axioms partial_fold_memory
#print axioms partial_fold_outside_shared
#print axioms partial_fold_reads
#print axioms partial_fold_caches
#print axioms partial_fold_run
#print axioms partial_fold_trace
#print axioms original_partial_events_length
#print axioms original_partial_events_member
#print axioms fixed_last_partial_good
#print axioms fixed_partial_fold_good
end LarkNativeSglangRmsNorm
