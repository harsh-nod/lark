import Lark.NativeSglangRmsNormSecondScalar

/-! Actual scalar preparation of the second reduction's full native cohort.
Only logical warp0 reads shared memory; inactive lanes park at PC76. Every
read remains in the trace and all cached/private/shared values are preserved.
-/
namespace LarkNativeSglangRmsNorm
open LarkNonlinear LarkCollective
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
attribute [local irreducible] prefixFold reductionSnapshot partialFold firstBlockFold

def secondPC (t : Nat) : Nat := if t%1024<32 then 62 else 76
def secondFold (ops : Ops α) (input : Nat → Nat → α) (ts : List Nat) (s : State α) : State α :=
  ts.foldl (fun s t => secondLane ops input t s) s

theorem second_lane_fields (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) :
    (secondLane ops input t s).pc t=secondPC t ∧
    (t%1024<32 → (secondLane ops input t s).regs t 7=some (blockPartialValue ops input (t/1024) (t%1024)) ∧
      (secondLane ops input t s).regs t 8=some (ops.literal 0 1)) := by
  by_cases ht : t%1024<32
  · have h := second_active_fields ops t (t%1024) (blockPartialValue ops input (t/1024) (t%1024)) s
    simp only [secondLane,secondPC,if_pos ht]
    exact ⟨h.1,fun _ => h.2⟩
  · simp only [secondLane,secondPC,if_neg ht,advance,↓reduceIte,ht,false_implies,and_true]

theorem second_fold_preserves (ops : Ops α) (input : Nat → Nat → α) (ts : List Nat) (s : State α) :
    (secondFold ops input ts s).memory=s.memory ∧ (secondFold ops input ts s).indices=s.indices ∧
    (secondFold ops input ts s).epochs=s.epochs := by
  induction ts generalizing s with
  | nil => exact ⟨rfl,rfl,rfl⟩
  | cons t ts ih =>
      have h := ih (secondLane ops input t s)
      have hs := second_lane_preserves ops input t s
      exact ⟨h.1.trans hs.1,h.2.1.trans hs.2.1,h.2.2.trans hs.2.2⟩

theorem second_fold_other (ops : Ops α) (input : Nat → Nat → α) (ts : List Nat)
    (t : Nat) (s : State α) (ht : t∉ts) :
    (secondFold ops input ts s).pc t=s.pc t ∧ (secondFold ops input ts s).regs t=s.regs t := by
  induction ts generalizing s with
  | nil => exact ⟨rfl,rfl⟩
  | cons u ts ih =>
      have hn : t∉ts := by intro hm; exact ht (by simp [hm])
      have hne : t≠u := by intro he; subst t; simp at ht
      have h := ih (secondLane ops input u s) hn
      have hs := second_lane_other ops input u t s hne
      exact ⟨h.1.trans hs.1,h.2.trans hs.2⟩

theorem second_fold_member (ops : Ops α) (input : Nat → Nat → α) (ts : List Nat)
    (s : State α) (hn : ts.Nodup) (t : Nat) (ht : t∈ts) :
    (secondFold ops input ts s).pc t=secondPC t ∧
    (t%1024<32 → (secondFold ops input ts s).regs t 7=some (blockPartialValue ops input (t/1024) (t%1024)) ∧
      (secondFold ops input ts s).regs t 8=some (ops.literal 0 1)) := by
  induction ts generalizing s with
  | nil => simp at ht
  | cons u ts ih =>
      obtain ⟨hnot,hnodup⟩ := List.nodup_cons.mp hn
      rcases List.mem_cons.mp ht with he | hm
      · subst t
        have h := second_fold_other ops input ts u (secondLane ops input u s) hnot
        have hs := second_lane_fields ops input u s
        refine ⟨h.1.trans hs.1,?_⟩
        intro hu
        exact ⟨(congrFun h.2 7).trans (hs.2 hu).1,(congrFun h.2 8).trans (hs.2 hu).2⟩
      · exact ih (secondLane ops input u s) hnodup hm

theorem second_fold_run (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (ts : List Nat) (s : State α) (hn : ts.Nodup)
    (hi : ∀ t∈ts,NativeIndices t s) (hp : ∀ t∈ts,s.pc t=57)
    (shared : ∀ t∈ts,∀ tid,tid<32 → s.memory (partialSlot t tid)=some (blockPartialValue ops input (t/1024) tid)) :
    ts.foldlM (fun u t => LarkCollective.runLane ops (layout p) (geometry p) (program true) t fuel.lane u) s=
      some (secondFold ops input ts s) := by
  induction ts generalizing s with
  | nil => rfl
  | cons t ts ih =>
      obtain ⟨hnot,hnodup⟩ := List.nodup_cons.mp hn
      rw [List.foldlM_cons,second_source_lane p ops input t s (hi t (by simp)) (hp t (by simp)) (shared t (by simp))]
      apply ih (secondLane ops input t s) hnodup
      · intro u hu
        simpa only [NativeIndices,(second_lane_preserves ops input t s).2.1] using hi u (by simp [hu])
      · intro u hu
        have hne : u≠t := by intro he; subst u; exact hnot hu
        exact (second_lane_other ops input t u s hne).1.trans (hp u (by simp [hu]))
      · intro u hu tid ht
        rw [(second_lane_preserves ops input t s).1]
        exact shared u (by simp [hu]) tid ht

def secondEvents (epochs : Nat → Epoch) : List Nat → List Access
  | [] => []
  | t::ts => secondEvents epochs ts ++
      (if t%1024<32 then [⟨t,partialSlot t (t%1024),false,epochs t⟩] else [])

theorem second_fold_trace (ops : Ops α) (input : Nat → Nat → α) (ts : List Nat) (s : State α) :
    (secondFold ops input ts s).trace=secondEvents s.epochs ts ++ s.trace := by
  induction ts generalizing s with
  | nil => rfl
  | cons t ts ih =>
      change (secondFold ops input ts (secondLane ops input t s)).trace=_
      rw [ih,(second_lane_preserves ops input t s).2.2,second_lane_trace]
      simp only [secondEvents,List.append_assoc]

theorem second_lane_good (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α)
    (epoch : (s.epochs t).block=1) (good : ∀ event∈s.trace,Good event) :
    ∀ event∈(secondLane ops input t s).trace,Good event := by
  intro event he
  rw [second_lane_trace] at he
  by_cases ht : t%1024<32
  · rw [if_pos ht] at he
    simp only [List.singleton_append,List.mem_cons] at he
    rcases he with rfl | he
    · exact Good.partialRead rfl rfl rfl rfl epoch rfl
    · exact good event he
  · rw [if_neg ht,List.nil_append] at he
    exact good event he

theorem second_fold_good (ops : Ops α) (input : Nat → Nat → α) (ts : List Nat) (s : State α)
    (epochs : ∀ t∈ts,(s.epochs t).block=1) (good : ∀ event∈s.trace,Good event) :
    ∀ event∈(secondFold ops input ts s).trace,Good event := by
  induction ts generalizing s with
  | nil => exact good
  | cons t ts ih =>
      apply ih (secondLane ops input t s)
      · intro u hu
        rw [(second_lane_preserves ops input t s).2.2]
        exact epochs u (by simp [hu])
      · exact second_lane_good ops input t s (epochs t (by simp)) good

theorem resumed_second_fold_run (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row w : Nat) (s : State α) (reads : Reads p input s) (hw : w<16) :
    (cohortThreads row w 64).foldlM
      (fun u t => LarkCollective.runLane ops (layout p) (geometry p) (program true) t fuel.lane u)
      (resumedFirstBlock p ops input row s)=
      some (secondFold ops input (cohortThreads row w 64) (resumedFirstBlock p ops input row s)) := by
  apply second_fold_run p ops input _ _ (cohort_nodup row w 64)
  · intro t ht
    exact resumed_first_block_indices p ops input row t s reads (cohort_in_block p row w t hw ht)
  · intro t ht
    exact resumed_first_block_pc p ops input row t s (cohort_in_block p row w t hw ht)
  · intro t ht tid htid
    obtain ⟨lane,hl,rfl⟩ := (cohort_mem row w 64 t).mp ht
    have hc := cohort_arithmetic row w lane hw hl
    simpa only [partialSlot,hc.1] using resumed_first_block_shared_values p ops input row s reads tid htid

#print axioms second_lane_fields
#print axioms second_fold_preserves
#print axioms second_fold_other
#print axioms second_fold_member
#print axioms second_fold_run
#print axioms second_fold_trace
#print axioms second_lane_good
#print axioms second_fold_good
#print axioms resumed_second_fold_run
end LarkNativeSglangRmsNorm
