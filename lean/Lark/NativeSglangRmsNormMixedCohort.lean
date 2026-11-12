import Lark.NativeSglangRmsNormSecondFold
import Lark.NativeSglangRmsNormRegisterXor

/-! The second reduction selects one logical32 cohort inside the full physical
wave64. Inactive lanes remain in the native runner, parked at the block barrier.
-/
namespace LarkNativeSglangRmsNorm
open LarkNonlinear LarkCollective
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
attribute [local irreducible] prefixFold reductionSnapshot partialFold firstBlockFold secondFold

def cohortUpper (row warp : Nat) : List Nat :=
  (List.range 32).map (fun lane => cohortBase row warp+32+lane)

theorem cohort_split (row warp : Nat) :
    cohortThreads row warp 64=cohortThreads row warp 32 ++ cohortUpper row warp := by
  have ranges : List.range 64=List.range 32 ++ (List.range 32).map (fun lane => 32+lane) := by decide
  simp only [cohortThreads,cohortUpper,ranges,List.map_append,List.map_map,Function.comp_def,Nat.add_assoc]

theorem cohort_upper_mem (row warp t : Nat) :
    t∈cohortUpper row warp ↔ ∃ lane,lane<32 ∧ t=cohortBase row warp+32+lane := by
  simp only [cohortUpper,List.mem_map,List.mem_range]
  constructor
  · rintro ⟨lane,hl,he⟩; exact ⟨lane,hl,he.symm⟩
  · rintro ⟨lane,hl,he⟩; exact ⟨lane,hl,he.symm⟩

theorem mixed_next (row pc : Nat) (s : State α) (hne : pc≠76)
    (active : ∀ lane,lane<32 → s.pc (cohortBase row 0+lane)=pc)
    (inactive : ∀ lane,lane<32 → s.pc (cohortBase row 0+32+lane)=76)
    (shuffle : ∀ t,s.pc t=pc → LarkPartitionCollective.isShuffle (program true) s t=true) :
    LarkPartitionCollective.nextCohort (program true) (cohortThreads row 0 64) s=
      some (cohortThreads row 0 32) := by
  have barrier : (program true)[76]?=some (.scalar (.barrier .block)) := by decide
  have ha : (cohortThreads row 0 32).filter (LarkPartitionCollective.isShuffle (program true) s)=
      cohortThreads row 0 32 := by
    apply List.filter_eq_self.mpr
    intro t ht
    obtain ⟨lane,hl,rfl⟩ := (cohort_mem row 0 32 t).mp ht
    exact shuffle _ (active lane hl)
  have hb : (cohortUpper row 0).filter (LarkPartitionCollective.isShuffle (program true) s)=[] := by
    apply List.filter_eq_nil_iff.mpr
    intro t ht
    obtain ⟨lane,hl,rfl⟩ := (cohort_upper_mem row 0 t).mp ht
    simp only [LarkPartitionCollective.isShuffle,inactive lane hl,barrier,Bool.false_eq_true,not_false_eq_true]
  have hp0 : s.pc (cohortBase row 0)=pc := by simpa only [Nat.add_zero] using active 0 (by decide)
  unfold LarkPartitionCollective.nextCohort
  rw [cohort_split,List.filter_append,ha,hb,List.append_nil,cohort_head row 0 32 (by decide)]
  simp only [bind,pure,Option.some_bind,hp0,List.filter_append]
  have hac : (cohortThreads row 0 32).filter (fun t => s.pc t==pc)=cohortThreads row 0 32 := by
    apply List.filter_eq_self.mpr
    intro t ht
    obtain ⟨lane,hl,rfl⟩ := (cohort_mem row 0 32 t).mp ht
    simp [active lane hl]
  have hbc : (cohortUpper row 0).filter (fun t => s.pc t==pc)=[] := by
    apply List.filter_eq_nil_iff.mpr
    intro t ht
    obtain ⟨lane,hl,rfl⟩ := (cohort_upper_mem row 0 t).mp ht
    simp [inactive lane hl,Ne.symm hne]
  rw [hac,hbc,List.append_nil]

theorem barrier_lane_fold (p : Shape) (ops : Ops α) (ts : List Nat) (s : State α)
    (hp : ∀ t∈ts,s.pc t=76) :
    ts.foldlM (fun u t => LarkCollective.runLane ops (layout p) (geometry p) (program true) t fuel.lane u) s=
      some s := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
      have parked : LarkCollective.parked (program true) s t=some .block := by
        have code : (program true)[76]?=some (.scalar (.barrier .block)) := by decide
        simp only [LarkCollective.parked,hp t (by simp),code,scalarCut]
      have lane : LarkCollective.runLane ops (layout p) (geometry p) (program true) t fuel.lane s=some s := by
        change LarkCollective.runLane ops (layout p) (geometry p) (program true) t (511+1) s=_
        rw [LarkCollective.runLane,parked]
      rw [List.foldlM_cons,lane]
      exact ih (fun u hu => hp u (by simp [hu]))

def secondPrepared (ops : Ops α) (input : Nat → Nat → α) (row : Nat) (s : State α) : State α :=
  secondFold ops input (cohortThreads row 0 64) s

theorem second_prepared_fields (ops : Ops α) (input : Nat → Nat → α) (row lane : Nat)
    (s : State α) (hl : lane<64) :
    (secondPrepared ops input row s).pc (cohortBase row 0+lane)=(if lane<32 then 62 else 76) ∧
    (lane<32 → (secondPrepared ops input row s).regs (cohortBase row 0+lane) 7=
      some (blockPartialValue ops input row lane)) := by
  have h := second_fold_member ops input (cohortThreads row 0 64) s (cohort_nodup row 0 64)
    _ ((cohort_mem row 0 64 _).mpr ⟨lane,hl,rfl⟩)
  have coords := cohort_arithmetic row 0 lane (by decide) hl
  constructor
  · change (secondFold ops input (cohortThreads row 0 64) s).pc _=_
    rw [h.1]
    simp only [secondPC,coords.2.1,Nat.zero_mul,Nat.zero_add]
  · intro ht
    have htid : (cohortBase row 0+lane)%1024<32 := by rw [coords.2.1]; omega
    change (secondFold ops input (cohortThreads row 0 64) s).regs _ _=_
    have hreg := (h.2 htid).1
    simpa only [coords.1,coords.2.1,Nat.zero_mul,Nat.zero_add] using hreg

def secondFirstSnapshot (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row : Nat) (s : State α) : State α :=
  shuffleUpdates 8 (xorSnapshot p row 0 32 16 (blockPartialValue ops input row))
    (secondPrepared ops input row s)

theorem second_prepared_next (ops : Ops α) (input : Nat → Nat → α) (row : Nat) (s : State α) :
    LarkPartitionCollective.nextCohort (program true) (cohortThreads row 0 64)
      (secondPrepared ops input row s)=some (cohortThreads row 0 32) := by
  apply mixed_next row 62 _ (by decide)
  · intro lane hl
    simpa only [if_pos hl] using (second_prepared_fields ops input row lane s (by omega)).1
  · intro lane hl
    have hn : ¬32+lane<32 := by omega
    simpa only [Nat.add_assoc,if_neg hn] using
      (second_prepared_fields ops input row (32+lane) s (by omega)).1
  · intro t ht
    have code : (program true)[62]?=some (.shuffle .xor 8 7 (.const 16) 32) := by decide
    simp only [LarkPartitionCollective.isShuffle,ht,code]

theorem second_first_shuffle (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row : Nat) (s : State α) :
    LarkPartitionCollective.runShuffle (geometry p) (program true) (cohortThreads row 0 32)
      (secondPrepared ops input row s)=some (secondFirstSnapshot p ops input row s) := by
  apply cohort_reg_xor_shuffle p true row 0 32 16 62 8 7 _ (blockPartialValue ops input row)
    (by decide) (Or.inl rfl) (by decide)
  · intro lane hl
    simpa only [if_pos hl] using (second_prepared_fields ops input row lane s (by omega)).1
  · intro lane hl
    exact (second_prepared_fields ops input row lane s (by omega)).2 hl
  · decide

theorem native_second_entry (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row n : Nat) (s : State α) (reads : Reads p input s) :
    LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel (program true)
      (warpThreads (geometry p) row 0) (n+1) (resumedFirstBlock p ops input row s)=
    LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel (program true)
      (cohortThreads row 0 64) n (secondFirstSnapshot p ops input row (resumedFirstBlock p ops input row s)) := by
  rw [cohort_native_threads p row 0 (by decide),run_warp_continue,
    resumed_second_fold_run p ops input row 0 s reads (by decide)]
  simp only [Option.some_bind]
  change continueCohort p true ops (cohortThreads row 0 64) n
    (secondPrepared ops input row (resumedFirstBlock p ops input row s))=_
  unfold continueCohort
  rw [second_prepared_next]
  dsimp only
  rw [second_first_shuffle]
  rfl

#print axioms cohort_split
#print axioms cohort_upper_mem
#print axioms mixed_next
#print axioms barrier_lane_fold
#print axioms second_prepared_fields
#print axioms second_prepared_next
#print axioms second_first_shuffle
#print axioms native_second_entry
end LarkNativeSglangRmsNorm
