import Lark.NativeSglangRmsNormOutputFold

/-! Actual native output-wave composition. Each full physical wave64 runs all
its lanes to halt, retaining earlier wave outputs and readiness of later waves.
-/
namespace LarkNativeSglangRmsNorm
open LarkNonlinear LarkCollective
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
attribute [local irreducible] prefixFold reductionSnapshot partialFold firstBlockFold secondFold regAddFold inverseFold secondSnapshot skipFold inactiveWaves scalePairs scaleRounds outputCopies outputFold

theorem halt_next_none (ts : List Nat) (s : State α) (hp : ∀ t∈ts,s.pc t=109) :
    LarkPartitionCollective.nextCohort (program true) ts s=none := by
  have code : (program true)[109]?=some (.scalar .halt) := by decide
  have hf : ts.filter (LarkPartitionCollective.isShuffle (program true) s)=[] := by
    apply List.filter_eq_nil_iff.mpr
    intro t ht
    simp only [LarkPartitionCollective.isShuffle,hp t ht,code,Bool.false_eq_true,not_false_eq_true]
  unfold LarkPartitionCollective.nextCohort
  rw [hf]
  rfl

theorem halt_converged (ts : List Nat) (s : State α) (hn : ts≠[]) (hp : ∀ t∈ts,s.pc t=109) :
    LarkCollective.converged (program true) ts s=some .halt := by
  have code : (program true)[109]?=some (.scalar .halt) := by decide
  cases ts with
  | nil => exact False.elim (hn rfl)
  | cons t ts =>
      have hp0 := hp t (by simp)
      have hall : (t::ts).all (fun u => s.pc u==109)=true := by
        apply List.all_eq_true.mpr
        intro u hu
        simp only [hp u hu,beq_self_eq_true]
      simp only [LarkCollective.converged,List.head?_cons,bind,Option.some_bind,
        LarkCollective.parked,hp0,hall,↓reduceIte,code]

theorem native_output_wave (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row w n : Nat) (s : State α) (hr : row<p.rows) (hw : w<16)
    (ready : ∀ t∈cohortThreads row w 64,OutputReady ops input t s) :
    LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel (program true)
      (warpThreads (geometry p) row w) (n+1) s=some (outputFold ops input (cohortThreads row w 64) s) := by
  have bounds : ∀ t∈cohortThreads row w 64,t/1024<p.rows := by
    intro t ht
    obtain ⟨lane,hl,rfl⟩ := (cohort_mem row w 64 t).mp ht
    rw [(cohort_arithmetic row w lane hw hl).1]
    exact hr
  rw [cohort_native_threads p row w hw,run_warp_continue,
    output_fold_run p ops input _ s (cohort_nodup row w 64) bounds ready]
  simp only [Option.some_bind]
  have hp := fun t ht => output_fold_member_pc ops input (cohortThreads row w 64) s (cohort_nodup row w 64) t ht
  have hn : cohortThreads row w 64≠[] := by
    intro he
    have hh := cohort_head row w 64 (by decide)
    rw [he] at hh
    cases hh
  unfold continueCohort
  rw [halt_next_none _ _ hp,halt_converged _ _ hn hp]
  rfl

def outputWaves (ops : Ops α) (input : Nat → Nat → α) (row : Nat) (ws : List Nat) (s : State α) : State α :=
  ws.foldl (fun s w => outputFold ops input (cohortThreads row w 64) s) s

theorem output_waves_eq_fold (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ws : List Nat) (s : State α) :
    outputWaves ops input row ws s=outputFold ops input (ws.flatMap (fun w => cohortThreads row w 64)) s := by
  induction ws generalizing s with
  | nil => rw [outputWaves,outputFold]; rfl
  | cons w ws ih =>
      change outputWaves ops input row ws (outputFold ops input (cohortThreads row w 64) s)=_
      rw [ih]
      simp only [List.flatMap_cons,outputFold,List.foldl_append]

theorem output_waves_run (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ws : List Nat) (s : State α) (hr : row<p.rows)
    (hn : ws.Nodup) (bounds : ∀ w∈ws,w<16)
    (ready : ∀ t∈ws.flatMap (fun w => cohortThreads row w 64),OutputReady ops input t s) :
    ws.foldlM (fun u w => LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel (program true)
      (warpThreads (geometry p) row w) fuel.warp u) s=some (outputWaves ops input row ws s) := by
  induction ws generalizing s with
  | nil => rfl
  | cons w ws ih =>
      obtain ⟨hnot,hnodup⟩ := List.nodup_cons.mp hn
      have headReady : ∀ t∈cohortThreads row w 64,OutputReady ops input t s := by
        intro t ht
        exact ready t (by rw [List.flatMap_cons]; exact List.mem_append_left _ ht)
      have headRun : LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel (program true)
          (warpThreads (geometry p) row w) fuel.warp s=some (outputFold ops input (cohortThreads row w 64) s) :=
        native_output_wave p ops input row w 7 s hr (bounds w (by simp)) headReady
      rw [List.foldlM_cons,headRun]
      apply ih (outputFold ops input (cohortThreads row w 64) s) hnodup
      · intro v hv; exact bounds v (by simp [hv])
      · intro t ht
        obtain ⟨v,hv,htv⟩ := List.mem_flatMap.mp ht
        have hne : v≠w := by intro he; subst v; exact hnot hv
        apply output_fold_ready_other ops input (cohortThreads row w 64) t s (distinct_cohorts row v w t hne htv)
        exact ready t (by rw [List.flatMap_cons]; exact List.mem_append_right _ ht)

theorem all_output_threads (p : Shape) (row : Nat) :
    (List.range 16).flatMap (fun w => cohortThreads row w 64)=blockThreads (geometry p) row := by
  have h : (List.range 16).flatMap (fun w => (List.range 64).map (fun lane => w*64+lane))=List.range 1024 := by decide
  have hmap := congrArg (List.map (fun t => row*1024+t)) h
  simpa only [List.map_flatMap,List.map_map,Function.comp_def,cohortThreads,cohortBase,
    blockThreads,geometry,Nat.add_assoc] using hmap

#print axioms halt_next_none
#print axioms halt_converged
#print axioms native_output_wave
#print axioms output_waves_eq_fold
#print axioms output_waves_run
#print axioms all_output_threads
end LarkNativeSglangRmsNorm
