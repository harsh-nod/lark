import Lark.NativeFlashInferRmsNormOutputWave

/-! Actual source-ordered composition of physical output waves. Already stored
values and halted lanes remain present as each later wave runs.
-/
namespace LarkNativeFlashInferRmsNorm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def outputWaves (ops : Ops α) (input : Nat → Nat → α) (row : Nat) (ws : List Nat) (s : State α) : State α :=
  ws.foldl (fun s w => outputWave ops input row w s) s

theorem output_waves_eq_fold (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ws : List Nat) (s : State α) :
    outputWaves ops input row ws s = outputFold ops input row (ws.flatMap (fun w => cohortThreads row w 64)) s := by
  induction ws generalizing s with
  | nil => rfl
  | cons w ws ih =>
      change outputWaves ops input row ws (outputWave ops input row w s) = _
      rewrite [ih]
      simp only [List.flatMap_cons,outputFold,List.foldl_append]
      rfl

theorem output_entry_subset (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ts us : List Nat) (s : State α) (hs : ∀ t ∈ ts, t ∈ us)
    (entry : OutputFoldEntry p ops input row us s) : OutputFoldEntry p ops input row ts s := by
  exact {
    valid := entry.valid, reads := entry.reads, total := entry.total, good := entry.good
    indices := fun t ht => entry.indices t (hs t ht)
    pc := fun t ht => entry.pc t (hs t ht)
    epoch := fun t ht => entry.epoch t (hs t ht) }

theorem output_entry_after_fold (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ts us : List Nat) (s : State α)
    (entry : OutputFoldEntry p ops input row us s) (hd : ∀ u ∈ us, u ∉ ts)
    (good : ∀ a ∈ (outputFold ops input row ts s).trace, Good a) :
    OutputFoldEntry p ops input row us (outputFold ops input row ts s) := by
  exact {
    valid := entry.valid
    reads := output_fold_reads ops input row ts s entry.reads
    indices := fun u hu => output_fold_indices ops input row ts u s (entry.indices u hu)
    total := (output_fold_shared ops input row ts s row 0 0).trans entry.total
    pc := fun u hu => (output_fold_other ops input row ts u s (hd u hu)).1.trans (entry.pc u hu)
    epoch := by
      intro u hu
      exact (congrArg (fun epochs => (epochs u).block) (output_fold_epochs ops input row ts s)).trans (entry.epoch u hu)
    good := good }

theorem output_waves_run (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ws : List Nat) (s : State α) (hn : ws.Nodup) (hb : ∀ w ∈ ws, w < 16)
    (entry : OutputFoldEntry p ops input row (ws.flatMap (fun w => cohortThreads row w 64)) s) :
    ws.foldlM (fun s w => LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel program
      (warpThreads (geometry p) row w) fuel.warp s) s = some (outputWaves ops input row ws s) := by
  induction ws generalizing s with
  | nil => rfl
  | cons w ws ih =>
      rcases List.nodup_cons.mp hn with ⟨hnot,hnodup⟩
      have headEntry := output_entry_subset p ops input row (cohortThreads row w 64)
        ((w :: ws).flatMap (fun u => cohortThreads row u 64)) s
        (by intro t ht; simp [List.mem_flatMap,ht]) entry
      have tailEntry := output_entry_subset p ops input row (ws.flatMap (fun u => cohortThreads row u 64))
        ((w :: ws).flatMap (fun u => cohortThreads row u 64)) s
        (by intro t ht; simp only [List.flatMap_cons,List.mem_append]; exact Or.inr ht) entry
      have next := output_entry_after_fold p ops input row (cohortThreads row w 64)
        (ws.flatMap (fun u => cohortThreads row u 64)) s tailEntry
        (by
          intro t ht
          obtain ⟨u,hu,ht⟩ := List.mem_flatMap.mp ht
          exact cohorts_disjoint row u w t (by intro he; subst u; exact hnot hu) ht)
        (output_fold_good p ops input row (cohortThreads row w 64) s (cohort_nodup row w 64)
          (by
            intro t ht
            obtain ⟨lane,hl,rfl⟩ := (cohort_mem row w 64 t).mp ht
            exact (cohort_arithmetic row w lane (hb w (by simp)) hl).1) headEntry)
      rewrite [List.foldlM_cons,output_wave_run p ops input row w s (hb w (by simp)) headEntry]
      simp only [bind,Option.some_bind]
      exact ih (outputWave ops input row w s) hnodup (by intro u hu; exact hb u (by simp [hu])) next

theorem all_output_threads (p : Shape) (row : Nat) :
    (List.range 16).flatMap (fun w => cohortThreads row w 64) = blockThreads (geometry p) row := by
  have h : (List.range 16).flatMap (fun w => (List.range 64).map (fun lane => w * 64 + lane)) = List.range 1024 := by decide
  have hmap := congrArg (List.map (fun t => row * 1024 + t)) h
  simpa only [List.map_flatMap,List.map_map,Function.comp_def,cohortThreads,cohortBase,
    blockThreads,geometry,Nat.add_assoc] using hmap

#print axioms output_waves_eq_fold
#print axioms output_entry_subset
#print axioms output_entry_after_fold
#print axioms output_waves_run
#print axioms all_output_threads
end LarkNativeFlashInferRmsNorm
