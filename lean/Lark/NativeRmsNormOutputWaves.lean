import Lark.NativeRmsNormOutputWave

/-! Actual source-ordered physical-wave composition for the output phase. -/
namespace LarkNativeRmsNorm
open LarkNonlinear
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

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
      simp only [List.flatMap_cons, outputFold, List.foldl_append]
      rfl

theorem output_wave_scale_frame (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp : Nat) (s : State α) (hw : warp < 16) :
    (outputWave ops input row warp s).memory (scaleSlot row) = s.memory (scaleSlot row) := by
  apply output_fold_memory_frame p ops input row _ s
  · intro t ht
    obtain ⟨lane, hl, rfl⟩ := (cohort_mem row warp 64 t).mp ht
    exact (cohort_arithmetic row warp lane hw hl).1
  · intro t ht howner
    have h := howner.1
    simp [scaleSlot] at h

theorem output_waves_run (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ws : List Nat) (s : State α) (hr : row < p.rows) (hn : ws.Nodup)
    (hb : ∀ w ∈ ws, w < 16) (reads : Reads p input s)
    (hi : ∀ w ∈ ws, ∀ lane, lane < 64 → NativeIndices (cohortBase row w + lane) s)
    (hs : s.memory (scaleSlot row) = some (scale ops input row))
    (hp : ∀ w ∈ ws, ∀ lane, lane < 64 → s.pc (cohortBase row w + lane) = 56) :
    ws.foldlM (fun s w => LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel program
      (warpThreads (geometry p) row w) fuel.warp s) s = some (outputWaves ops input row ws s) := by
  induction ws generalizing s with
  | nil => rfl
  | cons w ws ih =>
      rcases List.nodup_cons.mp hn with ⟨hnot, hnodup⟩
      rewrite [List.foldlM_cons, output_wave_run p ops input row w s hr (hb w (by simp)) reads
        (hi w (by simp)) hs (hp w (by simp))]
      simp only [bind, Option.some_bind]
      apply ih (outputWave ops input row w s) hnodup (by intro u hu; exact hb u (by simp [hu]))
      · exact output_fold_reads p ops input row (cohortThreads row w 64) s reads
      · intro u hu lane hl
        exact output_fold_indices ops input row (cohortThreads row w 64) _ s (hi u (by simp [hu]) lane hl)
      · exact (output_wave_scale_frame p ops input row w s (hb w (by simp))).trans hs
      · intro u hu lane hl
        have ht := cohort_disjoint row u w lane hl (by intro he; subst u; exact hnot hu)
        exact (output_fold_other ops input row (cohortThreads row w 64) _ s ht).1.trans (hp u (by simp [hu]) lane hl)

theorem all_output_threads (p : Shape) (row : Nat) :
    (List.range 16).flatMap (fun w => cohortThreads row w 64) = blockThreads (geometry p) row := by
  have h : (List.range 16).flatMap (fun w => (List.range 64).map (fun lane => w * 64 + lane)) = List.range 1024 := by decide
  have hmap := congrArg (List.map (fun t => row * 1024 + t)) h
  simpa only [List.map_flatMap, List.map_map, Function.comp_def, cohortThreads, cohortBase,
    blockThreads, geometry, Nat.add_assoc] using hmap

#print axioms output_waves_run
#print axioms all_output_threads
end LarkNativeRmsNorm
