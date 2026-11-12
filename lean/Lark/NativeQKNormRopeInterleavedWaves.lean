import Lark.NativeQKNormRopeInterleavedResult

/-! Actual sequential wave execution within a native block. Completed outputs
and other waves' entry states are preserved without resetting memory. -/
namespace LarkNativeQKNormRope
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def interleavedWaves (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (block : Nat)
    (ws : List Nat) (s : State α) : State α :=
  ws.foldl (fun s warp => interleavedWaveState p ops input block warp s) s

theorem interleaved_waves_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (block : Nat)
    (ws : List Nat) (s : State α) (hr : Reads p input s) : Reads p input (interleavedWaves p ops input block ws s) := by
  induction ws generalizing s with
  | nil => exact hr
  | cons w ws ih => exact ih (interleavedWaveState p ops input block w s) (interleaved_wave_reads p ops input block w s hr)

theorem interleaved_waves_epochs (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (block : Nat)
    (ws : List Nat) (s : State α) : (interleavedWaves p ops input block ws s).epochs = s.epochs := by
  induction ws generalizing s with
  | nil => rfl
  | cons w ws ih => exact (ih (interleavedWaveState p ops input block w s)).trans (interleaved_wave_epochs p ops input block w s)

theorem interleaved_waves_other (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (block : Nat)
    (ws : List Nat) (t : Nat) (s : State α) (ht : ∀ w ∈ ws, t ∉ cohortThreads block w 64) :
    (interleavedWaves p ops input block ws s).pc t = s.pc t ∧
    (interleavedWaves p ops input block ws s).indices t = s.indices t ∧
    (interleavedWaves p ops input block ws s).regs t = s.regs t := by
  induction ws generalizing s with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons w ws ih =>
      have after := ih (interleavedWaveState p ops input block w s) (by intro v hv; exact ht v (by simp [hv]))
      have first := interleaved_wave_other p ops input block w t s (ht w (by simp))
      exact ⟨after.1.trans first.1, after.2.1.trans first.2.1, after.2.2.trans first.2.2⟩

theorem interleaved_waves_memory_frame (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (block : Nat)
    (ws : List Nat) (s : State α) (loc : Location)
    (hn : ∀ w ∈ ws, ∀ t ∈ cohortThreads block w 64, loc.buffer ≠ 0 ∨ loc.offset / 4 ≠ t) :
    (interleavedWaves p ops input block ws s).memory loc = s.memory loc := by
  induction ws generalizing s with
  | nil => rfl
  | cons w ws ih =>
      exact (ih (interleavedWaveState p ops input block w s) (by intro v hv; exact hn v (by simp [hv]))).trans
        (interleaved_wave_memory_frame p ops input block w s loc (hn w (by simp)))

theorem interleaved_waves_run (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (block : Nat)
    (ws : List Nat) (s : State α) (hb : block < p.rows * 5) (hn : ws.Nodup) (hw : ∀ w ∈ ws, w < 4)
    (hp : ∀ w ∈ ws, ∀ t ∈ cohortThreads block w 64, s.pc t = 0) (hr : Reads p input s) :
    ws.foldlM (fun s w => LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel (program false)
      (warpThreads (geometry p) block w) fuel.warp s) s = some (interleavedWaves p ops input block ws s) := by
  induction ws generalizing s with
  | nil => rfl
  | cons w ws ih =>
      obtain ⟨hnot, hnodup⟩ := List.nodup_cons.mp hn
      rw [List.foldlM_cons, native_interleaved_wave p ops input block w s hb (hw w (by simp)) (hp w (by simp)) hr]
      simp only [bind, Option.some_bind]
      apply ih (interleavedWaveState p ops input block w s) hnodup
      · intro v hv; exact hw v (by simp [hv])
      · intro v hv t ht
        have hne : v ≠ w := by intro eq; subst v; exact hnot hv
        have outside := cohort_foreign_warp block w v t (hw w (by simp)) (hw v (by simp [hv])) hne ht
        exact (interleaved_wave_other p ops input block w t s outside).1.trans (hp v (by simp [hv]) t ht)
      · exact interleaved_wave_reads p ops input block w s hr

theorem interleaved_waves_pc (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (block : Nat)
    (ws : List Nat) (s : State α) (hn : ws.Nodup) (hw : ∀ w ∈ ws, w < 4)
    (w t : Nat) (hm : w ∈ ws) (ht : t ∈ cohortThreads block w 64) :
    (interleavedWaves p ops input block ws s).pc t = 87 := by
  induction ws generalizing s with
  | nil => simp at hm
  | cons v ws ih =>
      obtain ⟨hnot, hnodup⟩ := List.nodup_cons.mp hn
      rcases List.mem_cons.mp hm with eq | hm
      · subst w
        have outside : ∀ u ∈ ws, t ∉ cohortThreads block u 64 := by
          intro u hu
          apply cohort_foreign_warp block u v t (hw u (by simp [hu])) (hw v (by simp)) ?_ ht
          intro eq; subst u; exact hnot hu
        have after := interleaved_waves_other p ops input block ws t (interleavedWaveState p ops input block v s) outside
        obtain ⟨lane, hl, rfl⟩ := (cohort_mem block v 64 t).mp ht
        exact after.1.trans (interleaved_wave_pc p ops input block v lane s hl)
      · exact ih (interleavedWaveState p ops input block v s) hnodup (by intro u hu; exact hw u (by simp [hu])) hm

theorem interleaved_waves_value (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (block : Nat)
    (ws : List Nat) (s : State α) (hn : ws.Nodup) (hw : ∀ w ∈ ws, w < 4)
    (w t e : Nat) (hm : w ∈ ws) (ht : t ∈ cohortThreads block w 64) (he : e < 4) :
    (interleavedWaves p ops input block ws s).memory (globalCell 0 (outputAddress t e)) =
      some (interleavedSourceResult ops input t e) := by
  induction ws generalizing s with
  | nil => simp at hm
  | cons v ws ih =>
      obtain ⟨hnot, hnodup⟩ := List.nodup_cons.mp hn
      rcases List.mem_cons.mp hm with eq | hm
      · subst w
        have outside : ∀ u ∈ ws, t ∉ cohortThreads block u 64 := by
          intro u hu
          apply cohort_foreign_warp block u v t (hw u (by simp [hu])) (hw v (by simp)) ?_ ht
          intro eq; subst u; exact hnot hu
        have after := interleaved_waves_memory_frame p ops input block ws (interleavedWaveState p ops input block v s)
          (globalCell 0 (outputAddress t e)) (by
            intro u hu x hx
            apply Or.inr
            change outputAddress t e / 4 ≠ x
            rw [output_owner t e he]
            intro eq; subst x; exact outside u hu hx)
        exact after.trans (interleaved_wave_global_value p ops input block v t e s (hw v (by simp)) ht he)
      · exact ih (interleavedWaveState p ops input block v s) hnodup (by intro u hu; exact hw u (by simp [hu])) hm

theorem interleaved_waves_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (block : Nat)
    (ws : List Nat) (s : State α) (good : ∀ access ∈ s.trace, Good access) :
    ∀ access ∈ (interleavedWaves p ops input block ws s).trace, Good access := by
  induction ws generalizing s with
  | nil => exact good
  | cons w ws ih => exact ih (interleavedWaveState p ops input block w s) (interleaved_wave_good p ops input block w s good)

theorem interleaved_waves_trace_length (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (block : Nat)
    (ws : List Nat) (s : State α) : (interleavedWaves p ops input block ws s).trace.length = s.trace.length + 1024 * ws.length := by
  induction ws generalizing s with
  | nil => simp [interleavedWaves]
  | cons w ws ih =>
      change (interleavedWaves p ops input block ws (interleavedWaveState p ops input block w s)).trace.length = _
      rw [ih, interleaved_wave_trace_length]
      simp only [List.length_cons]
      omega

#print axioms interleaved_waves_reads
#print axioms interleaved_waves_epochs
#print axioms interleaved_waves_other
#print axioms interleaved_waves_memory_frame
#print axioms interleaved_waves_run
#print axioms interleaved_waves_pc
#print axioms interleaved_waves_value
#print axioms interleaved_waves_good
#print axioms interleaved_waves_trace_length
end LarkNativeQKNormRope
