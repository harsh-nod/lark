import Lark.NativeRmsNormOutputOwnership

/-! Actual source-ordered output lane folds, with native writer frames. -/
namespace LarkNativeRmsNorm
open LarkNonlinear
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def outputFold (ops : Ops α) (input : Nat → Nat → α) (row : Nat) (ts : List Nat) (s : State α) : State α :=
  ts.foldl (fun s t => outputLane ops input row (t % 1024) t s) s

theorem native_thread_eq (row t : Nat) (hr : t / 1024 = row) : t = row * 1024 + t % 1024 := by
  have h := Nat.div_add_mod t 1024
  omega

theorem output_fold_epochs (ops : Ops α) (input : Nat → Nat → α) (row : Nat) (ts : List Nat) (s : State α) :
    (outputFold ops input row ts s).epochs = s.epochs := by
  induction ts generalizing s with
  | nil => rfl
  | cons t ts ih => exact (ih (outputLane ops input row (t % 1024) t s)).trans (output_lane_epochs ops input row (t % 1024) t s)

theorem output_fold_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ts : List Nat) (s : State α) (reads : Reads p input s) : Reads p input (outputFold ops input row ts s) := by
  induction ts generalizing s with
  | nil => exact reads
  | cons t ts ih => exact ih (outputLane ops input row (t % 1024) t s) (output_lane_reads p ops input row (t % 1024) t s reads)

theorem output_fold_indices (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ts : List Nat) (u : Nat) (s : State α) (hi : NativeIndices u s) :
    NativeIndices u (outputFold ops input row ts s) := by
  induction ts generalizing s with
  | nil => exact hi
  | cons t ts ih => exact ih (outputLane ops input row (t % 1024) t s) (output_lane_native_indices ops input row (t % 1024) t u s hi)

theorem output_fold_other (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ts : List Nat) (u : Nat) (s : State α) (hu : u ∉ ts) :
    (outputFold ops input row ts s).pc u = s.pc u ∧
    (outputFold ops input row ts s).indices u = s.indices u ∧
    (outputFold ops input row ts s).regs u = s.regs u := by
  induction ts generalizing s with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons t ts ih =>
      have hn : u ∉ ts := by intro h; exact hu (by simp [h])
      have he : u ≠ t := by intro h; subst u; simp at hu
      have h := ih (outputLane ops input row (t % 1024) t s) hn
      have h1 := output_lane_other ops input row (t % 1024) t u s he
      exact ⟨h.1.trans h1.1, h.2.1.trans h1.2.1, h.2.2.trans h1.2.2⟩

theorem output_fold_memory_frame (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ts : List Nat) (s : State α) (hr : ∀ t ∈ ts, t / 1024 = row)
    (l : Location) (hl : ∀ t ∈ ts, ¬ OutputOwner p t l) :
    (outputFold ops input row ts s).memory l = s.memory l := by
  induction ts generalizing s with
  | nil => rfl
  | cons t ts ih =>
      exact (ih (outputLane ops input row (t % 1024) t s) (by intro u hu; exact hr u (by simp [hu]))
        (by intro u hu; exact hl u (by simp [hu]))).trans
        (output_lane_memory_frame p ops input row (t % 1024) t s (Nat.mod_lt _ (by decide))
          (native_thread_eq row t (hr t (by simp))) l (hl t (by simp)))

theorem output_fold_pc (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ts : List Nat) (s : State α) (hn : ts.Nodup) (t : Nat) (ht : t ∈ ts) :
    (outputFold ops input row ts s).pc t = 70 := by
  induction ts generalizing s with
  | nil => simp at ht
  | cons u ts ih =>
      rcases List.nodup_cons.mp hn with ⟨hnot, hnodup⟩
      rcases List.mem_cons.mp ht with he | hm
      · subst t
        exact (output_fold_other ops input row ts u (outputLane ops input row (u % 1024) u s) hnot).1.trans
          (output_lane_pc ops input row (u % 1024) u s)
      · exact ih (outputLane ops input row (u % 1024) u s) hnodup hm

theorem output_fold_run (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ts : List Nat) (s : State α) (hn : ts.Nodup) (hr : row < p.rows)
    (ho : ∀ t ∈ ts, t / 1024 = row) (reads : Reads p input s)
    (hi : ∀ t ∈ ts, NativeIndices t s)
    (hscale : s.memory (scaleSlot row) = some (scale ops input row)) (hp : ∀ t ∈ ts, s.pc t = 56) :
    ts.foldlM (fun s t => LarkCollective.runLane ops (layout p) (geometry p) program t fuel.lane s) s =
      some (outputFold ops input row ts s) := by
  induction ts generalizing s with
  | nil => rfl
  | cons t ts ih =>
      rcases List.nodup_cons.mp hn with ⟨hnot, hnodup⟩
      have hit := hi t (by simp)
      have hrow := ho t (by simp)
      have hi0 : s.indices t 0 = some (row : Int) := by simpa only [hrow] using hit.1
      rewrite [List.foldlM_cons, output_lane_run p ops input row (t % 1024) t s reads hr
        (Nat.mod_lt _ (by decide)) hrow hi0 hit.2.1 hscale (hp t (by simp))]
      simp only [bind, Option.some_bind]
      apply ih (outputLane ops input row (t % 1024) t s) hnodup
      · intro u hu; exact ho u (by simp [hu])
      · exact output_lane_reads p ops input row (t % 1024) t s reads
      · intro u hu; exact output_lane_native_indices ops input row (t % 1024) t u s (hi u (by simp [hu]))
      · exact (output_lane_scale_frame p ops input row (t % 1024) t s (Nat.mod_lt _ (by decide))
          (native_thread_eq row t hrow)).trans hscale
      · intro u hu
        exact (output_lane_other ops input row (t % 1024) t u s (by intro he; subst u; exact hnot hu)).1.trans (hp u (by simp [hu]))

theorem output_fold_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ts : List Nat) (s : State α) (ho : ∀ t ∈ ts, t / 1024 = row)
    (he : ∀ t ∈ ts, (s.epochs t).block = 2)
    (good : ∀ a ∈ s.trace, LarkReductionFootprint.Good (traversal p) 0 a) :
    ∀ a ∈ (outputFold ops input row ts s).trace, LarkReductionFootprint.Good (traversal p) 0 a := by
  induction ts generalizing s with
  | nil => exact good
  | cons t ts ih =>
      have hp := output_lane_epochs ops input row (t % 1024) t s
      apply ih (outputLane ops input row (t % 1024) t s) (by intro u hu; exact ho u (by simp [hu]))
      · intro u hu
        exact (congrArg (fun epochs => (epochs u).block) hp).trans (he u (by simp [hu]))
      · exact output_lane_good p ops input row (t % 1024) t s (Nat.mod_lt _ (by decide))
          (native_thread_eq row t (ho t (by simp))) (ho t (by simp)) (he t (by simp)) good

theorem output_fold_value (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ts : List Nat) (s : State α) (hn : ts.Nodup) (ho : ∀ t ∈ ts, t / 1024 = row)
    (t : Nat) (ht : t ∈ ts) (l : Location) (value : α) (hl : OutputOwner p t l)
    (hv : ∀ u : State α, (outputLane ops input row (t % 1024) t u).memory l = some value) :
    (outputFold ops input row ts s).memory l = some value := by
  induction ts generalizing s with
  | nil => simp at ht
  | cons u ts ih =>
      rcases List.nodup_cons.mp hn with ⟨hnot, hnodup⟩
      rcases List.mem_cons.mp ht with he | hm
      · subst t
        exact (output_fold_memory_frame p ops input row ts (outputLane ops input row (u % 1024) u s)
          (by intro t ht; exact ho t (by simp [ht])) l
          (by intro t ht; exact output_owner_ne p u t l hl (by intro he; subst t; exact hnot ht))).trans (hv s)
      · exact ih (outputLane ops input row (u % 1024) u s) hnodup (by intro t ht; exact ho t (by simp [ht])) hm

#print axioms output_fold_run
#print axioms output_fold_value
#print axioms output_fold_good
end LarkNativeRmsNorm
