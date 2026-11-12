import Lark.NativeQKNormRopeInterleavedLane

/-! Actual sequential interleaved lane completion, preserving outputs already
written by other lanes and the four read-only input buffers. -/
namespace LarkNativeQKNormRope
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def interleavedFold (ops : Ops α) (input : Nat → Nat → α) (a b : Nat → α)
    (ts : List Nat) (s : State α) : State α :=
  ts.foldl (fun s t => interleavedTail ops input t (a t) (b t) s) s

theorem interleaved_fold_epochs (ops : Ops α) (input : Nat → Nat → α) (a b : Nat → α)
    (ts : List Nat) (s : State α) : (interleavedFold ops input a b ts s).epochs = s.epochs := by
  induction ts generalizing s with
  | nil => rfl
  | cons t ts ih => exact (ih (interleavedTail ops input t (a t) (b t) s)).trans (interleaved_tail_epochs ops input t (a t) (b t) s)

theorem interleaved_fold_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (a b : Nat → α)
    (ts : List Nat) (s : State α) (hr : Reads p input s) : Reads p input (interleavedFold ops input a b ts s) := by
  induction ts generalizing s with
  | nil => exact hr
  | cons t ts ih => exact ih (interleavedTail ops input t (a t) (b t) s) (interleaved_tail_reads p ops input t (a t) (b t) s hr)

theorem interleaved_fold_other (ops : Ops α) (input : Nat → Nat → α) (a b : Nat → α)
    (ts : List Nat) (t : Nat) (s : State α) (ht : t ∉ ts) :
    (interleavedFold ops input a b ts s).pc t = s.pc t ∧
    (interleavedFold ops input a b ts s).indices t = s.indices t ∧
    (interleavedFold ops input a b ts s).regs t = s.regs t := by
  induction ts generalizing s with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons u ts ih =>
      have hu : t ≠ u := by intro he; subst t; simp at ht
      have hn : t ∉ ts := by intro hm; exact ht (by simp [hm])
      have later := ih (interleavedTail ops input u (a u) (b u) s) hn
      have first := interleaved_tail_other ops input u t (a u) (b u) s hu
      exact ⟨later.1.trans first.1, later.2.1.trans first.2.1, later.2.2.trans first.2.2⟩

theorem interleaved_fold_memory_frame (ops : Ops α) (input : Nat → Nat → α) (a b : Nat → α)
    (ts : List Nat) (s : State α) (loc : Location) (hn : ∀ t ∈ ts, loc.buffer ≠ 0 ∨ loc.offset / 4 ≠ t) :
    (interleavedFold ops input a b ts s).memory loc = s.memory loc := by
  induction ts generalizing s with
  | nil => rfl
  | cons t ts ih =>
      exact (ih (interleavedTail ops input t (a t) (b t) s) (by intro u hu; exact hn u (by simp [hu]))).trans
        (interleaved_tail_unowned ops input t (a t) (b t) s loc (hn t (by simp)))

theorem interleaved_fold_pc (ops : Ops α) (input : Nat → Nat → α) (a b : Nat → α)
    (ts : List Nat) (s : State α) (hn : ts.Nodup) (t : Nat) (ht : t ∈ ts) :
    (interleavedFold ops input a b ts s).pc t = 87 := by
  induction ts generalizing s with
  | nil => simp at ht
  | cons u ts ih =>
      obtain ⟨hnot, hnodup⟩ := List.nodup_cons.mp hn
      rcases List.mem_cons.mp ht with he | ht
      · subst t
        exact (interleaved_fold_other ops input a b ts u (interleavedTail ops input u (a u) (b u) s) hnot).1.trans
          (interleaved_tail_pc ops input u (a u) (b u) s)
      · exact ih (interleavedTail ops input u (a u) (b u) s) hnodup ht

theorem interleaved_fold_value (ops : Ops α) (input : Nat → Nat → α) (a b : Nat → α)
    (ts : List Nat) (s : State α) (hn : ts.Nodup) (t e : Nat) (ht : t ∈ ts) (he : e < 4) :
    (interleavedFold ops input a b ts s).memory (globalCell 0 (outputAddress t e)) =
      some (ops.toHalf (interleavedResult ops input t (a t) (b t) e)) := by
  induction ts generalizing s with
  | nil => simp at ht
  | cons u ts ih =>
      obtain ⟨hnot, hnodup⟩ := List.nodup_cons.mp hn
      rcases List.mem_cons.mp ht with eq | ht
      · subst t
        have after := interleaved_fold_memory_frame ops input a b ts (interleavedTail ops input u (a u) (b u) s)
          (globalCell 0 (outputAddress u e)) (by
            intro v hv
            apply Or.inr
            change outputAddress u e / 4 ≠ v
            rw [output_owner u e he]
            intro equal; subst v; exact hnot hv)
        exact after.trans (interleaved_tail_values ops input u e (a u) (b u) s he)
      · exact ih (interleavedTail ops input u (a u) (b u) s) hnodup ht

theorem interleaved_fold_run (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (a b : Nat → α)
    (ts : List Nat) (s : State α) (hn : ts.Nodup) (ht : ∀ t ∈ ts, t < p.rows * 1280)
    (hp : ∀ t ∈ ts, s.pc t = 33) (ha : ∀ t ∈ ts, s.regs t 4 = some (a t))
    (hb : ∀ t ∈ ts, s.regs t 9 = some (b t)) (hv : ∀ t ∈ ts, InputValues ops input t s)
    (hi : ∀ t ∈ ts, NativeIndices t s) (hr : Reads p input s) :
    ts.foldlM (fun s t => LarkCollective.runLane ops (layout p) (geometry p) (program false) t fuel.lane s) s =
      some (interleavedFold ops input a b ts s) := by
  induction ts generalizing s with
  | nil => rfl
  | cons t ts ih =>
      obtain ⟨hnot, hnodup⟩ := List.nodup_cons.mp hn
      have other : ∀ u ∈ ts, u ≠ t := by intro u hu eq; subst u; exact hnot hu
      rw [List.foldlM_cons, interleaved_tail_lane p ops input t (a t) (b t) s (ht t (by simp))
        (hp t (by simp)) (ha t (by simp)) (hb t (by simp)) (hv t (by simp)) (hi t (by simp)) hr]
      simp only [bind, Option.some_bind]
      apply ih (interleavedTail ops input t (a t) (b t) s) hnodup
      · intro u hu; exact ht u (by simp [hu])
      · intro u hu; exact (interleaved_tail_other ops input t u (a t) (b t) s (other u hu)).1.trans (hp u (by simp [hu]))
      · intro u hu; exact (congrFun (interleaved_tail_other ops input t u (a t) (b t) s (other u hu)).2.2 4).trans (ha u (by simp [hu]))
      · intro u hu; exact (congrFun (interleaved_tail_other ops input t u (a t) (b t) s (other u hu)).2.2 9).trans (hb u (by simp [hu]))
      · intro u hu e he
        exact (congrFun (interleaved_tail_other ops input t u (a t) (b t) s (other u hu)).2.2 e).trans (hv u (by simp [hu]) e he)
      · intro u hu
        have hf := interleaved_tail_other ops input t u (a t) (b t) s (other u hu)
        simpa only [NativeIndices, hf.2.1] using hi u (by simp [hu])
      · exact interleaved_tail_reads p ops input t (a t) (b t) s hr

theorem interleaved_fold_good (ops : Ops α) (input : Nat → Nat → α) (a b : Nat → α)
    (ts : List Nat) (s : State α) (good : ∀ access ∈ s.trace, Good access) :
    ∀ access ∈ (interleavedFold ops input a b ts s).trace, Good access := by
  induction ts generalizing s with
  | nil => exact good
  | cons t ts ih => exact ih (interleavedTail ops input t (a t) (b t) s) (interleaved_tail_good ops input t (a t) (b t) s good)

theorem interleaved_fold_trace_length (ops : Ops α) (input : Nat → Nat → α) (a b : Nat → α)
    (ts : List Nat) (s : State α) : (interleavedFold ops input a b ts s).trace.length = s.trace.length + 12 * ts.length := by
  induction ts generalizing s with
  | nil => simp [interleavedFold]
  | cons t ts ih =>
      change (interleavedFold ops input a b ts (interleavedTail ops input t (a t) (b t) s)).trace.length = _
      rw [ih, interleaved_tail_trace_length]
      simp only [List.length_cons]
      omega

#print axioms interleaved_fold_epochs
#print axioms interleaved_fold_reads
#print axioms interleaved_fold_other
#print axioms interleaved_fold_memory_frame
#print axioms interleaved_fold_pc
#print axioms interleaved_fold_value
#print axioms interleaved_fold_run
#print axioms interleaved_fold_good
#print axioms interleaved_fold_trace_length
end LarkNativeQKNormRope
