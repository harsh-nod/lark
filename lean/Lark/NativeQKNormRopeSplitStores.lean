import Lark.NativeQKNormRopeHalt

/-! Actual complete split-half output-store fold after the second warp fence.
Every lane's four results survive all later lanes' disjoint stores. -/
namespace LarkNativeQKNormRope
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def splitStoreFold (ops : Ops α) (values : Nat → Nat → α) (ts : List Nat) (s : State α) : State α :=
  ts.foldl (fun s t => storeFour ops true t (values t) s) s

theorem split_store_fold_preserves (ops : Ops α) (values : Nat → Nat → α) (ts : List Nat) (s : State α) :
    (splitStoreFold ops values ts s).regs = s.regs ∧ (splitStoreFold ops values ts s).epochs = s.epochs := by
  induction ts generalizing s with
  | nil => exact ⟨rfl, rfl⟩
  | cons t ts ih => exact ih (storeFour ops true t (values t) s)

theorem split_store_fold_other (ops : Ops α) (values : Nat → Nat → α) (ts : List Nat)
    (t : Nat) (s : State α) (ht : t ∉ ts) :
    (splitStoreFold ops values ts s).pc t = s.pc t ∧
    (splitStoreFold ops values ts s).indices t = s.indices t ∧
    (splitStoreFold ops values ts s).regs t = s.regs t := by
  induction ts generalizing s with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons u ts ih =>
      have hu : t ≠ u := by intro eq; subst t; simp at ht
      have hn : t ∉ ts := by intro hm; exact ht (by simp [hm])
      have later := ih (storeFour ops true u (values u) s) hn
      have first := store_four_other ops true u t (values u) s hu
      exact ⟨later.1.trans first.1, later.2.1.trans first.2, later.2.2⟩

theorem split_store_fold_memory_frame (ops : Ops α) (values : Nat → Nat → α) (ts : List Nat)
    (s : State α) (loc : Location) (hn : ∀ t ∈ ts, loc.buffer ≠ 0 ∨ loc.offset / 4 ≠ t) :
    (splitStoreFold ops values ts s).memory loc = s.memory loc := by
  induction ts generalizing s with
  | nil => rfl
  | cons t ts ih =>
      exact (ih (storeFour ops true t (values t) s) (by intro u hu; exact hn u (by simp [hu]))).trans
        (store_four_unowned ops true t (values t) s loc (hn t (by simp)))

theorem split_store_fold_pc (ops : Ops α) (values : Nat → Nat → α) (ts : List Nat)
    (s : State α) (hn : ts.Nodup) (t : Nat) (ht : t ∈ ts) :
    (splitStoreFold ops values ts s).pc t = 106 := by
  induction ts generalizing s with
  | nil => simp at ht
  | cons u ts ih =>
      obtain ⟨hnot, hnodup⟩ := List.nodup_cons.mp hn
      rcases List.mem_cons.mp ht with same | ht
      · subst t
        exact (split_store_fold_other ops values ts u (storeFour ops true u (values u) s) hnot).1.trans
          (store_four_pc ops true u (values u) s)
      · exact ih (storeFour ops true u (values u) s) hnodup ht

theorem split_store_fold_value (ops : Ops α) (values : Nat → Nat → α) (ts : List Nat)
    (s : State α) (hn : ts.Nodup) (t e : Nat) (ht : t ∈ ts) (he : e < 4) :
    (splitStoreFold ops values ts s).memory (globalCell 0 (outputAddress t e)) =
      some (ops.toHalf (values t e)) := by
  induction ts generalizing s with
  | nil => simp at ht
  | cons u ts ih =>
      obtain ⟨hnot, hnodup⟩ := List.nodup_cons.mp hn
      rcases List.mem_cons.mp ht with same | ht
      · subst t
        have after := split_store_fold_memory_frame ops values ts (storeFour ops true u (values u) s)
          (globalCell 0 (outputAddress u e)) (by
            intro v hv
            apply Or.inr
            change outputAddress u e / 4 ≠ v
            rw [output_owner u e he]
            intro eq; subst v; exact hnot hv)
        exact after.trans (store_four_values ops true u e (values u) s he)
      · exact ih (storeFour ops true u (values u) s) hnodup ht

theorem split_store_fold_run (p : Shape) (ops : Ops α) (values : Nat → Nat → α)
    (ts : List Nat) (s : State α) (hn : ts.Nodup) (ht : ∀ t ∈ ts, t < p.rows * 1280)
    (hp : ∀ t ∈ ts, s.pc t = 98)
    (hi : ∀ t ∈ ts, s.indices t 6 = some ((outputAddress t 0 : Nat) : Int))
    (hv : ∀ t ∈ ts, StoreValues true (values t) t s) :
    ts.foldlM (fun s t => LarkCollective.runLane ops (layout p) (geometry p) (program true) t fuel.lane s) s =
      some (splitStoreFold ops values ts s) := by
  induction ts generalizing s with
  | nil => rfl
  | cons t ts ih =>
      obtain ⟨hnot, hnodup⟩ := List.nodup_cons.mp hn
      have other : ∀ u ∈ ts, u ≠ t := by intro u hu eq; subst u; exact hnot hu
      rw [List.foldlM_cons, store_four_lane p true ops t (values t) s
        (ht t (by simp)) (hp t (by simp)) (hi t (by simp)) (hv t (by simp))]
      simp only [bind, Option.some_bind]
      apply ih (storeFour ops true t (values t) s) hnodup
      · intro u hu; exact ht u (by simp [hu])
      · intro u hu
        exact (store_four_other ops true t u (values t) s (other u hu)).1.trans (hp u (by simp [hu]))
      · intro u hu
        exact (congrFun (store_four_other ops true t u (values t) s (other u hu)).2 6).trans (hi u (by simp [hu]))
      · intro u hu; exact hv u (by simp [hu])

theorem split_store_fold_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (values : Nat → Nat → α) (ts : List Nat) (s : State α) (hr : Reads p input s) :
    Reads p input (splitStoreFold ops values ts s) := by
  induction ts generalizing s with
  | nil => exact hr
  | cons t ts ih => exact ih (storeFour ops true t (values t) s) (store_four_reads p ops input true t (values t) s hr)

theorem split_store_fold_good (ops : Ops α) (values : Nat → Nat → α) (ts : List Nat)
    (s : State α) (good : ∀ a ∈ s.trace, Good a) :
    ∀ a ∈ (splitStoreFold ops values ts s).trace, Good a := by
  induction ts generalizing s with
  | nil => exact good
  | cons t ts ih => exact ih (storeFour ops true t (values t) s) (store_four_good ops true t (values t) s good)

theorem split_store_fold_trace_length (ops : Ops α) (values : Nat → Nat → α) (ts : List Nat) (s : State α) :
    (splitStoreFold ops values ts s).trace.length = s.trace.length + 4 * ts.length := by
  induction ts generalizing s with
  | nil => simp [splitStoreFold]
  | cons t ts ih =>
      change (splitStoreFold ops values ts (storeFour ops true t (values t) s)).trace.length = _
      rw [ih, store_four_trace]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega

#print axioms split_store_fold_preserves
#print axioms split_store_fold_other
#print axioms split_store_fold_memory_frame
#print axioms split_store_fold_pc
#print axioms split_store_fold_value
#print axioms split_store_fold_run
#print axioms split_store_fold_reads
#print axioms split_store_fold_good
#print axioms split_store_fold_trace_length
end LarkNativeQKNormRope
