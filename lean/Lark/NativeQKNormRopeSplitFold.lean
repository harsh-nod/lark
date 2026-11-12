import Lark.NativeQKNormRopeSplitLane

/-! Actual sequential physical-wave lane fold through the second source fence.
The fold preserves other lanes' normalized inputs and computed outputs. -/
namespace LarkNativeQKNormRope
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def splitRotaryFold (ops : Ops α) (input : Nat → Nat → α) (values peers : Nat → Nat → α)
    (ts : List Nat) (s : State α) : State α :=
  ts.foldl (fun s t => splitRotaryLane ops input (values t) (peers t) t s) s

theorem split_rotary_fold_preserves (ops : Ops α) (input : Nat → Nat → α) (values peers : Nat → Nat → α)
    (ts : List Nat) (s : State α) :
    (splitRotaryFold ops input values peers ts s).memory = s.memory ∧
    (splitRotaryFold ops input values peers ts s).epochs = s.epochs := by
  induction ts generalizing s with
  | nil => exact ⟨rfl, rfl⟩
  | cons t ts ih =>
      have later := ih (splitRotaryLane ops input (values t) (peers t) t s)
      have first := split_rotary_lane_preserves ops input (values t) (peers t) t s
      exact ⟨later.1.trans first.1, later.2.trans first.2⟩

theorem split_rotary_fold_other (ops : Ops α) (input : Nat → Nat → α) (values peers : Nat → Nat → α)
    (ts : List Nat) (t : Nat) (s : State α) (ht : t ∉ ts) :
    (splitRotaryFold ops input values peers ts s).pc t = s.pc t ∧
    (splitRotaryFold ops input values peers ts s).indices t = s.indices t ∧
    (splitRotaryFold ops input values peers ts s).regs t = s.regs t := by
  induction ts generalizing s with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons u ts ih =>
      have hu : t ≠ u := by intro eq; subst t; simp at ht
      have hn : t ∉ ts := by intro hm; exact ht (by simp [hm])
      have later := ih (splitRotaryLane ops input (values u) (peers u) u s) hn
      have first := split_rotary_lane_other ops input (values u) (peers u) u t s hu
      exact ⟨later.1.trans first.1, later.2.1.trans first.2.1, later.2.2.trans first.2.2⟩

theorem split_rotary_fold_index (ops : Ops α) (input : Nat → Nat → α) (values peers : Nat → Nat → α)
    (ts : List Nat) (t r : Nat) (s : State α) (hr : r < 15) :
    (splitRotaryFold ops input values peers ts s).indices t r = s.indices t r := by
  induction ts generalizing s with
  | nil => rfl
  | cons u ts ih =>
      have later := ih (splitRotaryLane ops input (values u) (peers u) u s)
      by_cases same : t = u
      · subst t; exact later.trans (split_rotary_lane_index ops input (values u) (peers u) u r s hr)
      · exact later.trans (congrFun (split_rotary_lane_other ops input (values u) (peers u) u t s same).2.1 r)

theorem split_rotary_fold_pc (ops : Ops α) (input : Nat → Nat → α) (values peers : Nat → Nat → α)
    (ts : List Nat) (s : State α) (hn : ts.Nodup) (t : Nat) (ht : t ∈ ts) :
    (splitRotaryFold ops input values peers ts s).pc t = 97 := by
  induction ts generalizing s with
  | nil => simp at ht
  | cons u ts ih =>
      obtain ⟨hnot, hnodup⟩ := List.nodup_cons.mp hn
      rcases List.mem_cons.mp ht with same | ht
      · subst t
        exact (split_rotary_fold_other ops input values peers ts u
          (splitRotaryLane ops input (values u) (peers u) u s) hnot).1.trans
          (split_rotary_lane_pc ops input (values u) (peers u) u s)
      · exact ih (splitRotaryLane ops input (values u) (peers u) u s) hnodup ht

theorem split_rotary_fold_value (ops : Ops α) (input : Nat → Nat → α) (values peers : Nat → Nat → α)
    (ts : List Nat) (s : State α) (hn : ts.Nodup) (t e : Nat) (ht : t ∈ ts) (he : e < 4) :
    (splitRotaryFold ops input values peers ts s).regs t (33 + 5 * e) =
      some (splitLaneResult ops input (values t) (peers t) t e) := by
  induction ts generalizing s with
  | nil => simp at ht
  | cons u ts ih =>
      obtain ⟨hnot, hnodup⟩ := List.nodup_cons.mp hn
      rcases List.mem_cons.mp ht with same | ht
      · subst t
        exact (congrFun (split_rotary_fold_other ops input values peers ts u
          (splitRotaryLane ops input (values u) (peers u) u s) hnot).2.2 (33 + 5 * e)).trans
          (split_rotary_lane_value ops input (values u) (peers u) u e s he)
      · exact ih (splitRotaryLane ops input (values u) (peers u) u s) hnodup ht

theorem split_rotary_fold_run (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (values peers : Nat → Nat → α)
    (ts : List Nat) (s : State α) (hn : ts.Nodup) (ht : ∀ t ∈ ts, t < p.rows * 1280)
    (hp : ∀ t ∈ ts, s.pc t = 64) (hv : ∀ t ∈ ts, SplitRotaryInputs (values t) (peers t) t s)
    (hi : ∀ t ∈ ts, NativeIndices t s) (hr : Reads p input s) :
    ts.foldlM (fun s t => LarkCollective.runLane ops (layout p) (geometry p) (program true) t fuel.lane s) s =
      some (splitRotaryFold ops input values peers ts s) := by
  induction ts generalizing s with
  | nil => rfl
  | cons t ts ih =>
      obtain ⟨hnot, hnodup⟩ := List.nodup_cons.mp hn
      have other : ∀ u ∈ ts, u ≠ t := by intro u hu eq; subst u; exact hnot hu
      rw [List.foldlM_cons, split_rotary_lane_run p ops input (values t) (peers t) t s
        (ht t (by simp)) (hp t (by simp)) (hv t (by simp)) (hi t (by simp)) hr]
      simp only [bind, Option.some_bind]
      apply ih (splitRotaryLane ops input (values t) (peers t) t s) hnodup
      · intro u hu; exact ht u (by simp [hu])
      · intro u hu
        exact (split_rotary_lane_other ops input (values t) (peers t) t u s (other u hu)).1.trans (hp u (by simp [hu]))
      · intro u hu
        simpa only [SplitRotaryInputs,
          (split_rotary_lane_other ops input (values t) (peers t) t u s (other u hu)).2.2] using hv u (by simp [hu])
      · intro u hu
        simpa only [NativeIndices,
          (split_rotary_lane_other ops input (values t) (peers t) t u s (other u hu)).2.1] using hi u (by simp [hu])
      · simpa only [Reads, (split_rotary_lane_preserves ops input (values t) (peers t) t s).1] using hr

theorem split_rotary_fold_trace_length (ops : Ops α) (input : Nat → Nat → α) (values peers : Nat → Nat → α)
    (ts : List Nat) (s : State α) :
    (splitRotaryFold ops input values peers ts s).trace.length = s.trace.length + 8 * ts.length := by
  induction ts generalizing s with
  | nil => simp [splitRotaryFold]
  | cons t ts ih =>
      change (splitRotaryFold ops input values peers ts (splitRotaryLane ops input (values t) (peers t) t s)).trace.length = _
      rw [ih, split_rotary_lane_trace_length]
      simp only [List.length_cons]
      omega

theorem split_rotary_fold_good (ops : Ops α) (input : Nat → Nat → α) (values peers : Nat → Nat → α)
    (ts : List Nat) (s : State α) (good : ∀ a ∈ s.trace, Good a) :
    ∀ a ∈ (splitRotaryFold ops input values peers ts s).trace, Good a := by
  induction ts generalizing s with
  | nil => exact good
  | cons t ts ih =>
      exact ih (splitRotaryLane ops input (values t) (peers t) t s)
        (split_rotary_lane_good ops input (values t) (peers t) t s good)

#print axioms split_rotary_fold_preserves
#print axioms split_rotary_fold_other
#print axioms split_rotary_fold_index
#print axioms split_rotary_fold_pc
#print axioms split_rotary_fold_value
#print axioms split_rotary_fold_run
#print axioms split_rotary_fold_trace_length
#print axioms split_rotary_fold_good
end LarkNativeQKNormRope
