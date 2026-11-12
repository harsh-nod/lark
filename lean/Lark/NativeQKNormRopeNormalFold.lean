import Lark.NativeQKNormRopeNormalLane

/-! Actual sequential lane fold from the last reduction snapshot to the first
split-half warp barrier. No synchronization is inserted into interleaved code. -/
namespace LarkNativeQKNormRope
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem normal_lane_parked (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t : Nat) (a b : α) (s : State α) (hp : s.pc t = 33)
    (ha : s.regs t 4 = some a) (hb : s.regs t 9 = some b)
    (hv : InputValues ops input t s) (hi : NativeIndices t s) (hr : Reads p input s) :
    LarkCollective.runLane ops (layout p) (geometry p) (program true) t fuel.lane s =
      some (normalLane ops input t a b s) := by
  have hs : weightSteps t ≤ 6 := by unfold weightSteps; split <;> omega
  have hc : fuel.lane = (239 - weightSteps t + 1) + (weightSteps t + 16) := by
    change 256 = _
    omega
  rw [hc, normal_lane_eq p true ops input t (239 - weightSteps t + 1) a b s hp ha hb hv hi hr]
  have hpark : LarkCollective.parked (program true) (normalLane ops input t a b s) t = some .warp := by
    simp only [LarkCollective.parked, normal_lane_pc]
    rfl
  simp only [LarkCollective.runLane, hpark]

def normalFold (ops : Ops α) (input : Nat → Nat → α) (a b : Nat → α)
    (ts : List Nat) (s : State α) : State α :=
  ts.foldl (fun s t => normalLane ops input t (a t) (b t) s) s

theorem normal_fold_preserves (ops : Ops α) (input : Nat → Nat → α) (a b : Nat → α)
    (ts : List Nat) (s : State α) :
    (normalFold ops input a b ts s).memory = s.memory ∧ (normalFold ops input a b ts s).epochs = s.epochs := by
  induction ts generalizing s with
  | nil => exact ⟨rfl, rfl⟩
  | cons t ts ih =>
      have after := ih (normalLane ops input t (a t) (b t) s)
      have first := normal_lane_preserves ops input t (a t) (b t) s
      exact ⟨after.1.trans first.1, after.2.trans first.2⟩

theorem normal_fold_other (ops : Ops α) (input : Nat → Nat → α) (a b : Nat → α)
    (ts : List Nat) (t : Nat) (s : State α) (ht : t ∉ ts) :
    (normalFold ops input a b ts s).pc t = s.pc t ∧
    (normalFold ops input a b ts s).indices t = s.indices t ∧
    (normalFold ops input a b ts s).regs t = s.regs t := by
  induction ts generalizing s with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons u ts ih =>
      have hu : t ≠ u := by intro he; subst t; simp at ht
      have hn : t ∉ ts := by intro hm; exact ht (by simp [hm])
      have after := ih (normalLane ops input u (a u) (b u) s) hn
      have first := normal_lane_other ops input u t (a u) (b u) s hu
      exact ⟨after.1.trans first.1, after.2.1.trans first.2.1, after.2.2.trans first.2.2⟩

structure NormalReady (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (a b : α) (s : State α) : Prop where
  pc : s.pc t = 59
  values : ∀ e, e < 4 → s.regs t (18 + 2 * e) =
    some (normalizedValue ops input t (weightBuffer t) (normalScale ops (ops.add a b)) e)
  indices : NativeIndices t s

theorem normal_fold_member (ops : Ops α) (input : Nat → Nat → α) (a b : Nat → α)
    (ts : List Nat) (s : State α) (hn : ts.Nodup) (t : Nat) (ht : t ∈ ts)
    (hi : ∀ u ∈ ts, NativeIndices u s) : NormalReady ops input t (a t) (b t) (normalFold ops input a b ts s) := by
  induction ts generalizing s with
  | nil => simp at ht
  | cons u ts ih =>
      obtain ⟨hnot, hnodup⟩ := List.nodup_cons.mp hn
      rcases List.mem_cons.mp ht with he | ht
      · subst t
        have later := normal_fold_other ops input a b ts u (normalLane ops input u (a u) (b u) s) hnot
        refine ⟨later.1.trans (normal_lane_pc ops input u (a u) (b u) s), ?_, ?_⟩
        · intro e he
          exact (congrFun later.2.2 (18 + 2 * e)).trans (normal_lane_value ops input u e (a u) (b u) s he)
        · change NativeIndices u (normalFold ops input a b ts (normalLane ops input u (a u) (b u) s))
          simpa only [NativeIndices, later.2.1] using normal_lane_indices ops input u (a u) (b u) s (hi u (by simp))
      · apply ih (normalLane ops input u (a u) (b u) s) hnodup ht
        intro v hv
        have hne : v ≠ u := by intro he; subst v; exact hnot hv
        have hf := normal_lane_other ops input u v (a u) (b u) s hne
        simpa only [NativeIndices, hf.2.1] using hi v (by simp [hv])

theorem normal_fold_run (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (a b : Nat → α)
    (ts : List Nat) (s : State α) (hn : ts.Nodup) (hp : ∀ t ∈ ts, s.pc t = 33)
    (ha : ∀ t ∈ ts, s.regs t 4 = some (a t)) (hb : ∀ t ∈ ts, s.regs t 9 = some (b t))
    (hv : ∀ t ∈ ts, InputValues ops input t s) (hi : ∀ t ∈ ts, NativeIndices t s) (hr : Reads p input s) :
    ts.foldlM (fun s t => LarkCollective.runLane ops (layout p) (geometry p) (program true) t fuel.lane s) s =
      some (normalFold ops input a b ts s) := by
  induction ts generalizing s with
  | nil => rfl
  | cons t ts ih =>
      obtain ⟨hnot, hnodup⟩ := List.nodup_cons.mp hn
      have hother : ∀ u ∈ ts, u ≠ t := by intro u hu he; subst u; exact hnot hu
      rw [List.foldlM_cons, normal_lane_parked p ops input t (a t) (b t) s
        (hp t (by simp)) (ha t (by simp)) (hb t (by simp)) (hv t (by simp)) (hi t (by simp)) hr]
      simp only [bind, Option.some_bind]
      apply ih (normalLane ops input t (a t) (b t) s) hnodup
      · intro u hu; exact (normal_lane_other ops input t u (a t) (b t) s (hother u hu)).1.trans (hp u (by simp [hu]))
      · intro u hu; exact (congrFun (normal_lane_other ops input t u (a t) (b t) s (hother u hu)).2.2 4).trans (ha u (by simp [hu]))
      · intro u hu; exact (congrFun (normal_lane_other ops input t u (a t) (b t) s (hother u hu)).2.2 9).trans (hb u (by simp [hu]))
      · intro u hu r hr
        exact (congrFun (normal_lane_other ops input t u (a t) (b t) s (hother u hu)).2.2 r).trans (hv u (by simp [hu]) r hr)
      · intro u hu
        have hf := normal_lane_other ops input t u (a t) (b t) s (hother u hu)
        simpa only [NativeIndices, hf.2.1] using hi u (by simp [hu])
      · simpa only [Reads, (normal_lane_preserves ops input t (a t) (b t) s).1] using hr

theorem normal_fold_good (ops : Ops α) (input : Nat → Nat → α) (a b : Nat → α)
    (ts : List Nat) (s : State α) (good : ∀ access ∈ s.trace, Good access) :
    ∀ access ∈ (normalFold ops input a b ts s).trace, Good access := by
  induction ts generalizing s with
  | nil => exact good
  | cons t ts ih => exact ih (normalLane ops input t (a t) (b t) s) (normal_lane_good ops input t (a t) (b t) s good)

theorem normal_fold_trace_length (ops : Ops α) (input : Nat → Nat → α) (a b : Nat → α)
    (ts : List Nat) (s : State α) :
    (normalFold ops input a b ts s).trace.length = s.trace.length + 4 * ts.length := by
  induction ts generalizing s with
  | nil => simp [normalFold]
  | cons t ts ih =>
      change (normalFold ops input a b ts (normalLane ops input t (a t) (b t) s)).trace.length = _
      rw [ih, normal_lane_trace]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega

#print axioms normal_lane_parked
#print axioms normal_fold_preserves
#print axioms normal_fold_other
#print axioms normal_fold_member
#print axioms normal_fold_run
#print axioms normal_fold_good
#print axioms normal_fold_trace_length
end LarkNativeQKNormRope
