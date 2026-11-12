import Lark.NativeQKNormRopePrepare

/-! Sequential lane preparation through the actual scheduler fold. -/
namespace LarkNativeQKNormRope
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def NativeIndices (t : Nat) (s : State α) : Prop :=
  s.indices t 1 = some ((row t : Nat) : Int) ∧
  s.indices t 2 = some ((head t : Nat) : Int) ∧
  s.indices t 3 = some ((t % 32 : Nat) : Int) ∧
  s.indices t 4 = some ((column t 0 : Nat) : Int) ∧
  s.indices t 5 = some ((inputAddress t 0 : Nat) : Int) ∧
  s.indices t 6 = some ((outputAddress t 0 : Nat) : Int)

theorem prepared_indices (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) :
    NativeIndices t (prepared ops input t s) := by
  simp only [NativeIndices,
    prepared_low_indices ops input t 1 s (by decide), prepared_low_indices ops input t 2 s (by decide),
    prepared_low_indices ops input t 3 s (by decide), prepared_low_indices ops input t 4 s (by decide),
    prepared_low_indices ops input t 5 s (by decide), prepared_low_indices ops input t 6 s (by decide)]
  exact ⟨(indexed_ready t s).rowIx, (indexed_ready t s).headIx, (indexed_ready t s).laneIx,
    (indexed_ready t s).columnIx, (indexed_ready t s).inputBaseIx, (indexed_ready t s).outputBaseIx⟩

structure PrepareReady (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) : Prop where
  pc : s.pc t = 24
  values : InputValues ops input t s
  accumulator : s.regs t 4 = some (squarePrefix ops input t 4)
  indices : NativeIndices t s

theorem prepared_ready (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) :
    PrepareReady ops input t (prepared ops input t s) :=
  ⟨prepared_pc ops input t s, prepared_values ops input t s, prepared_acc ops input t s,
    prepared_indices ops input t s⟩

theorem prepared_ready_other (ops : Ops α) (input : Nat → Nat → α) (t u : Nat) (s : State α)
    (hu : u ≠ t) (ready : PrepareReady ops input u s) :
    PrepareReady ops input u (prepared ops input t s) := by
  have h := prepared_other ops input t u s hu
  refine ⟨h.1.trans ready.pc, ?_, (congrFun h.2.2 4).trans ready.accumulator, ?_⟩
  · intro e he
    exact (congrFun h.2.2 e).trans (ready.values e he)
  · simpa only [NativeIndices, h.2.1] using ready.indices

def prepareFold (ops : Ops α) (input : Nat → Nat → α) (ts : List Nat) (s : State α) : State α :=
  ts.foldl (fun s t => prepared ops input t s) s

theorem prepare_fold_preserves (ops : Ops α) (input : Nat → Nat → α) (ts : List Nat) (s : State α) :
    (prepareFold ops input ts s).memory = s.memory ∧ (prepareFold ops input ts s).epochs = s.epochs := by
  induction ts generalizing s with
  | nil => exact ⟨rfl, rfl⟩
  | cons t ts ih =>
      have h := ih (prepared ops input t s)
      have first := prepared_preserves ops input t s
      exact ⟨h.1.trans first.1, h.2.trans first.2⟩

theorem prepare_fold_other (ops : Ops α) (input : Nat → Nat → α) (ts : List Nat)
    (t : Nat) (s : State α) (ht : t ∉ ts) :
    (prepareFold ops input ts s).pc t = s.pc t ∧
    (prepareFold ops input ts s).indices t = s.indices t ∧
    (prepareFold ops input ts s).regs t = s.regs t := by
  induction ts generalizing s with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons u ts ih =>
      have hne : t ≠ u := by intro he; subst t; simp at ht
      have hn : t ∉ ts := by intro hm; exact ht (by simp [hm])
      have h := ih (prepared ops input u s) hn
      have first := prepared_other ops input u t s hne
      exact ⟨h.1.trans first.1, h.2.1.trans first.2.1, h.2.2.trans first.2.2⟩

theorem prepare_fold_ready_other (ops : Ops α) (input : Nat → Nat → α) (ts : List Nat)
    (t : Nat) (s : State α) (ht : t ∉ ts) (ready : PrepareReady ops input t s) :
    PrepareReady ops input t (prepareFold ops input ts s) := by
  have h := prepare_fold_other ops input ts t s ht
  refine ⟨h.1.trans ready.pc, ?_, (congrFun h.2.2 4).trans ready.accumulator, ?_⟩
  · intro e he; exact (congrFun h.2.2 e).trans (ready.values e he)
  · simpa only [NativeIndices, h.2.1] using ready.indices

theorem prepare_fold_member (ops : Ops α) (input : Nat → Nat → α) (ts : List Nat)
    (s : State α) (hn : ts.Nodup) (t : Nat) (ht : t ∈ ts) :
    PrepareReady ops input t (prepareFold ops input ts s) := by
  induction ts generalizing s with
  | nil => simp at ht
  | cons u ts ih =>
      obtain ⟨hnot, hnodup⟩ := List.nodup_cons.mp hn
      rcases List.mem_cons.mp ht with he | ht
      · subst t
        exact prepare_fold_ready_other ops input ts u (prepared ops input u s) hnot (prepared_ready ops input u s)
      · exact ih (prepared ops input u s) hnodup ht

theorem prepare_fold_run (p : Shape) (neox : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (ts : List Nat) (s : State α) (hn : ts.Nodup) (ht : ∀ t ∈ ts, t < p.rows * 1280)
    (hp : ∀ t ∈ ts, s.pc t = 0) (hr : Reads p input s) :
    ts.foldlM (fun s t => LarkCollective.runLane ops (layout p) (geometry p) (program neox) t fuel.lane s) s =
      some (prepareFold ops input ts s) := by
  induction ts generalizing s with
  | nil => rfl
  | cons t ts ih =>
      obtain ⟨hnot, hnodup⟩ := List.nodup_cons.mp hn
      rewrite [List.foldlM_cons, prepared_lane p neox ops input t s (ht t (by simp)) (hp t (by simp)) hr]
      simp only [bind, Option.some_bind]
      apply ih (prepared ops input t s) hnodup
      · intro u hu; exact ht u (by simp [hu])
      · intro u hu
        have hne : u ≠ t := by intro he; subst u; exact hnot hu
        exact (prepared_other ops input t u s hne).1.trans (hp u (by simp [hu]))
      · exact hr

theorem prepare_fold_good (ops : Ops α) (input : Nat → Nat → α) (ts : List Nat) (s : State α)
    (good : ∀ a ∈ s.trace, Good a) : ∀ a ∈ (prepareFold ops input ts s).trace, Good a := by
  induction ts generalizing s with
  | nil => exact good
  | cons t ts ih => exact ih (prepared ops input t s) (prepared_good ops input t s good)

theorem prepare_fold_trace_length (ops : Ops α) (input : Nat → Nat → α) (ts : List Nat) (s : State α) :
    (prepareFold ops input ts s).trace.length = s.trace.length + 4 * ts.length := by
  induction ts generalizing s with
  | nil => simp [prepareFold]
  | cons t ts ih =>
      change (prepareFold ops input ts (prepared ops input t s)).trace.length = _
      rw [ih, prepared_trace]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega

#print axioms prepared_indices
#print axioms prepared_ready
#print axioms prepared_ready_other
#print axioms prepare_fold_preserves
#print axioms prepare_fold_other
#print axioms prepare_fold_ready_other
#print axioms prepare_fold_member
#print axioms prepare_fold_run
#print axioms prepare_fold_good
#print axioms prepare_fold_trace_length
end LarkNativeQKNormRope
