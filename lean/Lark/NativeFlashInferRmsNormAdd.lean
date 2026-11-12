import Lark.NativeFlashInferRmsNormXorState

/-! Actual post-snapshot add and its sequential cohort fold. No algebraic
reordering is used: each lane adds its old accumulator to its selected peer.
-/
namespace LarkNativeFlashInferRmsNorm
open LarkNonlinear LarkCollective
open LarkReduction (setReg execute_pure_of)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def addAfter (ops : Ops α) (t pc : Nat) (a b : α) (s : State α) : State α :=
  setReg s t 0 (ops.add a b) (pc + 1)

theorem add_eq (p : Shape) (ops : Ops α) (t pc extra : Nat) (a b : α) (s : State α)
    (hp : s.pc t = pc) (ha : s.regs t 0 = some a) (hb : s.regs t 1 = some b)
    (code : program[pc]? = some (.scalar (.assign 0 (.bin .add (.reg 0) (.reg 1))))) :
    LarkCollective.runLane ops (layout p) (geometry p) program t (extra + 1) s =
      LarkCollective.runLane ops (layout p) (geometry p) program t extra (addAfter ops t pc a b s) := by
  have he := execute_pure_of ops (layout p) (geometry p) t 0 (pc + 1)
    (.bin .add (.reg 0) (.reg 1)) s (ops.add a b)
    (by simp [evalExpr, applyBinary, ha, hb]) (by omega)
  exact scalar_step p ops t pc extra _ s _ code hp he

theorem add_lane (p : Shape) (ops : Ops α) (t pc : Nat) (a b : α) (s : State α)
    (hp : s.pc t = pc) (ha : s.regs t 0 = some a) (hb : s.regs t 1 = some b)
    (code : program[pc]? = some (.scalar (.assign 0 (.bin .add (.reg 0) (.reg 1)))))
    (cut : LarkCollective.Cut)
    (parked : ∀ u : State α, u.pc t = pc + 1 → LarkCollective.parked program u t = some cut) :
    LarkCollective.runLane ops (layout p) (geometry p) program t fuel.lane s =
      some (addAfter ops t pc a b s) := by
  change LarkCollective.runLane ops (layout p) (geometry p) program t (511 + 1) s = _
  rewrite [add_eq p ops t pc 511 a b s hp ha hb code]
  have hparked := parked (addAfter ops t pc a b s) (by simp [addAfter, setReg, advance])
  simp only [LarkCollective.runLane, hparked]

theorem add_other (ops : Ops α) (t pc u : Nat) (a b : α) (s : State α) (hu : u ≠ t) :
    (addAfter ops t pc a b s).pc u = s.pc u ∧
    (addAfter ops t pc a b s).regs u = s.regs u := by
  simp [addAfter, setReg, advance, hu]

def addFold (ops : Ops α) (pc : Nat) (a b : Nat → α) (ts : List Nat) (s : State α) : State α :=
  ts.foldl (fun s t => addAfter ops t pc (a t) (b t) s) s

theorem add_fold_other (ops : Ops α) (pc : Nat) (a b : Nat → α)
    (ts : List Nat) (t : Nat) (s : State α) (ht : t ∉ ts) :
    (addFold ops pc a b ts s).pc t = s.pc t ∧ (addFold ops pc a b ts s).regs t = s.regs t := by
  induction ts generalizing s with
  | nil => exact ⟨rfl, rfl⟩
  | cons u ts ih =>
      have hne : t ≠ u := by intro he; subst t; simp at ht
      have hn : t ∉ ts := by intro hm; exact ht (by simp [hm])
      have h := ih (addAfter ops u pc (a u) (b u) s) hn
      have h1 := add_other ops u pc t (a u) (b u) s hne
      exact ⟨h.1.trans h1.1, h.2.trans h1.2⟩

theorem add_fold_preserves (ops : Ops α) (pc : Nat) (a b : Nat → α) (ts : List Nat) (s : State α) :
    (addFold ops pc a b ts s).memory = s.memory ∧
    (addFold ops pc a b ts s).indices = s.indices ∧
    (addFold ops pc a b ts s).epochs = s.epochs ∧ (addFold ops pc a b ts s).trace = s.trace := by
  induction ts generalizing s with
  | nil => exact ⟨rfl, rfl, rfl, rfl⟩
  | cons t ts ih => exact ih (addAfter ops t pc (a t) (b t) s)

theorem add_fold_member (ops : Ops α) (pc : Nat) (a b : Nat → α)
    (ts : List Nat) (s : State α) (hn : ts.Nodup) (t : Nat) (ht : t ∈ ts) :
    (addFold ops pc a b ts s).pc t = pc + 1 ∧
    (addFold ops pc a b ts s).regs t 0 = some (ops.add (a t) (b t)) := by
  induction ts generalizing s with
  | nil => simp at ht
  | cons u ts ih =>
      obtain ⟨hnot, hnodup⟩ := List.nodup_cons.mp hn
      rcases List.mem_cons.mp ht with he | hm
      · subst t
        have h := add_fold_other ops pc a b ts u (addAfter ops u pc (a u) (b u) s) hnot
        constructor
        · simpa [addAfter, setReg, advance] using h.1
        · simpa [addAfter, setReg, advance] using congrFun h.2 0
      · exact ih (addAfter ops u pc (a u) (b u) s) hnodup hm

theorem add_fold_run (p : Shape) (ops : Ops α) (pc : Nat) (a b : Nat → α)
    (ts : List Nat) (s : State α) (hn : ts.Nodup)
    (hp : ∀ t ∈ ts, s.pc t = pc) (ha : ∀ t ∈ ts, s.regs t 0 = some (a t))
    (hb : ∀ t ∈ ts, s.regs t 1 = some (b t))
    (code : program[pc]? = some (.scalar (.assign 0 (.bin .add (.reg 0) (.reg 1)))))
    (cut : LarkCollective.Cut)
    (parked : ∀ (u : State α) t, t ∈ ts → u.pc t = pc + 1 → LarkCollective.parked program u t = some cut) :
    ts.foldlM (fun s t => LarkCollective.runLane ops (layout p) (geometry p) program t fuel.lane s) s =
      some (addFold ops pc a b ts s) := by
  induction ts generalizing s with
  | nil => rfl
  | cons t ts ih =>
      obtain ⟨hnot, hnodup⟩ := List.nodup_cons.mp hn
      have hother : ∀ u ∈ ts, u ≠ t := by intro u hu he; subst u; exact hnot hu
      rewrite [List.foldlM_cons, add_lane p ops t pc (a t) (b t) s
        (hp t (by simp)) (ha t (by simp)) (hb t (by simp)) code cut
        (fun u hu => parked u t (by simp) hu)]
      simp only [bind, Option.some_bind]
      apply ih (addAfter ops t pc (a t) (b t) s) hnodup
      · intro u hu
        exact (add_other ops t pc u (a t) (b t) s (hother u hu)).1.trans (hp u (by simp [hu]))
      · intro u hu
        exact (congrFun (add_other ops t pc u (a t) (b t) s (hother u hu)).2 0).trans (ha u (by simp [hu]))
      · intro u hu
        exact (congrFun (add_other ops t pc u (a t) (b t) s (hother u hu)).2 1).trans (hb u (by simp [hu]))
      · intro u v hv hpc; exact parked u v (by simp [hv]) hpc

def xorStep (p : Shape) (ops : Ops α) (row warp active pc mask : Nat) (values : Nat → α) (s : State α) : State α :=
  addFold ops (pc + 1)
    (fun t => values (LarkPartitionCollective.nativeLane (geometry p) t))
    (fun t => values (xorPeer32 (LarkPartitionCollective.nativeLane (geometry p) t) mask))
    (cohortThreads row warp active) (shuffleUpdates 1 (xorSnapshot p row warp active mask values) s)

theorem xor_step_run (p : Shape) (ops : Ops α) (row warp active pc mask : Nat) (values : Nat → α)
    (s : State α) (hw : warp < 16) (ha : active = 32 ∨ active = 64) (hm : mask < 32)
    (hp : ∀ lane, lane < active → s.pc (cohortBase row warp + lane) = pc)
    (hr : ∀ lane, lane < active → s.regs (cohortBase row warp + lane) 0 = some (values lane))
    (shuffleCode : program[pc]? = some (.shuffle .xor 1 0 (.const (mask : Int)) 32))
    (addCode : program[pc + 1]? = some (.scalar (.assign 0 (.bin .add (.reg 0) (.reg 1)))))
    (parked : ∀ (u : State α) t, t ∈ cohortThreads row warp active → u.pc t = pc + 2 →
      LarkCollective.parked program u t = some .shuffle) :
    ((LarkPartitionCollective.runShuffle (geometry p) program (cohortThreads row warp active) s).bind
      fun shuffled => (cohortThreads row warp active).foldlM
        (fun u t => LarkCollective.runLane ops (layout p) (geometry p) program t fuel.lane u) shuffled) =
      some (xorStep p ops row warp active pc mask values s) := by
  rewrite [cohort_xor_shuffle p row warp active mask pc s values hw ha hm hp hr shuffleCode]
  simp only [Option.some_bind]
  apply add_fold_run p ops (pc + 1) _ _ _ _ (cohort_nodup row warp active) (cut := .shuffle)
  · intro t ht
    obtain ⟨lane, hl, rfl⟩ := (cohort_mem row warp active t).mp ht
    exact (xor_shuffled_fields p row warp active mask lane values s hw (by omega) hl).1.trans
      (congrArg (· + 1) (hp lane hl))
  · intro t ht
    obtain ⟨lane, hl, rfl⟩ := (cohort_mem row warp active t).mp ht
    rewrite [(cohort_coords p row warp lane hw (by omega)).2]
    exact (xor_shuffled_fields p row warp active mask lane values s hw (by omega) hl).2.1.trans (hr lane hl)
  · intro t ht
    obtain ⟨lane, hl, rfl⟩ := (cohort_mem row warp active t).mp ht
    rewrite [(cohort_coords p row warp lane hw (by omega)).2]
    exact (xor_shuffled_fields p row warp active mask lane values s hw (by omega) hl).2.2
  · exact addCode
  · intro u t ht hpc; exact parked u t ht (by omega)

theorem xor_step_fields (p : Shape) (ops : Ops α) (row warp active pc mask lane : Nat)
    (values : Nat → α) (s : State α) (hw : warp < 16) (ha : active ≤ 64) (hl : lane < active) :
    (xorStep p ops row warp active pc mask values s).pc (cohortBase row warp + lane) = pc + 2 ∧
    (xorStep p ops row warp active pc mask values s).regs (cohortBase row warp + lane) 0 =
      some (ops.add (values lane) (values (xorPeer32 lane mask))) := by
  have h := add_fold_member ops (pc + 1)
    (fun t => values (LarkPartitionCollective.nativeLane (geometry p) t))
    (fun t => values (xorPeer32 (LarkPartitionCollective.nativeLane (geometry p) t) mask))
    (cohortThreads row warp active) (shuffleUpdates 1 (xorSnapshot p row warp active mask values) s)
    (cohort_nodup row warp active) _ ((cohort_mem row warp active _).mpr ⟨lane, hl, rfl⟩)
  simpa only [(cohort_coords p row warp lane hw (by omega)).2] using h

theorem xor_step_preserves (p : Shape) (ops : Ops α) (row warp active pc mask : Nat)
    (values : Nat → α) (s : State α) :
    (xorStep p ops row warp active pc mask values s).memory = s.memory ∧
    (xorStep p ops row warp active pc mask values s).indices = s.indices ∧
    (xorStep p ops row warp active pc mask values s).epochs = s.epochs ∧
    (xorStep p ops row warp active pc mask values s).trace = s.trace :=
  add_fold_preserves ops (pc + 1) _ _ (cohortThreads row warp active)
    (shuffleUpdates 1 (xorSnapshot p row warp active mask values) s)

#print axioms add_eq
#print axioms add_lane
#print axioms add_fold_run
#print axioms add_fold_member
#print axioms add_fold_preserves
#print axioms xor_step_run
#print axioms xor_step_fields
#print axioms xor_step_preserves
end LarkNativeFlashInferRmsNorm
