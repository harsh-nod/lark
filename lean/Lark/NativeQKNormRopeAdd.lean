import Lark.NativeQKNormRopeXorState

/-! Actual post-snapshot accumulator addition and its sequential lane fold. -/
namespace LarkNativeQKNormRope
open LarkNonlinear LarkCollective
open LarkReduction (setReg execute_pure_of)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def addAfter (ops : Ops α) (t pc : Nat) (a b : α) (s : State α) : State α :=
  setReg s t 4 (ops.add a b) (pc + 1)

theorem add_eq (p : Shape) (neox : Bool) (ops : Ops α) (t pc extra : Nat) (a b : α) (s : State α)
    (hp : s.pc t = pc) (ha : s.regs t 4 = some a) (hb : s.regs t 9 = some b)
    (code : (program neox)[pc]? = some (.scalar (.assign 4 (.bin .add (.reg 4) (.reg 9))))) :
    LarkCollective.runLane ops (layout p) (geometry p) (program neox) t (extra + 1) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program neox) t extra (addAfter ops t pc a b s) := by
  have he := execute_pure_of ops (layout p) (geometry p) t 4 (pc + 1)
    (.bin .add (.reg 4) (.reg 9)) s (ops.add a b)
    (by simp [evalExpr, applyBinary, ha, hb]) (by omega)
  exact scalar_step p neox ops t pc extra _ s _ code hp he

theorem add_lane (p : Shape) (neox : Bool) (ops : Ops α) (t pc : Nat) (a b : α) (s : State α)
    (hp : s.pc t = pc) (ha : s.regs t 4 = some a) (hb : s.regs t 9 = some b)
    (code : (program neox)[pc]? = some (.scalar (.assign 4 (.bin .add (.reg 4) (.reg 9)))))
    (cut : LarkCollective.Cut)
    (parked : ∀ u : State α, u.pc t = pc + 1 → LarkCollective.parked (program neox) u t = some cut) :
    LarkCollective.runLane ops (layout p) (geometry p) (program neox) t fuel.lane s =
      some (addAfter ops t pc a b s) := by
  change LarkCollective.runLane _ _ _ _ _ (255 + 1) s = _
  rw [add_eq p neox ops t pc 255 a b s hp ha hb code]
  have hparked := parked (addAfter ops t pc a b s) (by simp [addAfter, setReg, advance])
  simp only [LarkCollective.runLane, hparked]

theorem add_other (ops : Ops α) (t pc u : Nat) (a b : α) (s : State α) (hu : u ≠ t) :
    (addAfter ops t pc a b s).pc u = s.pc u ∧ (addAfter ops t pc a b s).regs u = s.regs u := by
  simp [addAfter, setReg, advance, hu]

def addFold (ops : Ops α) (pc : Nat) (a b : Nat → α) (ts : List Nat) (s : State α) : State α :=
  ts.foldl (fun s t => addAfter ops t pc (a t) (b t) s) s

theorem add_fold_other (ops : Ops α) (pc : Nat) (a b : Nat → α) (ts : List Nat)
    (t : Nat) (s : State α) (ht : t ∉ ts) :
    (addFold ops pc a b ts s).pc t = s.pc t ∧ (addFold ops pc a b ts s).regs t = s.regs t := by
  induction ts generalizing s with
  | nil => exact ⟨rfl, rfl⟩
  | cons u ts ih =>
      have hne : t ≠ u := by intro he; subst t; simp at ht
      have hn : t ∉ ts := by intro hm; exact ht (by simp [hm])
      have h := ih (addAfter ops u pc (a u) (b u) s) hn
      have first := add_other ops u pc t (a u) (b u) s hne
      exact ⟨h.1.trans first.1, h.2.trans first.2⟩

theorem add_fold_preserves (ops : Ops α) (pc : Nat) (a b : Nat → α) (ts : List Nat) (s : State α) :
    (addFold ops pc a b ts s).memory = s.memory ∧ (addFold ops pc a b ts s).indices = s.indices ∧
    (addFold ops pc a b ts s).epochs = s.epochs ∧ (addFold ops pc a b ts s).trace = s.trace := by
  induction ts generalizing s with
  | nil => exact ⟨rfl, rfl, rfl, rfl⟩
  | cons t ts ih => exact ih (addAfter ops t pc (a t) (b t) s)

theorem add_fold_reg (ops : Ops α) (pc : Nat) (a b : Nat → α) (ts : List Nat)
    (t r : Nat) (s : State α) (hr : r ≠ 4) : (addFold ops pc a b ts s).regs t r = s.regs t r := by
  induction ts generalizing s with
  | nil => rfl
  | cons u ts ih =>
      exact (ih (addAfter ops u pc (a u) (b u) s)).trans (by simp [addAfter, setReg, advance, hr])

theorem add_fold_member (ops : Ops α) (pc : Nat) (a b : Nat → α) (ts : List Nat)
    (s : State α) (hn : ts.Nodup) (t : Nat) (ht : t ∈ ts) :
    (addFold ops pc a b ts s).pc t = pc + 1 ∧
    (addFold ops pc a b ts s).regs t 4 = some (ops.add (a t) (b t)) := by
  induction ts generalizing s with
  | nil => simp at ht
  | cons u ts ih =>
      obtain ⟨hnot, hnodup⟩ := List.nodup_cons.mp hn
      rcases List.mem_cons.mp ht with he | ht
      · subst t
        have h := add_fold_other ops pc a b ts u (addAfter ops u pc (a u) (b u) s) hnot
        constructor
        · simpa [addAfter, setReg, advance] using h.1
        · simpa [addAfter, setReg, advance] using congrFun h.2 4
      · exact ih (addAfter ops u pc (a u) (b u) s) hnodup ht

theorem add_fold_run (p : Shape) (neox : Bool) (ops : Ops α) (pc : Nat) (a b : Nat → α)
    (ts : List Nat) (s : State α) (hn : ts.Nodup) (hp : ∀ t ∈ ts, s.pc t = pc)
    (ha : ∀ t ∈ ts, s.regs t 4 = some (a t)) (hb : ∀ t ∈ ts, s.regs t 9 = some (b t))
    (code : (program neox)[pc]? = some (.scalar (.assign 4 (.bin .add (.reg 4) (.reg 9)))))
    (cut : LarkCollective.Cut)
    (parked : ∀ (u : State α) t, t ∈ ts → u.pc t = pc + 1 → LarkCollective.parked (program neox) u t = some cut) :
    ts.foldlM (fun s t => LarkCollective.runLane ops (layout p) (geometry p) (program neox) t fuel.lane s) s =
      some (addFold ops pc a b ts s) := by
  induction ts generalizing s with
  | nil => rfl
  | cons t ts ih =>
      obtain ⟨hnot, hnodup⟩ := List.nodup_cons.mp hn
      have hother : ∀ u ∈ ts, u ≠ t := by intro u hu he; subst u; exact hnot hu
      rw [List.foldlM_cons, add_lane p neox ops t pc (a t) (b t) s
        (hp t (by simp)) (ha t (by simp)) (hb t (by simp)) code cut
        (fun u hu => parked u t (by simp) hu)]
      simp only [bind, Option.some_bind]
      apply ih (addAfter ops t pc (a t) (b t) s) hnodup
      · intro u hu; exact (add_other ops t pc u (a t) (b t) s (hother u hu)).1.trans (hp u (by simp [hu]))
      · intro u hu; exact (congrFun (add_other ops t pc u (a t) (b t) s (hother u hu)).2 4).trans (ha u (by simp [hu]))
      · intro u hu; exact (congrFun (add_other ops t pc u (a t) (b t) s (hother u hu)).2 9).trans (hb u (by simp [hu]))
      · intro u v hv hpc; exact parked u v (by simp [hv]) hpc

def xorStep (p : Shape) (ops : Ops α) (block warp active pc mask : Nat) (values : Nat → α) (s : State α) : State α :=
  addFold ops (pc + 1)
    (fun t => values (LarkPartitionCollective.nativeLane (geometry p) t))
    (fun t => values (xorPeer32 (LarkPartitionCollective.nativeLane (geometry p) t) mask))
    (cohortThreads block warp active) (shuffleUpdates 9 (xorSnapshot p block warp active mask values) s)

theorem xor_step_run (p : Shape) (neox : Bool) (ops : Ops α) (block warp active pc mask : Nat)
    (values : Nat → α) (s : State α) (hw : warp < 4) (ha : active = 32 ∨ active = 64) (hm : mask < 32)
    (hp : ∀ lane, lane < active → s.pc (cohortBase block warp + lane) = pc)
    (hr : ∀ lane, lane < active → s.regs (cohortBase block warp + lane) 4 = some (values lane))
    (shuffleCode : (program neox)[pc]? = some (.shuffle .xor 9 4 (.const (mask : Int)) 32))
    (addCode : (program neox)[pc + 1]? = some (.scalar (.assign 4 (.bin .add (.reg 4) (.reg 9)))))
    (parked : ∀ (u : State α) t, t ∈ cohortThreads block warp active → u.pc t = pc + 2 →
      LarkCollective.parked (program neox) u t = some .shuffle) :
    ((LarkPartitionCollective.runShuffle (geometry p) (program neox) (cohortThreads block warp active) s).bind
      fun shuffled => (cohortThreads block warp active).foldlM
        (fun u t => LarkCollective.runLane ops (layout p) (geometry p) (program neox) t fuel.lane u) shuffled) =
      some (xorStep p ops block warp active pc mask values s) := by
  rw [cohort_xor_shuffle p neox block warp active mask pc 9 4 s values hw ha hm hp hr shuffleCode]
  simp only [Option.some_bind]
  apply add_fold_run p neox ops (pc + 1) _ _ _ _ (cohort_nodup block warp active) (cut := .shuffle)
  · intro t ht
    obtain ⟨lane, hl, rfl⟩ := (cohort_mem block warp active t).mp ht
    exact (xor_shuffled_fields p block warp active mask lane 9 values s hw (by omega) hl).1.trans
      (congrArg (· + 1) (hp lane hl))
  · intro t ht
    obtain ⟨lane, hl, rfl⟩ := (cohort_mem block warp active t).mp ht
    rw [xor_shuffled_reg p block warp active mask 9 _ 4 values s (by decide),
      (cohort_coords p block warp lane hw (by omega)).2]
    exact hr lane hl
  · intro t ht
    obtain ⟨lane, hl, rfl⟩ := (cohort_mem block warp active t).mp ht
    rw [(cohort_coords p block warp lane hw (by omega)).2]
    exact (xor_shuffled_fields p block warp active mask lane 9 values s hw (by omega) hl).2
  · exact addCode
  · intro u t ht hpc; exact parked u t ht (by omega)

theorem xor_step_fields (p : Shape) (ops : Ops α) (block warp active pc mask lane : Nat)
    (values : Nat → α) (s : State α) (hw : warp < 4) (ha : active ≤ 64) (hl : lane < active) :
    (xorStep p ops block warp active pc mask values s).pc (cohortBase block warp + lane) = pc + 2 ∧
    (xorStep p ops block warp active pc mask values s).regs (cohortBase block warp + lane) 4 =
      some (ops.add (values lane) (values (xorPeer32 lane mask))) := by
  have h := add_fold_member ops (pc + 1)
    (fun t => values (LarkPartitionCollective.nativeLane (geometry p) t))
    (fun t => values (xorPeer32 (LarkPartitionCollective.nativeLane (geometry p) t) mask))
    (cohortThreads block warp active) (shuffleUpdates 9 (xorSnapshot p block warp active mask values) s)
    (cohort_nodup block warp active) _ ((cohort_mem block warp active _).mpr ⟨lane, hl, rfl⟩)
  simpa only [(cohort_coords p block warp lane hw (by omega)).2] using h

theorem xor_step_preserves (p : Shape) (ops : Ops α) (block warp active pc mask : Nat)
    (values : Nat → α) (s : State α) :
    (xorStep p ops block warp active pc mask values s).memory = s.memory ∧
    (xorStep p ops block warp active pc mask values s).indices = s.indices ∧
    (xorStep p ops block warp active pc mask values s).epochs = s.epochs ∧
    (xorStep p ops block warp active pc mask values s).trace = s.trace :=
  add_fold_preserves ops (pc + 1) _ _ (cohortThreads block warp active) _

theorem xor_step_input_reg (p : Shape) (ops : Ops α) (block warp active pc mask t r : Nat)
    (values : Nat → α) (s : State α) (hr : r < 4) :
    (xorStep p ops block warp active pc mask values s).regs t r = s.regs t r := by
  unfold xorStep
  rw [add_fold_reg ops (pc + 1) _ _ _ t r _ (by omega),
    xor_shuffled_reg p block warp active mask 9 t r values s (by omega)]

#print axioms add_eq
#print axioms add_lane
#print axioms add_other
#print axioms add_fold_other
#print axioms add_fold_preserves
#print axioms add_fold_reg
#print axioms add_fold_member
#print axioms add_fold_run
#print axioms xor_step_run
#print axioms xor_step_fields
#print axioms xor_step_preserves
#print axioms xor_step_input_reg
end LarkNativeQKNormRope
