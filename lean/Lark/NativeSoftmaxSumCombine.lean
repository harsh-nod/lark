import Lark.NativeSoftmaxSumXorState

/-! Actual post-snapshot sum and its sequential cohort fold. No algebraic
reordering is used: each lane adds its old accumulator to its selected peer.
-/
namespace LarkNativeSoftmax
open LarkNonlinear LarkCollective
open LarkReduction (setReg execute_pure_of)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def sumCombineAfter (ops : Ops α) (t pc : Nat) (a b : α) (s : State α) : State α :=
  setReg s t 6 (ops.add a b) (pc + 1)

theorem sum_combine_eq (p : Shape) (guarded : Bool) (ops : Ops α) (t pc extra : Nat) (a b : α) (s : State α)
    (hp : s.pc t = pc) (ha : s.regs t 6 = some a) (hb : s.regs t 9 = some b)
    (code : (program guarded)[pc]? = some (.scalar (.assign 6 (.bin .add (.reg 6) (.reg 9))))) :
    LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t (extra + 1) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t extra (sumCombineAfter ops t pc a b s) := by
  have he := execute_pure_of ops (layout p) (geometry p) t 6 (pc + 1)
    (.bin .add (.reg 6) (.reg 9)) s (ops.add a b)
    (by simp [evalExpr, applyBinary, ha, hb]) (by omega)
  exact scalar_step p guarded ops t pc extra _ s _ code hp he

theorem sum_combine_lane (p : Shape) (guarded : Bool) (ops : Ops α) (t pc : Nat) (a b : α) (s : State α)
    (hp : s.pc t = pc) (ha : s.regs t 6 = some a) (hb : s.regs t 9 = some b)
    (code : (program guarded)[pc]? = some (.scalar (.assign 6 (.bin .add (.reg 6) (.reg 9)))))
    (cut : LarkCollective.Cut)
    (parked : ∀ u : State α, u.pc t = pc + 1 → LarkCollective.parked (program guarded) u t = some cut) :
    LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t fuel.lane s =
      some (sumCombineAfter ops t pc a b s) := by
  change LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t (4095 + 1) s = _
  rewrite [sum_combine_eq p guarded ops t pc 4095 a b s hp ha hb code]
  have hparked := parked (sumCombineAfter ops t pc a b s) (by simp [sumCombineAfter, setReg, advance])
  simp only [LarkCollective.runLane, hparked]

theorem sum_combine_other (ops : Ops α) (t pc u : Nat) (a b : α) (s : State α) (hu : u ≠ t) :
    (sumCombineAfter ops t pc a b s).pc u = s.pc u ∧
    (sumCombineAfter ops t pc a b s).regs u = s.regs u := by
  simp [sumCombineAfter, setReg, advance, hu]

def sumCombineFold (ops : Ops α) (pc : Nat) (a b : Nat → α) (ts : List Nat) (s : State α) : State α :=
  ts.foldl (fun s t => sumCombineAfter ops t pc (a t) (b t) s) s

theorem sum_combine_fold_other (ops : Ops α) (pc : Nat) (a b : Nat → α)
    (ts : List Nat) (t : Nat) (s : State α) (ht : t ∉ ts) :
    (sumCombineFold ops pc a b ts s).pc t = s.pc t ∧ (sumCombineFold ops pc a b ts s).regs t = s.regs t := by
  induction ts generalizing s with
  | nil => exact ⟨rfl, rfl⟩
  | cons u ts ih =>
      have hne : t ≠ u := by intro he; subst t; simp at ht
      have hn : t ∉ ts := by intro hm; exact ht (by simp [hm])
      have h := ih (sumCombineAfter ops u pc (a u) (b u) s) hn
      have h1 := sum_combine_other ops u pc t (a u) (b u) s hne
      exact ⟨h.1.trans h1.1, h.2.trans h1.2⟩

theorem sum_combine_fold_preserves (ops : Ops α) (pc : Nat) (a b : Nat → α) (ts : List Nat) (s : State α) :
    (sumCombineFold ops pc a b ts s).memory = s.memory ∧
    (sumCombineFold ops pc a b ts s).indices = s.indices ∧
    (sumCombineFold ops pc a b ts s).epochs = s.epochs ∧ (sumCombineFold ops pc a b ts s).trace = s.trace := by
  induction ts generalizing s with
  | nil => exact ⟨rfl, rfl, rfl, rfl⟩
  | cons t ts ih => exact ih (sumCombineAfter ops t pc (a t) (b t) s)

theorem sum_combine_fold_member (ops : Ops α) (pc : Nat) (a b : Nat → α)
    (ts : List Nat) (s : State α) (hn : ts.Nodup) (t : Nat) (ht : t ∈ ts) :
    (sumCombineFold ops pc a b ts s).pc t = pc + 1 ∧
    (sumCombineFold ops pc a b ts s).regs t 6 = some (ops.add (a t) (b t)) := by
  induction ts generalizing s with
  | nil => simp at ht
  | cons u ts ih =>
      obtain ⟨hnot, hnodup⟩ := List.nodup_cons.mp hn
      rcases List.mem_cons.mp ht with he | hm
      · subst t
        have h := sum_combine_fold_other ops pc a b ts u (sumCombineAfter ops u pc (a u) (b u) s) hnot
        constructor
        · simpa [sumCombineAfter, setReg, advance] using h.1
        · simpa [sumCombineAfter, setReg, advance] using congrFun h.2 6
      · exact ih (sumCombineAfter ops u pc (a u) (b u) s) hnodup hm

theorem sum_combine_fold_run (p : Shape) (guarded : Bool) (ops : Ops α) (pc : Nat) (a b : Nat → α)
    (ts : List Nat) (s : State α) (hn : ts.Nodup)
    (hp : ∀ t ∈ ts, s.pc t = pc) (ha : ∀ t ∈ ts, s.regs t 6 = some (a t))
    (hb : ∀ t ∈ ts, s.regs t 9 = some (b t))
    (code : (program guarded)[pc]? = some (.scalar (.assign 6 (.bin .add (.reg 6) (.reg 9)))))
    (cut : LarkCollective.Cut)
    (parked : ∀ (u : State α) t, t ∈ ts → u.pc t = pc + 1 → LarkCollective.parked (program guarded) u t = some cut) :
    ts.foldlM (fun s t => LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t fuel.lane s) s =
      some (sumCombineFold ops pc a b ts s) := by
  induction ts generalizing s with
  | nil => rfl
  | cons t ts ih =>
      obtain ⟨hnot, hnodup⟩ := List.nodup_cons.mp hn
      have hother : ∀ u ∈ ts, u ≠ t := by intro u hu he; subst u; exact hnot hu
      rewrite [List.foldlM_cons, sum_combine_lane p guarded ops t pc (a t) (b t) s
        (hp t (by simp)) (ha t (by simp)) (hb t (by simp)) code cut
        (fun u hu => parked u t (by simp) hu)]
      simp only [bind, Option.some_bind]
      apply ih (sumCombineAfter ops t pc (a t) (b t) s) hnodup
      · intro u hu
        exact (sum_combine_other ops t pc u (a t) (b t) s (hother u hu)).1.trans (hp u (by simp [hu]))
      · intro u hu
        exact (congrFun (sum_combine_other ops t pc u (a t) (b t) s (hother u hu)).2 6).trans (ha u (by simp [hu]))
      · intro u hu
        exact (congrFun (sum_combine_other ops t pc u (a t) (b t) s (hother u hu)).2 9).trans (hb u (by simp [hu]))
      · intro u v hv hpc; exact parked u v (by simp [hv]) hpc

def sumXorStep (p : Shape) (ops : Ops α) (row warp active pc distance : Nat) (values : Nat → α) (s : State α) : State α :=
  sumCombineFold ops (pc + 1)
    (fun t => values (LarkPartitionCollective.nativeLane (geometry p) t))
    (fun t => values (sumXorPeer32 (LarkPartitionCollective.nativeLane (geometry p) t) distance))
    (cohortThreads row warp active) (shuffleUpdates 9 (sumXorSnapshot p row warp active distance values) s)

theorem sum_xor_step_run (p : Shape) (guarded : Bool) (ops : Ops α) (row warp active pc distance : Nat) (values : Nat → α)
    (s : State α) (hw : warp < 16) (ha : active = 32 ∨ active = 64) (hm : distance < 32)
    (hp : ∀ lane, lane < active → s.pc (cohortBase row warp + lane) = pc)
    (hr : ∀ lane, lane < active → s.regs (cohortBase row warp + lane) 6 = some (values lane))
    (shuffleCode : (program guarded)[pc]? = some (.shuffle .xor 9 6 (.const (distance : Int)) 32))
    (combineCode : (program guarded)[pc + 1]? = some (.scalar (.assign 6 (.bin .add (.reg 6) (.reg 9)))))
    (parked : ∀ (u : State α) t, t ∈ cohortThreads row warp active → u.pc t = pc + 2 →
      LarkCollective.parked (program guarded) u t = some .shuffle) :
    ((LarkPartitionCollective.runShuffle (geometry p) (program guarded) (cohortThreads row warp active) s).bind
      fun shuffled => (cohortThreads row warp active).foldlM
        (fun u t => LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t fuel.lane u) shuffled) =
      some (sumXorStep p ops row warp active pc distance values s) := by
  rewrite [cohort_sum_xor_shuffle p guarded row warp active distance pc s values hw ha hm hp hr shuffleCode]
  simp only [Option.some_bind]
  apply sum_combine_fold_run p guarded ops (pc + 1) _ _ _ _ (cohort_nodup row warp active) (cut := .shuffle)
  · intro t ht
    obtain ⟨lane, hl, rfl⟩ := (cohort_mem row warp active t).mp ht
    exact (sum_xor_shuffled_fields p row warp active distance lane values s hw (by omega) hl).1.trans
      (congrArg (· + 1) (hp lane hl))
  · intro t ht
    obtain ⟨lane, hl, rfl⟩ := (cohort_mem row warp active t).mp ht
    rewrite [(cohort_coords p row warp lane hw (by omega)).2]
    exact (sum_xor_shuffled_fields p row warp active distance lane values s hw (by omega) hl).2.1.trans (hr lane hl)
  · intro t ht
    obtain ⟨lane, hl, rfl⟩ := (cohort_mem row warp active t).mp ht
    rewrite [(cohort_coords p row warp lane hw (by omega)).2]
    exact (sum_xor_shuffled_fields p row warp active distance lane values s hw (by omega) hl).2.2
  · exact combineCode
  · intro u t ht hpc; exact parked u t ht (by omega)

theorem sum_xor_step_fields (p : Shape) (ops : Ops α) (row warp active pc distance lane : Nat)
    (values : Nat → α) (s : State α) (hw : warp < 16) (ha : active ≤ 64) (hl : lane < active) :
    (sumXorStep p ops row warp active pc distance values s).pc (cohortBase row warp + lane) = pc + 2 ∧
    (sumXorStep p ops row warp active pc distance values s).regs (cohortBase row warp + lane) 6 =
      some (ops.add (values lane) (values (sumXorPeer32 lane distance))) := by
  have h := sum_combine_fold_member ops (pc + 1)
    (fun t => values (LarkPartitionCollective.nativeLane (geometry p) t))
    (fun t => values (sumXorPeer32 (LarkPartitionCollective.nativeLane (geometry p) t) distance))
    (cohortThreads row warp active) (shuffleUpdates 9 (sumXorSnapshot p row warp active distance values) s)
    (cohort_nodup row warp active) _ ((cohort_mem row warp active _).mpr ⟨lane, hl, rfl⟩)
  simpa only [(cohort_coords p row warp lane hw (by omega)).2] using h

theorem sum_xor_step_preserves (p : Shape) (ops : Ops α) (row warp active pc distance : Nat)
    (values : Nat → α) (s : State α) :
    (sumXorStep p ops row warp active pc distance values s).memory = s.memory ∧
    (sumXorStep p ops row warp active pc distance values s).indices = s.indices ∧
    (sumXorStep p ops row warp active pc distance values s).epochs = s.epochs ∧
    (sumXorStep p ops row warp active pc distance values s).trace = s.trace :=
  sum_combine_fold_preserves ops (pc + 1) _ _ (cohortThreads row warp active)
    (shuffleUpdates 9 (sumXorSnapshot p row warp active distance values) s)


#print axioms sum_combine_eq
#print axioms sum_combine_lane
#print axioms sum_combine_other
#print axioms sum_combine_fold_other
#print axioms sum_combine_fold_preserves
#print axioms sum_combine_fold_member
#print axioms sum_combine_fold_run
#print axioms sum_xor_step_run
#print axioms sum_xor_step_fields
#print axioms sum_xor_step_preserves
end LarkNativeSoftmax
