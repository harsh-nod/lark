import Lark.NativeSoftmaxExpOutput

/-! Constructive Some execution of exactly the four reduction block phases.
Each phase uses the full source program, original runWarp/lane fuel, actual
convergence test and actual barrier resume from runBlock. The continuation
lemma links successful prefixes to runBlock. Normalization is not executed. -/
namespace LarkNativeSoftmax
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def reductionPhase (p : Shape) (guarded : Bool) (ops : Ops α) (row : Nat) (s : State α) : Option (State α) := do
  let next ← (List.range (((geometry p).block+(geometry p).warp-1)/(geometry p).warp)).foldlM
    (fun s w => LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel (program guarded)
      (warpThreads (geometry p) row w) fuel.warp s) s
  let cut ← LarkCollective.converged (program guarded) (blockThreads (geometry p) row) next
  if cut=.block then some (resume (blockThreads (geometry p) row) .block next) else none

def reductionPrefix (p : Shape) (guarded : Bool) (ops : Ops α) (row : Nat) : Nat → State α → Option (State α)
  | 0,s => some s
  | count+1,s => (reductionPhase p guarded ops row s).bind (reductionPrefix p guarded ops row count)

theorem reduction_phase_of_fold (p : Shape) (guarded : Bool) (ops : Ops α) (row : Nat) (s next : State α)
    (hfold : (List.range (((geometry p).block+(geometry p).warp-1)/(geometry p).warp)).foldlM
      (fun s w => LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel (program guarded)
        (warpThreads (geometry p) row w) fuel.warp s) s=some next)
    (hcut : LarkCollective.converged (program guarded) (blockThreads (geometry p) row) next=some .block) :
    reductionPhase p guarded ops row s=some (resume (blockThreads (geometry p) row) .block next) := by
  simp only [reductionPhase,hfold,hcut,bind,pure,Option.bind,↓reduceIte]

theorem reduction_phase_continue (p : Shape) (guarded : Bool) (ops : Ops α) (row extra : Nat) (s next : State α)
    (h : reductionPhase p guarded ops row s=some next) :
    LarkPartitionCollective.runBlock ops (layout p) (geometry p) fuel (program guarded) row (extra+1) s=
      LarkPartitionCollective.runBlock ops (layout p) (geometry p) fuel (program guarded) row extra next := by
  unfold reductionPhase at h
  cases hf : (List.range (((geometry p).block+(geometry p).warp-1)/(geometry p).warp)).foldlM
    (fun s w => LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel (program guarded)
      (warpThreads (geometry p) row w) fuel.warp s) s with
  | none => simp only [hf,bind,pure,Option.bind,reduceCtorEq] at h
  | some state =>
    simp only [hf,bind,pure,Option.bind] at h
    cases hc : LarkCollective.converged (program guarded) (blockThreads (geometry p) row) state with
    | none => simp only [hc,bind,pure,Option.bind,reduceCtorEq] at h
    | some cut =>
      simp only [hc,bind,pure,Option.bind] at h
      split at h
      · rename_i he
        subst cut
        have hn : resume (blockThreads (geometry p) row) .block state=next := Option.some.inj h
        rewrite [LarkPartitionCollective.runBlock,hf]
        simp only [bind,pure,Option.some_bind,hc,↓reduceIte]
        rewrite [hn]
        rfl
      · simp only [reduceCtorEq] at h

theorem reduction_prefix_continue (p : Shape) (guarded : Bool) (ops : Ops α)
    (row count extra : Nat) (s next : State α) (h : reductionPrefix p guarded ops row count s=some next) :
    LarkPartitionCollective.runBlock ops (layout p) (geometry p) fuel (program guarded) row (extra+count) s=
      LarkPartitionCollective.runBlock ops (layout p) (geometry p) fuel (program guarded) row extra next := by
  induction count generalizing s with
  | zero =>
    have he : s=next := Option.some.inj h
    subst next
    rfl
  | succ count ih =>
    change (reductionPhase p guarded ops row s).bind (reductionPrefix p guarded ops row count)=some next at h
    cases hp : reductionPhase p guarded ops row s with
    | none => simp only [hp,Option.none_bind,reduceCtorEq] at h
    | some state =>
      simp only [hp,Option.some_bind] at h
      rewrite [show extra+(count+1)=(extra+count)+1 by omega,
        reduction_phase_continue p guarded ops row (extra+count) s state hp]
      exact ih state h

theorem reduction_first_phase (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) (entry : BlockEntry p input row s) :
    reductionPhase p guarded ops row s=some (midState p ops input row s) :=
  reduction_phase_of_fold p guarded ops row s (firstBlock p ops input row s)
    (first_block_fold_run p guarded ops input row s entry) (first_block_cut p guarded ops input row s entry)

theorem reduction_maximum_phase (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) (ready : MidReady p ops input row s) :
    reductionPhase p guarded ops row s=some (afterMaximum p ops input row s) :=
  reduction_phase_of_fold p guarded ops row s (serialBlock ops input row s)
    (serial_block_fold_run p guarded ops input row s ready) (serial_block_cut p guarded ops input row s)

theorem reduction_exp_phase (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) (ready : MaximumReady p ops input row s) :
    reductionPhase p guarded ops row s=some (afterExp p ops input row s) :=
  reduction_phase_of_fold p guarded ops row s (expBlock p ops input row s)
    (exp_block_fold_run p guarded ops input row s ready) (exp_block_cut p guarded ops input row s)

theorem reduction_sum_phase (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) (ready : ExpMidReady p ops input row s) :
    reductionPhase p guarded ops row s=some (afterSum p ops input row s) :=
  reduction_phase_of_fold p guarded ops row s (sumSerialBlock ops input row s)
    (sum_serial_block_fold_run p guarded ops input row s ready) (sum_serial_block_cut p guarded ops input row s)

theorem reduction_prefix_run (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) (entry : BlockEntry p input row s) :
    reductionPrefix p guarded ops row 4 s=some (sumState p ops input row s) := by
  have rmid := mid_ready p ops input row s entry
  have rmax := maximum_ready p ops input row s entry
  have rexp := after_exp_ready p ops input row (maximumState p ops input row s) rmax
  change ((reductionPhase p guarded ops row s).bind fun a =>
    (reductionPhase p guarded ops row a).bind fun b =>
      (reductionPhase p guarded ops row b).bind fun c =>
        (reductionPhase p guarded ops row c).bind fun d => some d)=_
  rewrite [reduction_first_phase p guarded ops input row s entry]
  simp only [Option.some_bind]
  rewrite [reduction_maximum_phase p guarded ops input row _ rmid]
  simp only [Option.some_bind]
  change ((reductionPhase p guarded ops row (maximumState p ops input row s)).bind fun c =>
    (reductionPhase p guarded ops row c).bind fun d => some d)=_
  rewrite [reduction_exp_phase p guarded ops input row _ rmax]
  simp only [Option.some_bind]
  rewrite [reduction_sum_phase p guarded ops input row _ rexp]
  rfl

theorem initial_reduction_prefix (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row : Nat) (hr : row<p.rows) :
    reductionPrefix p guarded ops row 4 (initial (layout p) input outside)=
      some (sumState p ops input row (initial (layout p) input outside)) :=
  reduction_prefix_run p guarded ops input row _ (initial_block_entry p input outside row hr)

#print axioms reduction_phase_of_fold
#print axioms reduction_phase_continue
#print axioms reduction_prefix_continue
#print axioms reduction_first_phase
#print axioms reduction_maximum_phase
#print axioms reduction_exp_phase
#print axioms reduction_sum_phase
#print axioms reduction_prefix_run
#print axioms initial_reduction_prefix
end LarkNativeSoftmax
