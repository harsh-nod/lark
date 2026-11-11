import Lark.NativeSoftmaxExpWaveFold

/-! Actual complete16-wave third block phase, from MaximumReady to the third
barrier. All1024 lanes park at PC82/epoch2 and all32 source-ordered sum partials
are retained. The third barrier has not resumed. -/
namespace LarkNativeSoftmax
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def expBlock (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row : Nat) (s : State α) : State α :=
  expWaveFold p ops input row (List.range 16) s

def expBlockPartial (ops : Ops α) (input : Nat → Nat → α) (row logicalWarp : Nat) : α :=
  sumWaveValues ops input row (logicalWarp/2) 5 ((logicalWarp%2)*32)

theorem exp_wave_entry_of_maximum (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ws : List Nat) (s : State α) (hb : ∀ w ∈ ws, w<16)
    (ready : MaximumReady p ops input row s) : ExpWaveEntry p ops input row ws s := by
  exact {
    valid := ready.valid
    pc := by
      intro w hw t ht
      exact (exp_cohort_entry_of_maximum p ops input row w s (hb w hw) ready).pc t ht
    native := by
      intro w hw t ht
      exact (exp_cohort_entry_of_maximum p ops input row w s (hb w hw) ready).native t ht
    maximum := ready.maximum
    reads := ready.reads
    epoch := by
      intro w hw t ht
      exact (exp_cohort_entry_of_maximum p ops input row w s (hb w hw) ready).epoch t ht
    good := ready.good }

theorem exp_block_fold_run (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) (ready : MaximumReady p ops input row s) :
    (List.range (((geometry p).block+(geometry p).warp-1)/(geometry p).warp)).foldlM
      (fun s w => LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel (program guarded)
        (warpThreads (geometry p) row w) fuel.warp s) s=some (expBlock p ops input row s) := by
  have hc : ((geometry p).block+(geometry p).warp-1)/(geometry p).warp=16 := by
    change (1024+64-1)/64=16
    decide
  rewrite [hc]
  exact exp_wave_fold_run p guarded ops input row (List.range 16) s List.nodup_range
    (fun _w hw => List.mem_range.mp hw)
    (exp_wave_entry_of_maximum p ops input row _ s (fun _w hw => List.mem_range.mp hw) ready)

theorem exp_block_pc (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid : Nat) (s : State α) (ht : tid<1024) : (expBlock p ops input row s).pc (row*1024+tid)=82 := by
  have h := exp_wave_fold_member_pc p ops input row (List.range 16) s List.nodup_range
    (fun _w hw => List.mem_range.mp hw) (tid/64) (tid%64)
    (List.mem_range.mpr (by omega)) (Nat.mod_lt _ (by decide))
  have he : cohortBase row (tid/64)+tid%64=row*1024+tid := by unfold cohortBase; omega
  simpa only [he] using h

theorem exp_block_epochs (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) : (expBlock p ops input row s).epochs=s.epochs :=
  exp_wave_fold_epochs p ops input row (List.range 16) s

theorem exp_block_epoch (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid : Nat) (s : State α) (ready : MaximumReady p ops input row s) (ht : tid<1024) :
    ((expBlock p ops input row s).epochs (row*1024+tid)).block=2 :=
  (congrArg (fun epochs => (epochs (row*1024+tid)).block) (exp_block_epochs p ops input row s)).trans (ready.epoch tid ht)

theorem exp_block_partial (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row logicalWarp : Nat) (s : State α) (hw : logicalWarp<32) :
    (expBlock p ops input row s).memory ⟨.shared,row,1,logicalWarp⟩=some (expBlockPartial ops input row logicalWarp) := by
  have h := exp_wave_fold_partial p ops input row (List.range 16) s List.nodup_range
    (fun _w hw => List.mem_range.mp hw) (logicalWarp/2) (logicalWarp%2)
    (List.mem_range.mpr (by omega)) (Nat.mod_lt _ (by decide))
  simpa only [show logicalWarp/2*2+logicalWarp%2=logicalWarp by omega,expBlockPartial] using h

theorem exp_block_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) (ready : MaximumReady p ops input row s) :
    ∀ a ∈ (expBlock p ops input row s).trace, Good a :=
  exp_wave_fold_good p ops input row (List.range 16) s List.nodup_range (fun _w hw => List.mem_range.mp hw)
    (exp_wave_entry_of_maximum p ops input row _ s (fun _w hw => List.mem_range.mp hw) ready)

theorem exp_block_race_free (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) (ready : MaximumReady p ops input row s) :
    raceFree (geometry p) (expBlock p ops input row s).trace=true :=
  race_free p _ (exp_block_good p ops input row s ready)

theorem exp_block_cut (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) :
    LarkCollective.converged (program guarded) (blockThreads (geometry p) row) (expBlock p ops input row s)=some .block := by
  have hs : blockThreads (geometry p) row=cohortThreads row 0 1024 := by
    simp [blockThreads,geometry,cohortThreads,cohortBase]
  rewrite [hs]
  apply (cohort_sum_partial_barrier guarded row 0 1024 _ (by decide) ?_).2
  intro tid ht
  simpa only [cohortBase,Nat.zero_mul,Nat.add_zero] using exp_block_pc p ops input row tid s ht

theorem initial_exp_block_fold (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row : Nat) (hr : row<p.rows) :
    (List.range (((geometry p).block+(geometry p).warp-1)/(geometry p).warp)).foldlM
      (fun s w => LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel (program guarded)
        (warpThreads (geometry p) row w) fuel.warp s)
      (maximumState p ops input row (initial (layout p) input outside))=
      some (expBlock p ops input row (maximumState p ops input row (initial (layout p) input outside))) :=
  exp_block_fold_run p guarded ops input row _ (initial_maximum_ready p ops input outside row hr)

#print axioms exp_wave_entry_of_maximum
#print axioms exp_block_fold_run
#print axioms exp_block_pc
#print axioms exp_block_epochs
#print axioms exp_block_epoch
#print axioms exp_block_partial
#print axioms exp_block_good
#print axioms exp_block_race_free
#print axioms exp_block_cut
#print axioms initial_exp_block_fold
end LarkNativeSoftmax
