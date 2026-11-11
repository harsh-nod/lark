import Lark.NativeSoftmaxExpBlock

/-! Actual third block barrier resume, after the complete16-wave exp/sum phase.
All lanes reach PC83/epoch3 with all32 partial sums. Serial sum and normalization
remain explicit, using the original two remaining block phases. -/
namespace LarkNativeSoftmax
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def afterExp (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row : Nat) (s : State α) : State α :=
  resume (blockThreads (geometry p) row) .block (expBlock p ops input row s)

structure ExpMidReady (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row : Nat) (s : State α) : Prop where
  valid : row<p.rows
  pc : ∀ tid, tid<1024 → s.pc (row*1024+tid)=83
  indices : ∀ tid, tid<1024 → MaxNativeIndices (row*1024+tid) s
  partials : ∀ logicalWarp, logicalWarp<32 → s.memory ⟨.shared,row,1,logicalWarp⟩=some (expBlockPartial ops input row logicalWarp)
  reads : Reads p input s
  epoch : ∀ tid, tid<1024 → (s.epochs (row*1024+tid)).block=3
  good : ∀ a ∈ s.trace, Good a

theorem after_exp_ready (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) (ready : MaximumReady p ops input row s) : ExpMidReady p ops input row (afterExp p ops input row s) := by
  exact {
    valid := ready.valid
    pc := by
      intro tid ht
      exact (resume_pc_at _ _ _ (block_contains p row tid ht)).trans
        (congrArg (·+1) (exp_block_pc p ops input row tid s ht))
    indices := by
      intro tid ht
      exact exp_wave_fold_native p ops input row (List.range 16) (row*1024+tid) s
        (fun _w hw => List.mem_range.mp hw) (ready.indices tid ht)
    partials := fun logicalWarp hw => exp_block_partial p ops input row logicalWarp s hw
    reads := exp_wave_fold_reads p ops input row (List.range 16) s ready.reads
    epoch := by
      intro tid ht
      exact (resume_epoch_at _ _ _ (block_contains p row tid ht)).trans
        (congrArg (·+1) (exp_block_epoch p ops input row tid s ready ht))
    good := exp_block_good p ops input row s ready }

theorem exp_block_step (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row extra : Nat) (s : State α) (ready : MaximumReady p ops input row s) :
    LarkPartitionCollective.runBlock ops (layout p) (geometry p) fuel (program guarded) row (extra+1) s=
      LarkPartitionCollective.runBlock ops (layout p) (geometry p) fuel (program guarded) row extra (afterExp p ops input row s) := by
  rewrite [LarkPartitionCollective.runBlock,exp_block_fold_run p guarded ops input row s ready]
  simp only [bind,pure,Option.some_bind,exp_block_cut p guarded ops input row s,↓reduceIte]
  rfl

theorem initial_exp_barrier (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row : Nat) (hr : row<p.rows) :
    LarkPartitionCollective.runBlock ops (layout p) (geometry p) fuel (program guarded) row fuel.block
      (initial (layout p) input outside)=
      LarkPartitionCollective.runBlock ops (layout p) (geometry p) fuel (program guarded) row 2
        (afterExp p ops input row (maximumState p ops input row (initial (layout p) input outside))) := by
  rewrite [initial_maximum_block p guarded ops input outside row hr]
  exact exp_block_step p guarded ops input row 2 _ (initial_maximum_ready p ops input outside row hr)

theorem initial_after_exp_ready (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row : Nat) (hr : row<p.rows) :
    ExpMidReady p ops input row (afterExp p ops input row (maximumState p ops input row (initial (layout p) input outside))) :=
  after_exp_ready p ops input row _ (initial_maximum_ready p ops input outside row hr)

theorem after_exp_race_free (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) (ready : MaximumReady p ops input row s) :
    raceFree (geometry p) (afterExp p ops input row s).trace=true := race_free p _ (after_exp_ready p ops input row s ready).good

#print axioms after_exp_ready
#print axioms exp_block_step
#print axioms initial_exp_barrier
#print axioms initial_after_exp_ready
#print axioms after_exp_race_free
end LarkNativeSoftmax
