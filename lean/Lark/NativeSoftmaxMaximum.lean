import Lark.NativeSoftmaxSerialBlock

/-! Complete maximum pass from the actual initializer through both block
barriers. All lanes reach PC43/epoch2; three block phases remain explicit.
The exponentiation, sum and normalization passes are separate obligations. -/
namespace LarkNativeSoftmax
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def afterMaximum (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row : Nat) (s : State α) : State α :=
  resume (blockThreads (geometry p) row) .block (serialBlock ops input row s)

def maximumState (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row : Nat) (s : State α) : State α :=
  afterMaximum p ops input row (midState p ops input row s)

structure MaximumReady (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row : Nat) (s : State α) : Prop where
  valid : row<p.rows
  pc : ∀ tid, tid<1024 → s.pc (row*1024+tid)=43
  indices : ∀ tid, tid<1024 → MaxNativeIndices (row*1024+tid) s
  maximum : s.memory ⟨.shared,row,0,0⟩=some (rowMaximum ops input row)
  reads : Reads p input s
  epoch : ∀ tid, tid<1024 → (s.epochs (row*1024+tid)).block=2
  good : ∀ a ∈ s.trace, Good a

theorem after_maximum_ready (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row : Nat)
    (s : State α) (ready : MidReady p ops input row s) : MaximumReady p ops input row (afterMaximum p ops input row s) := by
  exact {
    valid := ready.valid
    pc := by
      intro tid ht
      exact (resume_pc_at _ _ _ (block_contains p row tid ht)).trans
        (congrArg (·+1) (serial_block_pc ops input row tid s ht))
    indices := fun tid ht => serial_block_native p ops input row tid s ready ht
    maximum := serial_block_value ops input row s
    reads := serial_block_reads p ops input row s ready.reads
    epoch := by
      intro tid ht
      have he := (congrArg (fun epochs => (epochs (row*1024+tid)).block)
        (serial_block_epochs ops input row s)).trans (ready.epoch tid ht)
      exact (resume_epoch_at _ _ _ (block_contains p row tid ht)).trans (congrArg (·+1) he)
    good := serial_block_good p ops input row s ready }

theorem maximum_ready (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row : Nat)
    (s : State α) (entry : BlockEntry p input row s) : MaximumReady p ops input row (maximumState p ops input row s) :=
  after_maximum_ready p ops input row _ (mid_ready p ops input row s entry)

theorem initial_maximum_ready (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row : Nat) (hr : row<p.rows) :
    MaximumReady p ops input row (maximumState p ops input row (initial (layout p) input outside)) :=
  maximum_ready p ops input row _ (initial_block_entry p input outside row hr)

theorem maximum_block_eq (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row extra : Nat) (s : State α) (entry : BlockEntry p input row s) :
    LarkPartitionCollective.runBlock ops (layout p) (geometry p) fuel (program guarded) row (extra+2) s =
      LarkPartitionCollective.runBlock ops (layout p) (geometry p) fuel (program guarded) row extra
        (maximumState p ops input row s) := by
  rewrite [show extra+2=(extra+1)+1 by omega,block_first_eq p guarded ops input row (extra+1) s entry]
  exact serial_block_step p guarded ops input row extra _ (mid_ready p ops input row s entry)

theorem initial_maximum_block (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row : Nat) (hr : row<p.rows) :
    LarkPartitionCollective.runBlock ops (layout p) (geometry p) fuel (program guarded) row fuel.block
      (initial (layout p) input outside) =
        LarkPartitionCollective.runBlock ops (layout p) (geometry p) fuel (program guarded) row 3
          (maximumState p ops input row (initial (layout p) input outside)) :=
  maximum_block_eq p guarded ops input row 3 _ (initial_block_entry p input outside row hr)

theorem after_maximum_trace_length (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row : Nat) (s : State α) :
    (afterMaximum p ops input row s).trace.length=s.trace.length+33 := serial_block_trace_length ops input row s

theorem maximum_trace_length (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row : Nat) (s : State α) :
    (maximumState p ops input row s).trace.length=s.trace.length+57409 := by
  have h := after_maximum_trace_length p ops input row (midState p ops input row s)
  exact h.trans (by rewrite [mid_trace_length]; omega)

theorem after_maximum_memory_frame (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) (l : Location) (hl : l.space=.global ∨ l.buffer ≠ 0) :
    (afterMaximum p ops input row s).memory l=s.memory l := by
  apply serial_block_memory_other ops input row s l
  intro h
  rcases hl with hs | hb
  · have hc := congrArg Location.space h
    simp [hs] at hc
  · exact hb (by simpa only using congrArg Location.buffer h)

theorem maximum_memory_frame (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) (l : Location) (hl : l.space=.global ∨ l.buffer ≠ 0) :
    (maximumState p ops input row s).memory l=s.memory l :=
  (after_maximum_memory_frame p ops input row _ l hl).trans (mid_memory_frame p ops input row s l hl)

theorem initial_maximum_race_free (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row : Nat) (hr : row<p.rows) :
    raceFree (geometry p) (maximumState p ops input row (initial (layout p) input outside)).trace=true :=
  race_free p _ (initial_maximum_ready p ops input outside row hr).good

#print axioms after_maximum_ready
#print axioms maximum_ready
#print axioms initial_maximum_ready
#print axioms maximum_block_eq
#print axioms initial_maximum_block
#print axioms after_maximum_trace_length
#print axioms maximum_trace_length
#print axioms after_maximum_memory_frame
#print axioms maximum_memory_frame
#print axioms initial_maximum_race_free
end LarkNativeSoftmax
