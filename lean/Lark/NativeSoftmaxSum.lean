import Lark.NativeSoftmaxSumSerialBlock

/-! All four actual reduction block phases, from the initializer through the
fourth barrier. The source-ordered scalar sums, logical32 XOR trees and serial32
sum are retained. All lanes reach PC93/epoch4; normalization remains explicit. -/
namespace LarkNativeSoftmax
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def afterSum (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row : Nat) (s : State α) : State α :=
  resume (blockThreads (geometry p) row) .block (sumSerialBlock ops input row s)

def sumState (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row : Nat) (s : State α) : State α :=
  afterSum p ops input row (afterExp p ops input row (maximumState p ops input row s))

structure SumReady (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row : Nat) (s : State α) : Prop where
  valid : row<p.rows
  pc : ∀ tid, tid<1024 → s.pc (row*1024+tid)=93
  indices : ∀ tid, tid<1024 → MaxNativeIndices (row*1024+tid) s
  total : s.memory ⟨.shared,row,1,0⟩=some (rowExpSum ops input row)
  reads : Reads p input s
  epoch : ∀ tid, tid<1024 → (s.epochs (row*1024+tid)).block=4
  good : ∀ a ∈ s.trace, Good a

theorem after_sum_ready (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) (ready : ExpMidReady p ops input row s) : SumReady p ops input row (afterSum p ops input row s) := by
  exact {
    valid := ready.valid
    pc := by
      intro tid ht
      exact (resume_pc_at _ _ _ (block_contains p row tid ht)).trans
        (congrArg (·+1) (sum_serial_block_pc ops input row tid s ht))
    indices := fun tid ht => sum_serial_block_native p ops input row tid s ready ht
    total := sum_serial_block_value ops input row s
    reads := sum_serial_block_reads p ops input row s ready.reads
    epoch := by
      intro tid ht
      have he := (congrArg (fun epochs => (epochs (row*1024+tid)).block)
        (sum_serial_block_epochs ops input row s)).trans (ready.epoch tid ht)
      exact (resume_epoch_at _ _ _ (block_contains p row tid ht)).trans (congrArg (·+1) he)
    good := sum_serial_block_good p ops input row s ready }

theorem sum_ready (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) (entry : BlockEntry p input row s) : SumReady p ops input row (sumState p ops input row s) :=
  after_sum_ready p ops input row _ (after_exp_ready p ops input row _ (maximum_ready p ops input row s entry))

theorem initial_sum_ready (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row : Nat) (hr : row<p.rows) :
    SumReady p ops input row (sumState p ops input row (initial (layout p) input outside)) :=
  sum_ready p ops input row _ (initial_block_entry p input outside row hr)

theorem sum_block_eq (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row extra : Nat) (s : State α) (entry : BlockEntry p input row s) :
    LarkPartitionCollective.runBlock ops (layout p) (geometry p) fuel (program guarded) row (extra+4) s=
      LarkPartitionCollective.runBlock ops (layout p) (geometry p) fuel (program guarded) row extra (sumState p ops input row s) := by
  rewrite [show extra+4=((extra+1)+1)+2 by omega,
    maximum_block_eq p guarded ops input row ((extra+1)+1) s entry]
  rewrite [exp_block_step p guarded ops input row (extra+1) _ (maximum_ready p ops input row s entry)]
  exact sum_serial_block_step p guarded ops input row extra _
    (after_exp_ready p ops input row _ (maximum_ready p ops input row s entry))

theorem initial_sum_block (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row : Nat) (hr : row<p.rows) :
    LarkPartitionCollective.runBlock ops (layout p) (geometry p) fuel (program guarded) row fuel.block
      (initial (layout p) input outside)=
      LarkPartitionCollective.runBlock ops (layout p) (geometry p) fuel (program guarded) row 1
        (sumState p ops input row (initial (layout p) input outside)) :=
  sum_block_eq p guarded ops input row 1 _ (initial_block_entry p input outside row hr)

theorem after_sum_trace_length (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) : (afterSum p ops input row s).trace.length=s.trace.length+33 :=
  sum_serial_block_trace_length ops input row s

theorem after_sum_count_of_start (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) (hstart : s.trace.length=273667) :
    (afterSum p ops input row s).trace.length=273700 :=
  exp_count_total_of_start s (afterSum p ops input row s) 273667 33 hstart (after_sum_trace_length p ops input row s)

theorem initial_sum_trace_length (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row : Nat) :
    (sumState p ops input row (initial (layout p) input outside)).trace.length=273700 :=
  after_sum_count_of_start p ops input row (afterExp p ops input row (maximumState p ops input row (initial (layout p) input outside)))
    (initial_after_exp_trace_length p ops input outside row)

theorem after_sum_memory_frame (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) (l : Location) (hl : l ≠ ⟨.shared,row,1,0⟩) :
    (afterSum p ops input row s).memory l=s.memory l := sum_serial_block_memory_other ops input row s l hl

theorem after_sum_output_frame (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row offset : Nat) (s : State α) :
    (afterSum p ops input row s).memory (globalCell 0 offset)=s.memory (globalCell 0 offset) := by
  apply after_sum_memory_frame p ops input row s (globalCell 0 offset)
  intro h
  have he := congrArg Location.space h
  simp [globalCell] at he

theorem initial_sum_race_free (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row : Nat) (hr : row<p.rows) :
    raceFree (geometry p) (sumState p ops input row (initial (layout p) input outside)).trace=true :=
  race_free p _ (initial_sum_ready p ops input outside row hr).good

#print axioms after_sum_ready
#print axioms sum_ready
#print axioms initial_sum_ready
#print axioms sum_block_eq
#print axioms initial_sum_block
#print axioms after_sum_trace_length
#print axioms after_sum_count_of_start
#print axioms initial_sum_trace_length
#print axioms after_sum_memory_frame
#print axioms after_sum_output_frame
#print axioms initial_sum_race_free
end LarkNativeSoftmax
