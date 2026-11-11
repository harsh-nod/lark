import Lark.NativeSoftmaxSerialWaveFold

/-! Complete actual second block phase. The serial leader reads all32 partial
maxima, writes slot zero, and every participating lane reaches PC42. -/
namespace LarkNativeSoftmax
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def rowMaximum (ops : Ops α) (input : Nat → Nat → α) (row : Nat) : α :=
  serialMaximum ops (blockPartial ops input row)

def serialBlock (ops : Ops α) (input : Nat → Nat → α) (row : Nat) (s : State α) : State α :=
  serialWaves ops (blockPartial ops input row) row (List.range 16) s

theorem serial_waves_entry_of_mid (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) (ready : MidReady p ops input row s) :
    SerialWavesEntry (blockPartial ops input row) row (List.range 16) s := by
  exact {
    pc := by
      intro w hw t ht
      obtain ⟨lane,hl,rfl⟩ := (cohort_mem row w 64 t).mp ht
      have hw := List.mem_range.mp hw
      simpa only [cohortBase,Nat.add_assoc] using ready.pc (w*64+lane) (by omega)
    native := by
      intro w hw t ht
      obtain ⟨lane,hl,rfl⟩ := (cohort_mem row w 64 t).mp ht
      have hw := List.mem_range.mp hw
      simpa only [cohortBase,Nat.add_assoc] using ready.indices (w*64+lane) (by omega)
    pending := fun _ => mid_serial_reads p ops input row s ready
    epoch := by
      intro w hw t ht
      obtain ⟨lane,hl,rfl⟩ := (cohort_mem row w 64 t).mp ht
      have hw := List.mem_range.mp hw
      simpa only [cohortBase,Nat.add_assoc] using ready.epoch (w*64+lane) (by omega)
    good := ready.good }

theorem serial_block_fold_run (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) (ready : MidReady p ops input row s) :
    (List.range (((geometry p).block+(geometry p).warp-1)/(geometry p).warp)).foldlM
      (fun s w => LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel (program guarded)
        (warpThreads (geometry p) row w) fuel.warp s) s = some (serialBlock ops input row s) := by
  have hc : ((geometry p).block+(geometry p).warp-1)/(geometry p).warp=16 := by
    change (1024+64-1)/64=16
    decide
  rewrite [hc]
  exact serial_waves_run p guarded ops (blockPartial ops input row) row _ s List.nodup_range
    (fun _w hw => List.mem_range.mp hw) (serial_waves_entry_of_mid p ops input row s ready)

theorem serial_block_pc (ops : Ops α) (input : Nat → Nat → α) (row tid : Nat) (s : State α) (ht : tid<1024) :
    (serialBlock ops input row s).pc (row*1024+tid)=42 := by
  have he : row*1024+tid=cohortBase row (tid/64)+tid%64 := by unfold cohortBase; omega
  exact serial_waves_member_pc ops (blockPartial ops input row) row _ s List.nodup_range
    (tid/64) (row*1024+tid) (List.mem_range.mpr (by omega))
    ((cohort_mem row (tid/64) 64 _).mpr ⟨tid%64,Nat.mod_lt _ (by decide),he⟩)

theorem serial_block_native (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row tid : Nat)
    (s : State α) (ready : MidReady p ops input row s) (ht : tid<1024) :
    MaxNativeIndices (row*1024+tid) (serialBlock ops input row s) :=
  serial_waves_native ops (blockPartial ops input row) row _ _ s (ready.indices tid ht)

theorem serial_block_epochs (ops : Ops α) (input : Nat → Nat → α) (row : Nat) (s : State α) :
    (serialBlock ops input row s).epochs=s.epochs := serial_waves_epochs ops (blockPartial ops input row) row _ s

theorem serial_block_value (ops : Ops α) (input : Nat → Nat → α) (row : Nat) (s : State α) :
    (serialBlock ops input row s).memory ⟨.shared,row,0,0⟩=some (rowMaximum ops input row) := by
  have h := serial_waves_value ops (blockPartial ops input row) row (List.range 16) s (by decide)
  simpa only [partialCell,show row*1024/1024=row by omega,rowMaximum] using h

theorem serial_block_trace_length (ops : Ops α) (input : Nat → Nat → α) (row : Nat) (s : State α) :
    (serialBlock ops input row s).trace.length=s.trace.length+33 := by
  have h := serial_waves_trace_length ops (blockPartial ops input row) row (List.range 16) s
  exact h.trans (by rewrite [show (List.range 16).countP (fun w => w==0)=1 by decide]; omega)

theorem serial_block_memory_other (ops : Ops α) (input : Nat → Nat → α) (row : Nat) (s : State α)
    (l : Location) (hl : l ≠ ⟨.shared,row,0,0⟩) : (serialBlock ops input row s).memory l=s.memory l := by
  apply serial_waves_memory_other ops (blockPartial ops input row) row (List.range 16) s l
  simpa only [partialCell,show row*1024/1024=row by omega] using hl

theorem serial_block_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row : Nat)
    (s : State α) (reads : Reads p input s) : Reads p input (serialBlock ops input row s) := by
  intro offset ho
  rewrite [serial_block_memory_other ops input row s _ (by
    intro h; have hs := congrArg Location.space h; simp [globalCell] at hs)]
  exact reads offset ho

theorem serial_block_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row : Nat)
    (s : State α) (ready : MidReady p ops input row s) : ∀ a ∈ (serialBlock ops input row s).trace, Good a :=
  serial_waves_good ops (blockPartial ops input row) row _ s List.nodup_range
    (serial_waves_entry_of_mid p ops input row s ready)

theorem serial_block_cut (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) :
    LarkCollective.converged (program guarded) (blockThreads (geometry p) row) (serialBlock ops input row s)=some .block := by
  have hthreads : blockThreads (geometry p) row=cohortThreads row 0 1024 := by
    simp [blockThreads,geometry,cohortThreads,cohortBase]
  rewrite [hthreads]
  apply (serial_cohort_barrier guarded row 0 1024 _ (by decide) ?_).2
  intro tid ht
  simpa only [cohortBase,Nat.zero_mul,Nat.add_zero] using serial_block_pc ops input row tid s ht

theorem serial_block_step (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row extra : Nat) (s : State α) (ready : MidReady p ops input row s) :
    LarkPartitionCollective.runBlock ops (layout p) (geometry p) fuel (program guarded) row (extra+1) s =
      LarkPartitionCollective.runBlock ops (layout p) (geometry p) fuel (program guarded) row extra
        (resume (blockThreads (geometry p) row) .block (serialBlock ops input row s)) := by
  rewrite [LarkPartitionCollective.runBlock,serial_block_fold_run p guarded ops input row s ready]
  simp only [bind,pure,Option.some_bind,serial_block_cut p guarded ops input row s,↓reduceIte]

#print axioms serial_waves_entry_of_mid
#print axioms serial_block_fold_run
#print axioms serial_block_pc
#print axioms serial_block_native
#print axioms serial_block_epochs
#print axioms serial_block_value
#print axioms serial_block_trace_length
#print axioms serial_block_memory_other
#print axioms serial_block_reads
#print axioms serial_block_good
#print axioms serial_block_cut
#print axioms serial_block_step
end LarkNativeSoftmax
