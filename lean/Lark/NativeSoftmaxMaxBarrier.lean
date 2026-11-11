import Lark.NativeSoftmaxMaxFirstBlock

/-! Resume the actual first block barrier. Every participating PC advances to
33 and its block epoch to one; historical trace epochs and memory are unchanged.
-/
namespace LarkNativeSoftmax
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def midState (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row : Nat) (s : State α) : State α :=
  resume (blockThreads (geometry p) row) .block (firstBlock p ops input row s)

theorem block_contains (p : Shape) (row tid : Nat) (ht : tid < 1024) :
    (blockThreads (geometry p) row).contains (row * 1024 + tid) = true :=
  List.contains_iff_mem.mpr ((block_mem p row _).mpr ⟨tid, ht, rfl⟩)

theorem resume_pc_at (ts : List Nat) (s : State α) (t : Nat) (ht : ts.contains t = true) :
    (resume ts .block s).pc t = s.pc t + 1 := by simp only [resume, ht, ↓reduceIte]

theorem resume_epoch_at (ts : List Nat) (s : State α) (t : Nat) (ht : ts.contains t = true) :
    ((resume ts .block s).epochs t).block = (s.epochs t).block + 1 := by simp only [resume, ht, ↓reduceIte, bumpEpoch]

theorem block_first_eq (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row extra : Nat) (s : State α) (entry : BlockEntry p input row s) :
    LarkPartitionCollective.runBlock ops (layout p) (geometry p) fuel (program guarded) row (extra + 1) s =
      LarkPartitionCollective.runBlock ops (layout p) (geometry p) fuel (program guarded) row extra (midState p ops input row s) := by
  rewrite [LarkPartitionCollective.runBlock, first_block_fold_run p guarded ops input row s entry]
  simp only [bind, pure, Option.some_bind, first_block_cut p guarded ops input row s entry, ↓reduceIte]
  rfl

structure MidReady (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row : Nat) (s : State α) : Prop where
  valid : row < p.rows
  pc : ∀ tid, tid < 1024 → s.pc (row * 1024 + tid) = 33
  indices : ∀ tid, tid < 1024 → MaxNativeIndices (row * 1024 + tid) s
  partials : ∀ logicalWarp, logicalWarp < 32 →
    s.memory ⟨.shared, row, 0, logicalWarp⟩ = some (blockPartial ops input row logicalWarp)
  reads : Reads p input s
  epoch : ∀ tid, tid < 1024 → (s.epochs (row * 1024 + tid)).block = 1
  good : ∀ a ∈ s.trace, Good a

theorem mid_ready (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row : Nat)
    (s : State α) (entry : BlockEntry p input row s) : MidReady p ops input row (midState p ops input row s) := by
  have he := first_block_epochs p ops input row s
  exact {
    valid := entry.valid
    pc := by
      intro tid ht
      exact (resume_pc_at _ _ _ (block_contains p row tid ht)).trans
        (congrArg (· + 1) (first_block_member p ops input row tid s entry ht).pc)
    indices := fun tid ht => (first_block_member p ops input row tid s entry ht).indices
    partials := fun w hw => first_block_partial p ops input row w s hw
    reads := wave_fold_reads p ops input row (List.range 16) s entry.reads
    epoch := by
      intro tid ht
      have h := (congrArg (fun epochs => (epochs (row * 1024 + tid)).block) he).trans (entry.epoch tid ht)
      exact (resume_epoch_at _ _ _ (block_contains p row tid ht)).trans (congrArg (· + 1) h)
    good := first_block_good p ops input row s entry }

theorem initial_mid_ready (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row : Nat) (hr : row < p.rows) :
    MidReady p ops input row (midState p ops input row (initial (layout p) input outside)) :=
  mid_ready p ops input row _ (initial_block_entry p input outside row hr)

theorem initial_first_barrier (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row : Nat) (hr : row < p.rows) :
    LarkPartitionCollective.runBlock ops (layout p) (geometry p) fuel (program guarded) row fuel.block (initial (layout p) input outside) =
      LarkPartitionCollective.runBlock ops (layout p) (geometry p) fuel (program guarded) row 4
        (midState p ops input row (initial (layout p) input outside)) :=
  block_first_eq p guarded ops input row 4 _ (initial_block_entry p input outside row hr)

theorem initial_mid_race_free (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row : Nat) (hr : row < p.rows) :
    raceFree (geometry p) (midState p ops input row (initial (layout p) input outside)).trace = true :=
  race_free p _ (initial_mid_ready p ops input outside row hr).good

theorem mid_trace_length (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) :
    (midState p ops input row s).trace.length = s.trace.length+57376 :=
  first_block_trace_length p ops input row s

theorem mid_memory_frame (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) (l : Location) (hl : l.space = .global ∨ l.buffer ≠ 0) :
    (midState p ops input row s).memory l = s.memory l :=
  first_block_memory_frame p ops input row s l hl

#print axioms block_contains
#print axioms resume_pc_at
#print axioms resume_epoch_at
#print axioms block_first_eq
#print axioms mid_ready
#print axioms initial_mid_ready
#print axioms initial_first_barrier
#print axioms initial_mid_race_free
#print axioms mid_trace_length
#print axioms mid_memory_frame
end LarkNativeSoftmax
