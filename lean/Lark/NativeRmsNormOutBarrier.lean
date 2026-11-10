import Lark.NativeRmsNormScaleBlock

/-! The real second block barrier resumes every native thread at the output
phase and advances current block epochs from one to two. Recorded access epochs
remain attached to their original reads and writes.
-/
namespace LarkNativeRmsNorm
open LarkNonlinear
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def outState (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row : Nat) (s : State α) : State α :=
  resume (blockThreads (geometry p) row) .block (scaleBlock p ops input row s)

theorem block_second_eq (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row n : Nat) (s : State α) (ready : MidReady p ops input row s) :
    LarkPartitionCollective.runBlock ops (layout p) (geometry p) fuel program row (n + 1) s =
      LarkPartitionCollective.runBlock ops (layout p) (geometry p) fuel program row n
        (outState p ops input row s) := by
  rewrite [LarkPartitionCollective.runBlock, scale_block_fold_run p ops input row s ready]
  simp only [bind, pure, Option.some_bind, scale_block_cut p ops input row s ready, ↓reduceIte]
  rfl

structure OutReady (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row : Nat) (s : State α) : Prop where
  pc : ∀ tid, tid < 1024 → s.pc (row * 1024 + tid) = 56
  indices : ∀ tid, tid < 1024 → NativeIndices (row * 1024 + tid) s
  reads : Reads p input s
  scale : s.memory (scaleSlot row) = some (LarkNativeRmsNorm.scale ops input row)
  epoch : ∀ tid, tid < 1024 → (s.epochs (row * 1024 + tid)).block = 2
  good : ∀ access ∈ s.trace, LarkReductionFootprint.Good (traversal p) 0 access

theorem resume_pc_at (ts : List Nat) (s : State α) (t : Nat) (hc : ts.contains t = true) :
    (resume ts .block s).pc t = s.pc t + 1 := by simp only [resume, hc, ↓reduceIte]

theorem resume_indices (ts : List Nat) (s : State α) : (resume ts .block s).indices = s.indices := rfl

theorem resume_memory (ts : List Nat) (s : State α) : (resume ts .block s).memory = s.memory := rfl

theorem resume_trace (ts : List Nat) (s : State α) : (resume ts .block s).trace = s.trace := rfl

theorem resume_epoch_at (ts : List Nat) (s : State α) (t : Nat) (hc : ts.contains t = true) :
    ((resume ts .block s).epochs t).block = (s.epochs t).block + 1 := by
  simp only [resume, hc, ↓reduceIte, bumpEpoch]

theorem native_indices_of_eq (t : Nat) (s u : State α) (hi : u.indices = s.indices)
    (hn : NativeIndices t s) : NativeIndices t u := by
  simpa only [NativeIndices, hi] using hn

theorem out_ready (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row : Nat)
    (s : State α) (ready : MidReady p ops input row s) :
    OutReady p ops input row (outState p ops input row s) := by
  have hp := scale_block_preserves p ops input row s
  have hi : (outState p ops input row s).indices = s.indices :=
    (resume_indices (blockThreads (geometry p) row) (scaleBlock p ops input row s)).trans hp.1
  have hm := resume_memory (blockThreads (geometry p) row) (scaleBlock p ops input row s)
  have htrace := resume_trace (blockThreads (geometry p) row) (scaleBlock p ops input row s)
  constructor
  · intro tid ht
    exact (resume_pc_at _ (scaleBlock p ops input row s) _ (block_contains p row tid ht)).trans
      (congrArg (· + 1) (scale_block_pc p ops input row tid s ht ready))
  · intro tid ht
    exact native_indices_of_eq _ s (outState p ops input row s) hi (ready.indices tid ht)
  · exact reads_of_memory p input (scaleBlock p ops input row s) _
      (scale_block_reads p ops input row s ready.reads) hm
  · exact (congrFun hm (scaleSlot row)).trans (scale_block_value p ops input row s)
  · intro tid ht
    have he := (congrArg (fun epochs => (epochs (row * 1024 + tid)).block) hp.2).trans (ready.epoch tid ht)
    exact (resume_epoch_at _ (scaleBlock p ops input row s) _ (block_contains p row tid ht)).trans (congrArg (· + 1) he)
  · intro access ha
    exact scale_block_good p ops input row s ready access (htrace ▸ ha)

/-- Actual first and second block phases, followed by the source output phase. -/
theorem block_two_phases_eq (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row n : Nat) (hr : row < p.rows) :
    LarkPartitionCollective.runBlock ops (layout p) (geometry p) fuel program row (n + 2)
      (initial (layout p) input outside) =
    LarkPartitionCollective.runBlock ops (layout p) (geometry p) fuel program row n
      (outState p ops input row (midState p ops input row (initial (layout p) input outside))) :=
  (block_first_eq p ops input row (n + 1) _ hr (initial_reads p input outside) (by intro tid ht; rfl)).trans
    (block_second_eq p ops input row n _ (mid_ready_from_initial p ops input outside row))

#print axioms block_second_eq
#print axioms out_ready
#print axioms block_two_phases_eq
end LarkNativeRmsNorm
