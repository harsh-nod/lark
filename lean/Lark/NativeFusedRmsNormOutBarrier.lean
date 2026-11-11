import Lark.NativeFusedRmsNormScaleBlock

/-! The actual second block-barrier resume. All 1024 participants enter PC51
at epoch2 with the final total, all unrounded values, rounded residuals and
read-only weights intact. The normalization/output loop remains separate work.
-/
namespace LarkNativeFusedRmsNorm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def outState (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row : Nat) (s : State α) : State α :=
  resume (blockThreads (geometry p) row) .block (scaleBlock p ops input row s)

theorem block_second_eq (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row extra : Nat) (s : State α) (ready : MidReady p ops input row s) :
    LarkPartitionCollective.runBlock ops (layout p) (geometry p) fuel program row (extra + 1) s =
      LarkPartitionCollective.runBlock ops (layout p) (geometry p) fuel program row extra (outState p ops input row s) := by
  rewrite [LarkPartitionCollective.runBlock, scale_block_fold_run p ops input row s ready]
  simp only [bind, pure, Option.some_bind, scale_block_cut p ops input row s ready, ↓reduceIte]
  rfl

structure OutReady (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row : Nat) (s : State α) : Prop where
  valid : row < p.rows
  pc : ∀ tid, tid < 1024 → s.pc (row * 1024 + tid) = 51
  indices : ∀ tid, tid < 1024 → NativeIndices (row * 1024 + tid) s
  total : s.memory (partialSlot row 0) = some (blockSum ops input row)
  cells : ∀ col, col < 16384 →
    s.memory (globalCell 1 (address row col)) = some (ops.toHalf (rowAdded ops input row col)) ∧
    s.memory ⟨.shared, row, 1, col⟩ = some (rowAdded ops input row col)
  weights : ∀ col, col < 16384 → s.memory (globalCell 2 col) = some (input 2 col)
  epoch : ∀ tid, tid < 1024 → (s.epochs (row * 1024 + tid)).block = 2
  good : ∀ a ∈ s.trace, Good a

structure ReducedReady (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row : Nat) (s : State α) : Prop where
  valid : row < p.rows
  pc : ∀ tid, tid < 1024 → s.pc (row * 1024 + tid) = 50
  indices : ∀ tid, tid < 1024 → NativeIndices (row * 1024 + tid) s
  total : s.memory (partialSlot row 0) = some (blockSum ops input row)
  cells : ∀ col, col < 16384 →
    s.memory (globalCell 1 (address row col)) = some (ops.toHalf (rowAdded ops input row col)) ∧
    s.memory ⟨.shared, row, 1, col⟩ = some (rowAdded ops input row col)
  weights : ∀ col, col < 16384 → s.memory (globalCell 2 col) = some (input 2 col)
  epoch : ∀ tid, tid < 1024 → (s.epochs (row * 1024 + tid)).block = 1
  good : ∀ a ∈ s.trace, Good a

theorem reduced_ready (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row : Nat)
    (s : State α) (ready : MidReady p ops input row s) : ReducedReady p ops input row (scaleBlock p ops input row s) := by
  have hp := scale_block_preserves p ops input row s
  exact {
    valid := ready.valid
    pc := fun tid ht => scale_block_pc p ops input row tid s ht ready
    indices := by intro tid ht; simpa only [NativeIndices, hp.1] using ready.indices tid ht
    total := scale_block_total p ops input row s
    cells := by
      intro col hc
      exact ⟨(scale_block_memory_frame p ops input row s _ (by simp [globalCell, partialSlot])).trans (ready.cells col hc).1,
        (scale_block_memory_frame p ops input row s _ (by simp [partialSlot])).trans (ready.cells col hc).2⟩
    weights := by
      intro col hc
      exact (scale_block_memory_frame p ops input row s _ (by simp [globalCell, partialSlot])).trans (ready.weights col hc)
    epoch := by
      intro tid ht
      exact (congrArg (fun epochs => (epochs (row * 1024 + tid)).block) hp.2).trans (ready.epoch tid ht)
    good := scale_block_good p ops input row s ready }

theorem resume_reduced_ready (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row : Nat)
    (s : State α) (ready : ReducedReady p ops input row s) :
    OutReady p ops input row (resume (blockThreads (geometry p) row) .block s) := by
  exact {
    valid := ready.valid
    pc := by
      intro tid ht
      exact (resume_pc_at _ s _ (block_contains p row tid ht)).trans (congrArg (· + 1) (ready.pc tid ht))
    indices := ready.indices
    total := ready.total
    cells := ready.cells
    weights := ready.weights
    epoch := by
      intro tid ht
      exact (resume_epoch_at _ s _ (block_contains p row tid ht)).trans (congrArg (· + 1) (ready.epoch tid ht))
    good := ready.good }

theorem out_ready (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row : Nat)
    (s : State α) (ready : MidReady p ops input row s) : OutReady p ops input row (outState p ops input row s) :=
  resume_reduced_ready p ops input row (scaleBlock p ops input row s) (reduced_ready p ops input row s ready)

theorem initial_out_ready (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row : Nat) (hr : row < p.rows) :
    OutReady p ops input row (outState p ops input row (midState p ops input row (initial p input outside))) :=
  out_ready p ops input row _ (initial_mid_ready p ops input outside row hr)

theorem initial_two_barriers (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row : Nat) (hr : row < p.rows) :
    LarkPartitionCollective.runBlock ops (layout p) (geometry p) fuel program row fuel.block (initial p input outside) =
      LarkPartitionCollective.runBlock ops (layout p) (geometry p) fuel program row 1
        (outState p ops input row (midState p ops input row (initial p input outside))) :=
  (initial_first_barrier p ops input outside row hr).trans
    (block_second_eq p ops input row 1 _ (initial_mid_ready p ops input outside row hr))

theorem initial_out_race_free (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row : Nat) (hr : row < p.rows) :
    raceFree (geometry p) (outState p ops input row (midState p ops input row (initial p input outside))).trace = true :=
  race_free p _ (initial_out_ready p ops input outside row hr).good

#print axioms block_second_eq
#print axioms reduced_ready
#print axioms resume_reduced_ready
#print axioms out_ready
#print axioms initial_out_ready
#print axioms initial_two_barriers
#print axioms initial_out_race_free
end LarkNativeFusedRmsNorm
