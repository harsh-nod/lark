import Lark.NativeRmsNormFirstBlock

/-! The actual first block-barrier resume and the state entering the scale phase.
The trace retains prior access epochs; only current participating epochs advance.
-/
namespace LarkNativeRmsNorm
open LarkNonlinear
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def midState (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row : Nat) (s : State α) : State α :=
  resume (blockThreads (geometry p) row) .block (firstBlock p ops input row s)

theorem block_contains (p : Shape) (row tid : Nat) (ht : tid < 1024) :
    (blockThreads (geometry p) row).contains (row * 1024 + tid) = true := by
  apply List.contains_iff_mem.mpr
  unfold blockThreads
  exact List.mem_map.mpr ⟨tid, List.mem_range.mpr ht, rfl⟩

/-- Decompose the actual scheduler's first phase and real barrier resume. -/
theorem block_first_eq (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row n : Nat) (s : State α) (hr : row < p.rows) (reads : Reads p input s)
    (hp : ∀ tid, tid < 1024 → s.pc (row * 1024 + tid) = 0) :
    LarkPartitionCollective.runBlock ops (layout p) (geometry p) fuel program row (n + 1) s =
      LarkPartitionCollective.runBlock ops (layout p) (geometry p) fuel program row n
        (midState p ops input row s) := by
  rewrite [LarkPartitionCollective.runBlock, first_block_fold_run p ops input row s hr reads hp]
  simp only [bind, pure, Option.some_bind, first_block_cut, ↓reduceIte]
  rfl

structure MidReady (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row : Nat) (s : State α) : Prop where
  pc : ∀ tid, tid < 1024 → s.pc (row * 1024 + tid) = 39
  indices : ∀ tid, tid < 1024 → NativeIndices (row * 1024 + tid) s
  reads : Reads p input s
  partials : ∀ warp, warp < 16 → s.memory ⟨.shared, row, 0, warp⟩ = some (warpSum ops input row warp)
  epoch : ∀ tid, tid < 1024 → (s.epochs (row * 1024 + tid)).block = 1
  good : ∀ access ∈ s.trace, LarkReductionFootprint.Good (traversal p) 0 access

theorem mid_ready_from_initial (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row : Nat) :
    MidReady p ops input row (midState p ops input row (initial (layout p) input outside)) := by
  let start := initial (layout p) input outside
  constructor
  · intro tid ht
    have hp := (first_block_member p ops input row tid start ht).1
    change (if (blockThreads (geometry p) row).contains (row * 1024 + tid) then
      (firstBlock p ops input row start).pc (row * 1024 + tid) + 1 else _) = _
    rewrite [block_contains p row tid ht, if_pos rfl, hp]
    rfl
  · intro tid ht
    exact (first_block_member p ops input row tid start ht).2
  · exact wave_fold_reads p ops input row (List.range 16) start (initial_reads p input outside)
  · intro warp hw
    exact first_block_partial p ops input row warp start hw
  · intro tid ht
    have he : (firstBlock p ops input row start).epochs = start.epochs :=
      wave_fold_epochs p ops input row (List.range 16) start
    change (if (blockThreads (geometry p) row).contains (row * 1024 + tid) then
      bumpEpoch ((firstBlock p ops input row start).epochs (row * 1024 + tid)) .block else _).block = _
    rewrite [block_contains p row tid ht, if_pos rfl]
    change ((firstBlock p ops input row start).epochs (row * 1024 + tid)).block + 1 = 1
    rewrite [he]
    rfl
  · exact wave_fold_good p ops input row (List.range 16) start (fun w hw => List.mem_range.mp hw)
      (by intro w hw lane hl; rfl) (by intro access ha; cases ha)

#print axioms block_first_eq
#print axioms mid_ready_from_initial
end LarkNativeRmsNorm
