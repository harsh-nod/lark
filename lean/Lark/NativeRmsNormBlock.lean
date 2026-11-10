import Lark.NativeRmsNormOutputBlock

/-! Complete actual native block execution from its entry contract. The contract
is satisfied initially and can be preserved for later rows of the grid.
-/
namespace LarkNativeRmsNorm
open LarkNonlinear
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

structure BlockEntry (p : Shape) (input : Nat → Nat → α) (row : Nat) (s : State α) : Prop where
  pc : ∀ tid, tid < 1024 → s.pc (row * 1024 + tid) = 0
  reads : Reads p input s
  epoch : ∀ tid, tid < 1024 → (s.epochs (row * 1024 + tid)).block = 0
  good : ∀ a ∈ s.trace, LarkReductionFootprint.Good (traversal p) 0 a

theorem initial_block_entry (p : Shape) (input : Nat → Nat → α) (row : Nat) (outside : Location → Option α) :
    BlockEntry p input row (initial (layout p) input outside) :=
  ⟨by intro tid ht; rfl, initial_reads p input outside, by intro tid ht; rfl, by intro a ha; cases ha⟩

theorem mid_ready (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row : Nat)
    (s : State α) (entry : BlockEntry p input row s) : MidReady p ops input row (midState p ops input row s) := by
  have he : (firstBlock p ops input row s).epochs = s.epochs := wave_fold_epochs p ops input row (List.range 16) s
  have hm := resume_memory (blockThreads (geometry p) row) (firstBlock p ops input row s)
  have hi := resume_indices (blockThreads (geometry p) row) (firstBlock p ops input row s)
  have htrace := resume_trace (blockThreads (geometry p) row) (firstBlock p ops input row s)
  constructor
  · intro tid ht
    exact (resume_pc_at _ (firstBlock p ops input row s) _ (block_contains p row tid ht)).trans
      (congrArg (· + 1) (first_block_member p ops input row tid s ht).1)
  · intro tid ht
    exact native_indices_of_eq _ (firstBlock p ops input row s) (midState p ops input row s) hi
      (first_block_member p ops input row tid s ht).2
  · exact reads_of_memory p input (firstBlock p ops input row s) (midState p ops input row s)
      (wave_fold_reads p ops input row (List.range 16) s entry.reads) hm
  · intro warp hw
    exact (congrFun hm ⟨.shared, row, 0, warp⟩).trans (first_block_partial p ops input row warp s hw)
  · intro tid ht
    have h := (congrArg (fun epochs => (epochs (row * 1024 + tid)).block) he).trans (entry.epoch tid ht)
    exact (resume_epoch_at _ (firstBlock p ops input row s) _ (block_contains p row tid ht)).trans (congrArg (· + 1) h)
  · intro a ha
    exact wave_fold_good p ops input row (List.range 16) s (fun w hw => List.mem_range.mp hw)
      (by
        intro w hw lane hl
        have hw := List.mem_range.mp hw
        simpa only [cohortBase, Nat.add_assoc] using entry.epoch (w * 64 + lane) (by omega)) entry.good a (htrace ▸ ha)

def nativeBlock (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row : Nat) (s : State α) : State α :=
  outputBlock p ops input row (outState p ops input row (midState p ops input row s))

theorem native_block_run (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) (hr : row < p.rows) (entry : BlockEntry p input row s) :
    LarkPartitionCollective.runBlock ops (layout p) (geometry p) fuel program row fuel.block s =
      some (nativeBlock p ops input row s) := by
  have hm := mid_ready p ops input row s entry
  have ho := out_ready p ops input row (midState p ops input row s) hm
  exact (block_first_eq p ops input row 2 s hr entry.reads entry.pc).trans
    ((block_second_eq p ops input row 1 (midState p ops input row s) hm).trans
      (output_block_run p ops input row 0 (outState p ops input row (midState p ops input row s)) hr ho))

theorem native_block_pc (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid : Nat) (s : State α) (ht : tid < 1024) :
    (nativeBlock p ops input row s).pc (row * 1024 + tid) = 70 :=
  output_block_pc p ops input row tid (outState p ops input row (midState p ops input row s)) ht

theorem native_block_value (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row col : Nat) (s : State α) (hc : col < 16384) :
    (nativeBlock p ops input row s).memory (globalCell 0 (row * 16384 + col)) = some (result ops input row col) :=
  output_block_value p ops input row col (outState p ops input row (midState p ops input row s)) hc

theorem native_block_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) (entry : BlockEntry p input row s) :
    ∀ a ∈ (nativeBlock p ops input row s).trace, LarkReductionFootprint.Good (traversal p) 0 a :=
  output_block_good p ops input row (outState p ops input row (midState p ops input row s))
    (out_ready p ops input row (midState p ops input row s) (mid_ready p ops input row s entry))

theorem native_block_from_initial (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row : Nat) (hr : row < p.rows) :
    ∃ final,
      LarkPartitionCollective.runBlock ops (layout p) (geometry p) fuel program row fuel.block
        (initial (layout p) input outside) = some final ∧
      (∀ col, col < 16384 → final.memory (globalCell 0 (row * 16384 + col)) = some (result ops input row col)) ∧
      (∀ tid, tid < 1024 → final.pc (row * 1024 + tid) = 70) ∧ raceFree (geometry p) final.trace = true := by
  let start := initial (layout p) input outside
  have entry := initial_block_entry p input row outside
  refine ⟨nativeBlock p ops input row start, native_block_run p ops input row start hr entry,
    (fun col hc => native_block_value p ops input row col start hc),
    (fun tid ht => native_block_pc p ops input row tid start ht), ?_⟩
  exact LarkReductionFootprint.race_free (traversal p) 0 _ (native_block_good p ops input row start entry)

#print axioms mid_ready
#print axioms native_block_run
#print axioms native_block_from_initial
end LarkNativeRmsNorm
