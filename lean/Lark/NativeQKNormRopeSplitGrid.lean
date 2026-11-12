import Lark.NativeQKNormRopeSplitBlocks

/-! Complete actual split grid and launch execution, with the pinned
5*rows blocks, 256 threads, physical wave64 and unchanged execution fuel. -/
namespace LarkNativeQKNormRope
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def splitGridState (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (s : State α) : State α :=
  splitBlocks p ops input (List.range (p.rows * 5)) s

theorem split_grid_fold_run (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (s : State α)
    (hp : ∀ t, t < p.rows * 1280 → s.pc t = 0) (hr : Reads p input s) :
    (List.range (geometry p).grid).foldlM
      (fun s b => LarkPartitionCollective.runBlock ops (layout p) (geometry p) fuel (program true)
        b fuel.block s) s = some (splitGridState p ops input s) := by
  apply split_blocks_run p ops input (List.range (p.rows * 5)) s List.nodup_range
    (by intro b hb; exact List.mem_range.mp hb) ?_ hr
  intro b hb t ht
  exact hp t (split_native_block_bound p b t (List.mem_range.mp hb) ht)

theorem split_grid_pc (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (t : Nat)
    (s : State α) (ht : t < p.rows * 1280) : (splitGridState p ops input s).pc t = 106 :=
  split_blocks_pc p ops input (List.range (p.rows * 5)) s List.nodup_range (physicalBlock t) t
    (List.mem_range.mpr (physical_block_bound p t ht)) ((native_block_mem p (physicalBlock t) t).mpr rfl)

theorem split_grid_cut (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (s : State α) :
    LarkCollective.converged (program true) (List.range ((geometry p).grid * (geometry p).block))
      (splitGridState p ops input s) = some .halt := by
  have threads : List.range ((geometry p).grid * (geometry p).block) = cohortThreads 0 0 (p.rows * 1280) := by
    simp [geometry, cohortThreads, cohortBase, Nat.mul_assoc]
  rw [threads]
  apply (cohort_final_halt true 0 0 (p.rows * 1280) _ (by have h := p.positive; omega) ?_).2
  intro lane hl
  simpa only [cohortBase, Nat.zero_mul, Nat.add_zero, Nat.zero_add] using split_grid_pc p ops input lane s hl

theorem native_split_grid (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (s : State α)
    (hp : ∀ t, t < p.rows * 1280 → s.pc t = 0) (hr : Reads p input s) :
    LarkPartitionCollective.runGrid ops (layout p) (geometry p) fuel (program true) fuel.grid s =
      some (splitGridState p ops input s) := by
  change LarkPartitionCollective.runGrid _ _ _ _ _ (0 + 1) s = _
  rw [LarkPartitionCollective.runGrid, split_grid_fold_run p ops input s hp hr]
  simp only [bind, pure, Option.some_bind, split_grid_cut, reduceCtorEq, ↓reduceIte]

theorem native_split_launch (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (s : State α)
    (hp : ∀ t, t < p.rows * 1280 → s.pc t = 0) (hr : Reads p input s) :
    LarkPartitionCollective.runLaunch ops (layout p) (geometry p) fuel (program true) s =
      some (splitGridState p ops input s) := by
  have valid : ¬ ((geometry p).grid = 0 ∨ (geometry p).block = 0 ∨
      (geometry p).warp ≠ 64 ∨ (geometry p).block % 64 ≠ 0) := by
    simp only [geometry]
    have pos := p.positive
    omega
  rw [LarkPartitionCollective.runLaunch, if_neg valid]
  exact native_split_grid p ops input s hp hr

theorem split_grid_value (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (t e : Nat)
    (s : State α) (ht : t < p.rows * 1280) (he : e < 4) :
    (splitGridState p ops input s).memory (globalCell 0 (outputAddress t e)) =
      some (splitSourceResult ops input t e) :=
  split_blocks_value p ops input (List.range (p.rows * 5)) s List.nodup_range (physicalBlock t) t e
    (List.mem_range.mpr (physical_block_bound p t ht)) ((native_block_mem p (physicalBlock t) t).mpr rfl) he

theorem split_grid_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (s : State α)
    (hr : Reads p input s) : Reads p input (splitGridState p ops input s) :=
  split_blocks_reads p ops input (List.range (p.rows * 5)) s hr


theorem split_grid_other (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (t : Nat)
    (s : State α) (ht : p.rows * 1280 ≤ t) :
    (splitGridState p ops input s).pc t = s.pc t ∧
    (splitGridState p ops input s).indices t = s.indices t ∧
    (splitGridState p ops input s).regs t = s.regs t := by
  apply split_blocks_other
  intro hm
  have ho := List.mem_range.mp hm
  unfold physicalBlock at ho
  omega

theorem split_grid_memory_frame (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (s : State α) (loc : Location) (hn : loc.buffer ≠ 0 ∨ p.rows * 5120 ≤ loc.offset) :
    (splitGridState p ops input s).memory loc = s.memory loc := by
  apply split_blocks_memory_frame
  rcases hn with hb | ho
  · exact Or.inl hb
  · apply Or.inr
    intro hm
    have bound := List.mem_range.mp hm
    unfold physicalBlock at bound
    omega

theorem split_grid_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (s : State α)
    (good : ∀ access ∈ s.trace, Good access) : ∀ access ∈ (splitGridState p ops input s).trace, Good access :=
  split_blocks_good p ops input (List.range (p.rows * 5)) s good

theorem split_grid_trace_length (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (s : State α) :
    (splitGridState p ops input s).trace.length = s.trace.length + p.rows * 25600 := by
  have h : (splitGridState p ops input s).trace.length = s.trace.length + 5120 * (p.rows * 5) := by
    simpa only [List.length_range] using split_blocks_trace_length p ops input (List.range (p.rows * 5)) s
  omega

def splitFinalState (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) : State α := splitGridState p ops input (initial (layout p) input outside)

theorem split_final_launch (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) :
    LarkPartitionCollective.runLaunch ops (layout p) (geometry p) fuel (program true) (initial (layout p) input outside) =
      some (splitFinalState p ops input outside) :=
  native_split_launch p ops input _ (by intro t ht; rfl) (initial_reads p input outside)

theorem split_final_race_free (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) :
    raceFree (geometry p) (splitFinalState p ops input outside).trace = true :=
  race_free p _ (split_grid_good p ops input _ (by intro access ha; cases ha))

#print axioms split_grid_fold_run
#print axioms split_grid_pc
#print axioms split_grid_cut
#print axioms native_split_grid
#print axioms native_split_launch
#print axioms split_grid_value
#print axioms split_grid_reads
#print axioms split_grid_other
#print axioms split_grid_memory_frame
#print axioms split_grid_good
#print axioms split_grid_trace_length
#print axioms split_final_launch
#print axioms split_final_race_free
end LarkNativeQKNormRope
