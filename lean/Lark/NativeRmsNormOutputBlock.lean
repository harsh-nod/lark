import Lark.NativeRmsNormOutputWaves
import Lark.NativeRmsNormOutputColumn

/-! Actual complete output block phase, with all row values and actual access
classification, under the original 1024-thread/wave64 geometry and fuel.
-/
namespace LarkNativeRmsNorm
open LarkNonlinear
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem block_mem (p : Shape) (row t : Nat) :
    t ∈ blockThreads (geometry p) row ↔ ∃ tid, tid < 1024 ∧ t = row * 1024 + tid := by
  constructor
  · intro ht
    obtain ⟨tid, hm, he⟩ := List.mem_map.mp ht
    exact ⟨tid, List.mem_range.mp hm, he.symm⟩
  · rintro ⟨tid, ht, rfl⟩
    exact List.mem_map.mpr ⟨tid, List.mem_range.mpr ht, rfl⟩

theorem block_cohort (p : Shape) (row : Nat) : blockThreads (geometry p) row = cohortThreads row 0 1024 := by
  simp [blockThreads, geometry, cohortThreads, cohortBase]

theorem block_nodup (p : Shape) (row : Nat) : (blockThreads (geometry p) row).Nodup := by
  rewrite [block_cohort]
  exact cohort_nodup row 0 1024

theorem block_owner (p : Shape) (row t : Nat) (ht : t ∈ blockThreads (geometry p) row) : t / 1024 = row := by
  obtain ⟨tid, ht, rfl⟩ := (block_mem p row t).mp ht
  omega

def outputBlock (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row : Nat) (s : State α) : State α :=
  outputFold ops input row (blockThreads (geometry p) row) s

theorem output_block_fold_run (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) (hr : row < p.rows) (ready : OutReady p ops input row s) :
    (List.range (((geometry p).block + (geometry p).warp - 1) / (geometry p).warp)).foldlM
      (fun s w => LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel program
        (warpThreads (geometry p) row w) fuel.warp s) s = some (outputBlock p ops input row s) := by
  have hcount : ((geometry p).block + (geometry p).warp - 1) / (geometry p).warp = 16 := by
    change (1024 + 64 - 1) / 64 = 16
    decide
  have hf := output_waves_run p ops input row (List.range 16) s hr List.nodup_range
    (fun w hw => List.mem_range.mp hw) ready.reads
    (by
      intro w hw lane hl
      have hw := List.mem_range.mp hw
      simpa only [cohortBase, Nat.add_assoc] using ready.indices (w * 64 + lane) (by omega))
    ready.scale
    (by
      intro w hw lane hl
      have hw := List.mem_range.mp hw
      simpa only [cohortBase, Nat.add_assoc] using ready.pc (w * 64 + lane) (by omega))
  have he : outputWaves ops input row (List.range 16) s = outputBlock p ops input row s := by
    rewrite [output_waves_eq_fold, all_output_threads p row]
    rfl
  rewrite [hcount]
  exact hf.trans (congrArg some he)

theorem output_block_pc (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid : Nat) (s : State α) (ht : tid < 1024) :
    (outputBlock p ops input row s).pc (row * 1024 + tid) = 70 :=
  output_fold_pc ops input row (blockThreads (geometry p) row) s (block_nodup p row)
    (row * 1024 + tid) ((block_mem p row _).mpr ⟨tid, ht, rfl⟩)

theorem block_halt_of_pc (p : Shape) (row : Nat) (s : State α)
    (hp : ∀ tid, tid < 1024 → s.pc (row * 1024 + tid) = 70) :
    LarkCollective.converged program (blockThreads (geometry p) row) s = some .halt := by
  rewrite [block_cohort]
  apply (cohort_halt row 0 1024 s (by decide) ?_).2
  intro tid ht
  simpa only [cohortBase, Nat.zero_mul, Nat.add_zero] using hp tid ht

theorem output_block_cut (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row : Nat) (s : State α) :
    LarkCollective.converged program (blockThreads (geometry p) row) (outputBlock p ops input row s) = some .halt :=
  block_halt_of_pc p row (outputBlock p ops input row s) (fun tid ht => output_block_pc p ops input row tid s ht)

theorem output_block_run (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row extra : Nat) (s : State α) (hr : row < p.rows) (ready : OutReady p ops input row s) :
    LarkPartitionCollective.runBlock ops (layout p) (geometry p) fuel program row (extra + 1) s =
      some (outputBlock p ops input row s) := by
  rewrite [LarkPartitionCollective.runBlock, output_block_fold_run p ops input row s hr ready]
  simp only [bind, pure, Option.some_bind, output_block_cut, reduceCtorEq, ↓reduceIte, or_true]

theorem output_block_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) (ready : OutReady p ops input row s) :
    ∀ a ∈ (outputBlock p ops input row s).trace, LarkReductionFootprint.Good (traversal p) 0 a := by
  apply output_fold_good p ops input row (blockThreads (geometry p) row) s (block_owner p row)
  · intro t ht
    obtain ⟨tid, htid, rfl⟩ := (block_mem p row t).mp ht
    exact ready.epoch tid htid
  · exact ready.good

theorem output_block_value (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row col : Nat) (s : State α) (hc : col < 16384) :
    (outputBlock p ops input row s).memory (globalCell 0 (row * 16384 + col)) = some (result ops input row col) := by
  let tid := col / 8 % 1024
  let t := row * 1024 + tid
  have ht : tid < 1024 := Nat.mod_lt _ (by decide)
  have hm : t % 1024 = tid := by dsimp only [t]; omega
  have hv : col / 8 < 2048 := by omega
  have hcomp : col % 8 < 8 := Nat.mod_lt _ (by decide)
  have hcol : col / 8 * 8 + col % 8 = col := by have h := Nat.div_add_mod col 8; omega
  have howner : OutputOwner p t (globalCell 0 (row * 16384 + col)) := by
    have h := output_cell_owner p row tid t (col / 8) (col % 8) hv hcomp rfl rfl
    simpa only [scalarAddress, Nat.add_assoc, hcol] using h
  apply output_fold_value p ops input row (blockThreads (geometry p) row) s (block_nodup p row) (block_owner p row)
    t ((block_mem p row t).mpr ⟨tid, ht, rfl⟩) _ _ howner
  intro u
  rewrite [hm]
  exact output_lane_column_value ops input row t col u hc

#print axioms output_block_run
#print axioms output_block_value
#print axioms output_block_good
end LarkNativeRmsNorm
