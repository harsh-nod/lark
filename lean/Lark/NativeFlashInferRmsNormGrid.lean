import Lark.NativeFlashInferRmsNormRows

/-! Whole actual native read-only-input launch under the original grid scheduler.
All rows complete and the output has its source-ordered values with the input retained.
-/
namespace LarkNativeFlashInferRmsNorm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem grid_halt_of_pc (p : Shape) (s : State α)
    (hp : ∀ t, t < p.rows * 1024 → s.pc t = 67) :
    LarkCollective.converged program (List.range (p.rows * 1024)) s = some .halt := by
  have ht : List.range (p.rows * 1024) = cohortThreads 0 0 (p.rows * 1024) := by
    simp [cohortThreads,cohortBase]
  rewrite [ht]
  apply (cohort_halt 0 0 (p.rows * 1024) s (Nat.mul_pos p.positive (by decide)) ?_).2
  intro t ht
  simpa only [cohortBase,Nat.zero_mul,Nat.zero_add] using hp t ht

theorem launch_of_rows (p : Shape) (ops : Ops α) (s next : State α)
    (hf : (List.range p.rows).foldlM
      (fun s row => LarkPartitionCollective.runBlock ops (layout p) (geometry p) fuel program row fuel.block s) s = some next)
    (hc : LarkCollective.converged program (List.range (p.rows * 1024)) next = some .halt) :
    LarkPartitionCollective.runLaunch ops (layout p) (geometry p) fuel program s = some next := by
  have hg : ¬ ((geometry p).grid = 0 ∨ (geometry p).block = 0 ∨ (geometry p).warp ≠ 64 ∨ (geometry p).block % 64 ≠ 0) := by
    have hp := p.positive
    simp only [geometry]
    omega
  rewrite [LarkPartitionCollective.runLaunch,if_neg hg]
  change LarkPartitionCollective.runGrid ops (layout p) (geometry p) fuel program (0 + 1) s = _
  rewrite [LarkPartitionCollective.runGrid,show (geometry p).grid = p.rows from rfl,hf]
  simp only [bind,pure,Option.some_bind,show (geometry p).block = 1024 from rfl,hc,reduceCtorEq,↓reduceIte]

def finalState (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) : State α :=
  nativeRows p ops input (List.range p.rows) (initial p input outside)

theorem final_pc (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (t : Nat) (ht : t < p.rows * 1024) :
    (finalState p ops input outside).pc t = 67 := by
  have hr : t / 1024 < p.rows := by omega
  have hl : t % 1024 < 1024 := Nat.mod_lt _ (by decide)
  have he : t / 1024 * 1024 + t % 1024 = t := by omega
  have hp := native_rows_pc p ops input (List.range p.rows) (initial p input outside)
    List.nodup_range (t / 1024) (t % 1024) (List.mem_range.mpr hr) hl
  exact (congrArg (fun u => (finalState p ops input outside).pc u) he).symm.trans hp

theorem final_values (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row : Nat) (hr : row < p.rows) : RowValues ops input row (finalState p ops input outside) :=
  native_rows_values p ops input (List.range p.rows) (initial p input outside) List.nodup_range
    (fun r hr => initial_block_entry p input outside r (List.mem_range.mp hr)) row (List.mem_range.mpr hr)

theorem final_exec (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) :
    LarkPartitionCollective.runLaunch ops (layout p) (geometry p) fuel program (initial p input outside) =
      some (finalState p ops input outside) ∧ raceFree (geometry p) (finalState p ops input outside).trace = true := by
  have h := native_rows_exec p ops input (List.range p.rows) (initial p input outside) List.nodup_range
    (fun row hr => initial_block_entry p input outside row (List.mem_range.mp hr)) (by intro a ha; cases ha)
  exact ⟨launch_of_rows p ops (initial p input outside) (finalState p ops input outside) h.1
    (grid_halt_of_pc p (finalState p ops input outside) (final_pc p ops input outside)),race_free p _ h.2⟩

#print axioms grid_halt_of_pc
#print axioms launch_of_rows
#print axioms final_pc
#print axioms final_values
#print axioms final_exec
end LarkNativeFlashInferRmsNorm
