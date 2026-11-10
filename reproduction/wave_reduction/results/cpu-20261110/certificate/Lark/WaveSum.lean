import Lark.WaveReduceStore

/-! Whole actual launch for the six-stage full-wave reduction expression tree. -/
namespace LarkCollective.WaveSum
open LarkNonlinear
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem warp_tail (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (n remaining : Nat) (hn : n + remaining = 5) :
    runWarp ops layout geometry fuel program (List.range 64) (remaining + 1)
      (shuffled ops input outside n) = some (finalPartial ops input outside 64) := by
  induction remaining generalizing n with
  | zero =>
      have he : n = 5 := by omega
      subst n
      rewrite [runWarp, last_fold ops input outside 64 (by omega)]
      simp only [bind, pure, Option.some_bind, converged_final, reduceCtorEq, ↓reduceIte]
  | succ remaining ih =>
      have hlt : n < 5 := by omega
      change runWarp ops layout geometry fuel program (List.range 64) ((remaining + 1) + 1) _ = _
      rewrite [runWarp, add_fold ops input outside n hlt 64 (by omega)]
      rewrite [add_complete ops input outside n]
      simp only [bind, pure, Option.some_bind,
        converged_phase ops input outside (n + 1) (by omega), ↓reduceIte]
      rewrite [shuffle_eq ops input outside (n + 1) (by omega)]
      simp only [bind, pure, Option.some_bind]
      exact ih (n + 1) (by omega)

theorem warp_eq (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) :
    runWarp ops layout geometry fuel program (List.range 64) fuel.warp
      (initial layout input outside) = some (finalPartial ops input outside 64) := by
  have hload : (List.range 64).foldlM
      (fun s t => runLane ops layout geometry program t fuel.lane s)
      (initial layout input outside) = some (phaseState ops input outside 0) :=
    (load_fold ops input outside 64 (by omega)).trans
      (congrArg some (phase_zero ops input outside).symm)
  change runWarp ops layout geometry fuel program (List.range 64) (6 + 1) _ = _
  rewrite [runWarp, hload]
  simp only [bind, pure, Option.some_bind, converged_phase ops input outside 0 (by decide), ↓reduceIte]
  rewrite [shuffle_eq ops input outside 0 (by decide)]
  simp only [bind, pure, Option.some_bind]
  exact warp_tail ops input outside 0 5 rfl

theorem block_eq (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) :
    runBlock ops layout geometry fuel program 0 fuel.block (initial layout input outside) =
      some (finalPartial ops input outside 64) := by
  have hws : List.range ((geometry.block + geometry.warp - 1) / geometry.warp) = [0] := by decide
  have hwarp : warpThreads geometry 0 0 = List.range 64 := by decide
  have hblock : blockThreads geometry 0 = List.range 64 := by decide
  change runBlock ops layout geometry fuel program 0 (0 + 1) _ = _
  rewrite [runBlock, hws]
  simp only [List.foldlM_cons, List.foldlM_nil, hwarp, warp_eq, bind, pure, Option.some_bind,
    hblock, converged_final, reduceCtorEq, or_true, ↓reduceIte]

theorem launch_eq (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) :
    runLaunch ops layout geometry fuel program (initial layout input outside) =
      some (finalPartial ops input outside 64) := by
  have hblocks : List.range geometry.grid = [0] := by decide
  have hthreads : List.range (geometry.grid * geometry.block) = List.range 64 := by decide
  rewrite [runLaunch, if_neg (by decide)]
  change runGrid ops layout geometry fuel program (0 + 1) _ = _
  rewrite [runGrid, hblocks]
  simp only [List.foldlM_cons, List.foldlM_nil, block_eq, bind, pure, Option.some_bind,
    hthreads, converged_final, reduceCtorEq, ↓reduceIte]

def spec (ops : Ops α) (input : Nat → Nat → α) : List α :=
  (List.range 64).map (value ops input 6)

theorem final_extract (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) :
    extract layout (finalPartial ops input outside 64) = some (spec ops input) := by
  simp only [extract, layout, Transfer.layout, List.zipIdx_cons, List.zipIdx_nil,
    List.flatMap_cons, List.flatMap_nil, List.nil_append]
  simp only [List.map_cons, List.map_nil, show Role.input ≠ Role.output by decide,
    ↓reduceIte, List.nil_append, List.append_nil]
  change (((List.range 64).map (fun i => (1, i))).mapM
    (fun bi => (finalPartial ops input outside 64).memory
      ⟨.global, 0, bi.1, bi.2⟩) : Option (List α)) = _
  rewrite [Transfer.mapM_map]
  exact Transfer.mapM_some (List.range 64) _ _ (by
    intro t ht
    exact final_output ops input outside 64 t (List.mem_range.mp ht))

/-- Actual completion, RF and the entire expression-tree output, for arbitrary operations. -/
theorem correct (ops : Ops α) : Correct ops layout geometry fuel program (spec ops) := by
  intro input outside
  exact ⟨finalPartial ops input outside 64, launch_eq ops input outside,
    owned_raceFree geometry _ (final_owned ops input outside 64), final_extract ops input outside⟩

#print axioms warp_eq
#print axioms launch_eq
#print axioms correct
end LarkCollective.WaveSum
