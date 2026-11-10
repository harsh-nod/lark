import Lark.NativeRmsNormLastWave

/-! Decompose the unchanged scheduler to compose source phases while keeping
intermediate states abstract. These are definitional equalities, not new opcodes.
-/
namespace LarkNativeRmsNorm
open LarkNonlinear
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def continueCohort (p : Shape) (ops : Ops α) (ts : List Nat) (n : Nat) (s : State α) : Option (State α) := do
  match LarkPartitionCollective.nextCohort program ts s with
  | some cohort =>
    let next ← LarkPartitionCollective.runShuffle (geometry p) program cohort s
    LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel program ts n next
  | none =>
    let cut ← LarkCollective.converged program ts s
    if cut = .warp then
      LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel program ts n (resume ts .warp s)
    else some s

theorem runWarp_continue (p : Shape) (ops : Ops α) (ts : List Nat) (n : Nat) (s : State α) :
    LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel program ts (n + 1) s =
      (ts.foldlM (fun u t => LarkCollective.runLane ops (layout p) (geometry p) program t fuel.lane u) s).bind
        (continueCohort p ops ts n) := rfl

theorem continue_shuffle (p : Shape) (ops : Ops α) (ts cohort : List Nat) (n : Nat) (s : State α)
    (hc : LarkPartitionCollective.nextCohort program ts s = some cohort) :
    continueCohort p ops ts n s =
      (LarkPartitionCollective.runShuffle (geometry p) program cohort s).bind
        (fun next => LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel program ts n next) := by
  unfold continueCohort
  rewrite [hc]
  rfl

theorem bind_follow (f : Option (State α)) (g h : State α → Option (State α)) (next : State α)
    (hf : f.bind g = some next) : f.bind (fun s => (g s).bind h) = h next := by
  cases f with
  | none => simp at hf
  | some s =>
      simp only [Option.some_bind] at hf ⊢
      rewrite [hf]
      rfl

/-- Compose one actual shuffle and its following actual lane fold with the
remaining scheduler. `ts` remains the physical cohort; `cohort` is selected by
`nextCohort`, allowing a later complete logical partition without padding. -/
theorem continue_fold (p : Shape) (ops : Ops α) (ts cohort : List Nat) (n : Nat) (s next : State α)
    (hc : LarkPartitionCollective.nextCohort program ts s = some cohort)
    (hf : ((LarkPartitionCollective.runShuffle (geometry p) program cohort s).bind
      fun shuffled => ts.foldlM
        (fun u t => LarkCollective.runLane ops (layout p) (geometry p) program t fuel.lane u) shuffled) = some next) :
    continueCohort p ops ts (n + 1) s = continueCohort p ops ts n next := by
  rewrite [continue_shuffle p ops ts cohort (n + 1) s hc]
  have hrun : (fun shuffled => LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel program ts (n + 1) shuffled) =
      (fun shuffled => (ts.foldlM
        (fun u t => LarkCollective.runLane ops (layout p) (geometry p) program t fuel.lane u) shuffled).bind
        (continueCohort p ops ts n)) := by
    funext shuffled
    exact runWarp_continue p ops ts n shuffled
  rewrite [hrun]
  exact bind_follow _ _ _ next hf

#print axioms runWarp_continue
#print axioms continue_fold
end LarkNativeRmsNorm
