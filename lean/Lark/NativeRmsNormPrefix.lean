import Lark.NativeRmsNormVectors

/-! Complete actual per-thread execution up to the first native shuffle.
No claim about the remaining reduction, output phase or full launch is made.
-/
namespace LarkNativeRmsNorm
open LarkNonlinear
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def prefixState (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) : State α :=
  twoVectorsRun ops input (t / 1024) (t % 1024) t (ops.literal 0 1) (initialized ops t s)

theorem prefix_eq (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t extra : Nat) (s : State α) (reads : Reads p input s)
    (ht : t < p.rows * 1024) (hp : s.pc t = 0) :
    LarkCollective.runLane ops (layout p) (geometry p) program t (extra + 115) s =
      LarkCollective.runLane ops (layout p) (geometry p) program t extra (prefixState ops input t s) := by
  have hread := reads_of_memory p input s (initialized ops t s) reads (initialized_preserves ops t s).1
  have hr : t / 1024 < p.rows := (Nat.div_lt_iff_lt_mul (by decide)).mpr ht
  rcases initialized_fields ops t s with ⟨hpc, hi0, hi1, hi2, hi3, hi4, hi5, ha, hpeer⟩
  rewrite [show extra + 115 = (extra + 107) + 8 by omega, initialized_eq p ops t (extra + 107) s ht hp]
  exact two_vectors_eq p ops input (t / 1024) (t % 1024) t extra (ops.literal 0 1)
    (initialized ops t s) hread hr (Nat.mod_lt _ (by decide)) hi0 hi5 ha hpc

theorem prefix_pc (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) :
    (prefixState ops input t s).pc t = 18 := by
  simp [prefixState, twoVectorsRun, advance]

theorem prefix_lane (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t : Nat) (s : State α) (reads : Reads p input s)
    (ht : t < p.rows * 1024) (hp : s.pc t = 0) :
    LarkCollective.runLane ops (layout p) (geometry p) program t fuel.lane s =
      some (prefixState ops input t s) := by
  have hcut : LarkCollective.parked program (prefixState ops input t s) t = some .shuffle := by
    unfold LarkCollective.parked
    rewrite [prefix_pc, first_shuffle 0 (by decide)]
    rfl
  rewrite [show fuel.lane = 141 + 115 by decide, prefix_eq p ops input t 141 s reads ht hp]
  change LarkCollective.runLane ops (layout p) (geometry p) program t (140 + 1) _ = _
  rewrite [LarkCollective.runLane, hcut]
  rfl

theorem prefix_preserves (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) :
    (prefixState ops input t s).memory = s.memory ∧
    (prefixState ops input t s).epochs = s.epochs := by
  have h := two_vectors_preserves ops input (t / 1024) (t % 1024) t (ops.literal 0 1) (initialized ops t s)
  exact h

theorem prefix_acc (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) :
    (prefixState ops input t s).regs t 0 = some (threadSum ops input (t / 1024) (t % 1024)) := by
  have ha := (initialized_fields ops t s).2.2.2.2.2.2.2.1
  have h := two_vectors_acc ops input (t / 1024) (t % 1024) t (ops.literal 0 1) (initialized ops t s) ha
  rewrite [two_vectors_sum] at h
  exact h

theorem prefix_index_other (ops : Ops α) (input : Nat → Nat → α)
    (t reg : Nat) (s : State α) (h5 : reg ≠ 5) (h6 : reg ≠ 6) :
    (prefixState ops input t s).indices t reg = (initialized ops t s).indices t reg :=
  two_vectors_index_other ops input (t / 1024) (t % 1024) t reg (ops.literal 0 1) _ h5 h6

theorem prefix_other (ops : Ops α) (input : Nat → Nat → α)
    (t u : Nat) (s : State α) (hu : u ≠ t) :
    (prefixState ops input t s).pc u = s.pc u ∧
    (prefixState ops input t s).indices u = s.indices u ∧
    (prefixState ops input t s).regs u = s.regs u := by
  have h := two_vectors_other ops input (t / 1024) (t % 1024) t u (ops.literal 0 1) (initialized ops t s) hu
  have hi := initialized_other ops t u s hu
  exact ⟨h.1.trans hi.1, h.2.1.trans hi.2.1, h.2.2.trans hi.2.2⟩

theorem prefix_indices (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) :
    (prefixState ops input t s).indices t 0 = some ((t / 1024 : Nat) : Int) ∧
    (prefixState ops input t s).indices t 1 = some ((t % 1024 : Nat) : Int) ∧
    (prefixState ops input t s).indices t 2 = some (((t % 1024) % 64 : Nat) : Int) ∧
    (prefixState ops input t s).indices t 3 = some (((t % 1024) / 64 : Nat) : Int) ∧
    (prefixState ops input t s).indices t 4 = some (1024 - (((t % 1024) / 64 : Nat) : Int) * 64) := by
  have hi := initialized_fields ops t s
  exact ⟨(prefix_index_other ops input t 0 s (by decide) (by decide)).trans hi.2.1,
    (prefix_index_other ops input t 1 s (by decide) (by decide)).trans hi.2.2.1,
    (prefix_index_other ops input t 2 s (by decide) (by decide)).trans hi.2.2.2.1,
    (prefix_index_other ops input t 3 s (by decide) (by decide)).trans hi.2.2.2.2.1,
    (prefix_index_other ops input t 4 s (by decide) (by decide)).trans hi.2.2.2.2.2.1⟩

theorem prefix_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t : Nat) (s : State α) (good : ∀ a ∈ s.trace, LarkReductionFootprint.Good (traversal p) 0 a) :
    ∀ a ∈ (prefixState ops input t s).trace, LarkReductionFootprint.Good (traversal p) 0 a :=
  two_vectors_good p ops input (t / 1024) (t % 1024) t (ops.literal 0 1) (initialized ops t s) good

/-- Actual completion to the first shuffle, input-only accesses and the intended
ordered 16-term value, for every input and every initial outside state. -/
theorem prefix_from_initial (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (t : Nat) (ht : t < p.rows * 1024) :
    ∃ next,
      LarkCollective.runLane ops (layout p) (geometry p) program t fuel.lane
        (initial (layout p) input outside) = some next ∧
      next.pc t = 18 ∧
      next.regs t 0 = some (threadSum ops input (t / 1024) (t % 1024)) ∧
      next.memory = (initial (layout p) input outside).memory ∧
      next.epochs = (initial (layout p) input outside).epochs ∧
      (∀ a ∈ next.trace, LarkReductionFootprint.Good (traversal p) 0 a) := by
  let start := initial (layout p) input outside
  refine ⟨prefixState ops input t start, prefix_lane p ops input t start (initial_reads p input outside) ht rfl,
    prefix_pc ops input t start, prefix_acc ops input t start,
    (prefix_preserves ops input t start).1, (prefix_preserves ops input t start).2, ?_⟩
  exact prefix_good p ops input t start (by intro a ha; cases ha)

#print axioms prefix_lane
#print axioms prefix_acc
#print axioms prefix_other
#print axioms prefix_from_initial
end LarkNativeRmsNorm
