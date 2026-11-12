import Lark.NativeQKNormRopeStores

/-! Complete actual interleaved scalar continuation from the fifth reduction
snapshot through normalization, rotation, all four FP16 stores, and halt. -/
namespace LarkNativeQKNormRope
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def interleavedNormals (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (a b : α) : Nat → α :=
  normalizedValue ops input t (weightBuffer t) (normalScale ops (ops.add a b))
def interleavedResult (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (a b : α) : Nat → α :=
  interleavedOutput ops input (interleavedNormals ops input t a b) t
def interleavedComputed (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (a b : α) (s : State α) : State α :=
  interleavedAfter ops input (interleavedNormals ops input t a b) t (normalLane ops input t a b s)
def interleavedTail (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (a b : α) (s : State α) : State α :=
  storeFour ops false t (interleavedResult ops input t a b) (interleavedComputed ops input t a b s)

theorem interleaved_computed_preserves (ops : Ops α) (input : Nat → Nat → α) (t : Nat)
    (a b : α) (s : State α) : (interleavedComputed ops input t a b s).memory = s.memory ∧
      (interleavedComputed ops input t a b s).epochs = s.epochs := by
  have rf := interleaved_preserves ops input (interleavedNormals ops input t a b) t (normalLane ops input t a b s)
  have nf := normal_lane_preserves ops input t a b s
  exact ⟨rf.1.trans nf.1, rf.2.trans nf.2⟩

theorem interleaved_computed_low_index (ops : Ops α) (input : Nat → Nat → α) (t r : Nat)
    (a b : α) (s : State α) (hr : r < 11) : (interleavedComputed ops input t a b s).indices t r = s.indices t r :=
  (interleaved_low_index ops input (interleavedNormals ops input t a b) t r _ (by omega)).trans
    (normal_lane_low_index ops input t r a b s hr)

theorem interleaved_computed_values (ops : Ops α) (input : Nat → Nat → α) (t : Nat)
    (a b : α) (s : State α) : StoreValues false (interleavedResult ops input t a b) t (interleavedComputed ops input t a b s) := by
  intro e he
  exact interleaved_values ops input (interleavedNormals ops input t a b) t e _ he

theorem interleaved_tail_eq (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (t extra : Nat)
    (a b : α) (s : State α) (ht : t < p.rows * 1280) (hp : s.pc t = 33)
    (ha : s.regs t 4 = some a) (hb : s.regs t 9 = some b)
    (hv : InputValues ops input t s) (hi : NativeIndices t s) (hr : Reads p input s) :
    LarkCollective.runLane ops (layout p) (geometry p) (program false) t (extra + (weightSteps t + 44)) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program false) t extra (interleavedTail ops input t a b s) := by
  have count : extra + (weightSteps t + 44) = (extra + 28) + (weightSteps t + 16) := by omega
  rw [count, normal_lane_eq p false ops input t (extra + 28) a b s hp ha hb hv hi hr]
  have reads : Reads p input (normalLane ops input t a b s) := by
    simpa only [Reads, (normal_lane_preserves ops input t a b s).1] using hr
  rw [show extra + 28 = (extra + 8) + 20 by omega,
    interleaved_eq p ops input (interleavedNormals ops input t a b) t (extra + 8)
      (normalLane ops input t a b s) ht (normal_lane_pc ops input t a b s)
      (fun e he => normal_lane_value ops input t e a b s he)
      ((normal_lane_low_index ops input t 1 a b s (by decide)).trans hi.1)
      ((normal_lane_low_index ops input t 3 a b s (by decide)).trans hi.2.2.1) reads]
  change LarkCollective.runLane ops (layout p) (geometry p) (program false) t (extra + 8)
    (interleavedComputed ops input t a b s) = _
  exact store_four_eq p false ops t extra (interleavedResult ops input t a b) (interleavedComputed ops input t a b s)
    ht (interleaved_pc ops input (interleavedNormals ops input t a b) t _)
    ((interleaved_computed_low_index ops input t 6 a b s (by decide)).trans hi.2.2.2.2.2)
    (interleaved_computed_values ops input t a b s)

theorem interleaved_tail_lane (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (t : Nat)
    (a b : α) (s : State α) (ht : t < p.rows * 1280) (hp : s.pc t = 33)
    (ha : s.regs t 4 = some a) (hb : s.regs t 9 = some b)
    (hv : InputValues ops input t s) (hi : NativeIndices t s) (hr : Reads p input s) :
    LarkCollective.runLane ops (layout p) (geometry p) (program false) t fuel.lane s =
      some (interleavedTail ops input t a b s) := by
  have hs : weightSteps t ≤ 6 := by unfold weightSteps; split <;> omega
  have count : fuel.lane = (211 - weightSteps t + 1) + (weightSteps t + 44) := by change 256 = _; omega
  rw [count, interleaved_tail_eq p ops input t (211 - weightSteps t + 1) a b s ht hp ha hb hv hi hr]
  have parked : LarkCollective.parked (program false) (interleavedTail ops input t a b s) t = some .halt :=
    store_four_parked ops false t _ _
  simp only [LarkCollective.runLane, parked]

theorem interleaved_tail_pc (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (a b : α) (s : State α) :
    (interleavedTail ops input t a b s).pc t = 87 := store_four_pc ops false t _ _

theorem interleaved_tail_values (ops : Ops α) (input : Nat → Nat → α) (t e : Nat) (a b : α)
    (s : State α) (he : e < 4) : (interleavedTail ops input t a b s).memory (globalCell 0 (outputAddress t e)) =
      some (ops.toHalf (interleavedResult ops input t a b e)) := store_four_values ops false t e _ _ he

theorem interleaved_tail_unowned (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (a b : α)
    (s : State α) (loc : Location) (hn : loc.buffer ≠ 0 ∨ loc.offset / 4 ≠ t) :
    (interleavedTail ops input t a b s).memory loc = s.memory loc :=
  (store_four_unowned ops false t _ _ loc hn).trans (congrFun (interleaved_computed_preserves ops input t a b s).1 loc)

theorem interleaved_tail_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (a b : α)
    (s : State α) (hr : Reads p input s) : Reads p input (interleavedTail ops input t a b s) := by
  apply store_four_reads
  simpa only [Reads, (interleaved_computed_preserves ops input t a b s).1] using hr

theorem interleaved_tail_epochs (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (a b : α) (s : State α) :
    (interleavedTail ops input t a b s).epochs = s.epochs := (interleaved_computed_preserves ops input t a b s).2

theorem interleaved_tail_good (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (a b : α)
    (s : State α) (good : ∀ access ∈ s.trace, Good access) :
    ∀ access ∈ (interleavedTail ops input t a b s).trace, Good access :=
  store_four_good ops false t _ _ (interleaved_good ops input (interleavedNormals ops input t a b) t _
    (normal_lane_good ops input t a b s good))

theorem interleaved_tail_trace_length (ops : Ops α) (input : Nat → Nat → α) (t : Nat)
    (a b : α) (s : State α) : (interleavedTail ops input t a b s).trace.length = s.trace.length + 12 := by
  have nw : (normalLane ops input t a b s).trace.length = 4 + s.trace.length := by
    simpa only [List.length_append, List.length_cons, List.length_nil] using congrArg List.length (normal_lane_trace ops input t a b s)
  have rwc : (interleavedComputed ops input t a b s).trace.length = 4 + (normalLane ops input t a b s).trace.length := by
    simpa only [List.length_append, List.length_cons, List.length_nil] using
      congrArg List.length (interleaved_trace ops input (interleavedNormals ops input t a b) t (normalLane ops input t a b s))
  have sw : (interleavedTail ops input t a b s).trace.length = 4 + (interleavedComputed ops input t a b s).trace.length := by
    simpa only [List.length_append, List.length_cons, List.length_nil] using
      congrArg List.length (store_four_trace ops false t (interleavedResult ops input t a b) (interleavedComputed ops input t a b s))
  omega

theorem interleaved_tail_other (ops : Ops α) (input : Nat → Nat → α) (t u : Nat)
    (a b : α) (s : State α) (hu : u ≠ t) :
    (interleavedTail ops input t a b s).pc u = s.pc u ∧ (interleavedTail ops input t a b s).indices u = s.indices u ∧
    (interleavedTail ops input t a b s).regs u = s.regs u := by
  have nf := normal_lane_other ops input t u a b s hu
  have rf := interleaved_other ops input (interleavedNormals ops input t a b) t u (normalLane ops input t a b s) hu
  have sf := store_four_other ops false t u (interleavedResult ops input t a b) (interleavedComputed ops input t a b s) hu
  exact ⟨sf.1.trans (rf.1.trans nf.1), sf.2.trans (rf.2.1.trans nf.2.1), rf.2.2.trans nf.2.2⟩

#print axioms interleaved_computed_preserves
#print axioms interleaved_computed_low_index
#print axioms interleaved_computed_values
#print axioms interleaved_tail_eq
#print axioms interleaved_tail_lane
#print axioms interleaved_tail_pc
#print axioms interleaved_tail_values
#print axioms interleaved_tail_unowned
#print axioms interleaved_tail_reads
#print axioms interleaved_tail_epochs
#print axioms interleaved_tail_good
#print axioms interleaved_tail_trace_length
#print axioms interleaved_tail_other
end LarkNativeQKNormRope
