import Lark.NativeRmsNormOutputVectors

/-! Complete actual output-lane execution: shared-scale entry, two original
vector iterations, the final false outer guard and the real halt instruction.
-/
namespace LarkNativeRmsNorm
open LarkNonlinear
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem output_halt_eq (p : Shape) (ops : Ops α) (t vector extra : Nat) (s : State α)
    (hv : 2048 ≤ vector) (hi : s.indices t 7 = some (vector : Int)) (hp : s.pc t = 58) :
    LarkCollective.runLane ops (layout p) (geometry p) program t (extra + 2) s = some (advance s t 70) := by
  have hg := LarkReduction.predicate_nlt_of (geometry p) t s (.ivar 7) (.const 2048)
    (vector : Int) 2048 hi (LarkReduction.int32_cast 2048 (by decide)) (by omega)
  have he : execute ops (layout p) (geometry p) t (.branch (.lt (.ivar 7) (.const 2048)) 70) s =
      some (advance s t 70) := by
    simp only [execute, hg, bind, pure, Option.bind]
    rfl
  have hcut : LarkCollective.parked program (advance s t 70) t = some .halt := by
    unfold LarkCollective.parked
    simp only [advance, ↓reduceIte]
    rewrite [LarkNativeRmsNorm.halt]
    rfl
  have hlast : LarkCollective.runLane ops (layout p) (geometry p) program t (extra + 1) (advance s t 70) =
      some (advance s t 70) := by
    rewrite [LarkCollective.runLane, hcut]
    rfl
  exact (output_scalar_step p ops t 58 (extra + 1) _ s _ output_begin_code hp he).trans hlast

def outputPair (ops : Ops α) (input : Nat → Nat → α) (row tid t : Nat) (inverse : α) (s : State α) : State α :=
  outputVector ops input row (tid + 1024) t inverse (outputVector ops input row tid t inverse s)

theorem output_pair_run (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid t extra : Nat) (inverse : α) (s : State α)
    (reads : Reads p input s) (hr : row < p.rows) (ht : tid < 1024)
    (hi0 : s.indices t 0 = some (row : Int)) (hi7 : s.indices t 7 = some (tid : Int))
    (hx : s.regs t 4 = some inverse) (hp : s.pc t = 58) :
    LarkCollective.runLane ops (layout p) (geometry p) program t (extra + 140) s =
      some (advance (outputPair ops input row tid t inverse s) t 70) := by
  have h0 := output_vector_fields ops input row tid t inverse s
  have h1 := output_vector_fields ops input row (tid + 1024) t inverse (outputVector ops input row tid t inverse s)
  exact (output_vector_cycle p ops input row tid t (extra + 71) inverse s reads hr (by omega) hi0 hi7 hx hp).trans
    ((output_vector_cycle p ops input row (tid + 1024) t (extra + 2) inverse
      (outputVector ops input row tid t inverse s)
      (output_vector_reads p ops input row tid t inverse s reads) hr (by omega)
      (h0.2.1.trans hi0) h0.2.2.1 (h0.2.2.2.1.trans hx) h0.1).trans
      (output_halt_eq p ops t (tid + 1024 + 1024) extra
        (outputVector ops input row (tid + 1024) t inverse (outputVector ops input row tid t inverse s))
        (by omega) h1.2.2.1 h1.1))

def outputLane (ops : Ops α) (input : Nat → Nat → α) (row tid t : Nat) (s : State α) : State α :=
  advance (outputPair ops input row tid t (scale ops input row) (outEntered t row tid (scale ops input row) s)) t 70

theorem output_lane_run (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid t : Nat) (s : State α) (reads : Reads p input s) (hr : row < p.rows) (ht : tid < 1024)
    (hrow : t / 1024 = row) (hi0 : s.indices t 0 = some (row : Int))
    (hi1 : s.indices t 1 = some (tid : Int)) (hscale : s.memory (scaleSlot row) = some (scale ops input row))
    (hp : s.pc t = 56) :
    LarkCollective.runLane ops (layout p) (geometry p) program t fuel.lane s =
      some (outputLane ops input row tid t s) := by
  have hf := output_entry_fields t row tid (scale ops input row) s
  exact (output_entry_eq p ops t row tid 254 _ s hrow hi1 hscale hp).trans (output_pair_run p ops input row tid t 114 _ (outEntered t row tid (scale ops input row) s) reads hr ht
    (hf.2.1.trans hi0) hf.2.2.1 hf.2.2.2 hf.1)

theorem output_pair_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid t : Nat) (inverse : α) (s : State α) (ht : tid < 1024) (hthread : t = row * 1024 + tid)
    (good : ∀ a ∈ s.trace, LarkReductionFootprint.Good (traversal p) 0 a) :
    ∀ a ∈ (outputPair ops input row tid t inverse s).trace,
      LarkReductionFootprint.Good (traversal p) 0 a := by
  exact output_vector_good p ops input row (tid + 1024) t inverse
    (outputVector ops input row tid t inverse s) (by omega)
    (by simpa only [Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_eq_of_lt ht] using hthread)
    (output_vector_good p ops input row tid t inverse s (by omega)
      (by simpa only [Nat.mod_eq_of_lt ht] using hthread) good)

theorem output_lane_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid t : Nat) (s : State α) (ht : tid < 1024) (hthread : t = row * 1024 + tid)
    (hrow : t / 1024 = row) (he : (s.epochs t).block = 2)
    (good : ∀ a ∈ s.trace, LarkReductionFootprint.Good (traversal p) 0 a) :
    ∀ a ∈ (outputLane ops input row tid t s).trace,
      LarkReductionFootprint.Good (traversal p) 0 a :=
  output_pair_good p ops input row tid t (scale ops input row)
    (outEntered t row tid (scale ops input row) s) ht hthread
    (output_entry_good p t row tid (scale ops input row) s hrow he good)

#print axioms output_pair_run
#print axioms output_lane_run
#print axioms output_lane_good
end LarkNativeRmsNorm
