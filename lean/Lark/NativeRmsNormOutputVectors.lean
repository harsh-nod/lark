import Lark.NativeRmsNormOutputLoop

/-! Actual outer output-vector guard, inner-loop setup and stride-1024 tail. -/
namespace LarkNativeRmsNorm
open LarkNonlinear
open LarkReduction (setIndex int32_cast execute_index_of)
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def outputBegin (t : Nat) (s : State α) : State α := setIndex (advance s t 59) t 8 0 60
def outputTail (t vector : Nat) (s : State α) : State α :=
  advance (setIndex s t 7 ((vector + 1024 : Nat) : Int) 69) t 58

theorem output_begin_code : program[58]? = some (.scalar (.branch (.lt (.ivar 7) (.const 2048)) 70)) := by decide
theorem output_zero_code : program[59]? = some (.scalar (.index 8 (.const 0))) := by decide
theorem output_tail_code : program[68]? = some (.scalar (.index 7 (.add (.ivar 7) (.const 1024)))) := by decide
theorem output_jump_code : program[69]? = some (.scalar (.jump 58)) := by decide

theorem output_begin_eq (p : Shape) (ops : Ops α) (t vector extra : Nat) (s : State α)
    (hv : vector < 2048) (hi : s.indices t 7 = some (vector : Int)) (hp : s.pc t = 58) :
    LarkCollective.runLane ops (layout p) (geometry p) program t (extra + 2) s =
      LarkCollective.runLane ops (layout p) (geometry p) program t extra (outputBegin t s) := by
  let s1 := advance s t 59
  have hg := LarkReduction.predicate_lt_of (geometry p) t s (.ivar 7) (.const 2048)
    (vector : Int) 2048 hi (int32_cast 2048 (by decide)) (by omega)
  have h1 : execute ops (layout p) (geometry p) t (.branch (.lt (.ivar 7) (.const 2048)) 70) s = some s1 := by
    simp only [execute, hg, hp, bind, pure, Option.bind]
    rfl
  have h2 := execute_index_of ops (layout p) (geometry p) t 8 60 (.const 0) s1 0 (by rfl) (by simp [s1, advance])
  rewrite [output_scalar_step p ops t 58 _ _ s s1 output_begin_code hp h1,
    output_scalar_step p ops t 59 _ _ s1 _ output_zero_code (by simp [s1, advance]) h2]
  rfl

theorem output_tail_eq (p : Shape) (ops : Ops α) (t vector extra : Nat) (s : State α)
    (hv : vector < 2048) (hi : s.indices t 7 = some (vector : Int)) (hp : s.pc t = 68) :
    LarkCollective.runLane ops (layout p) (geometry p) program t (extra + 2) s =
      LarkCollective.runLane ops (layout p) (geometry p) program t extra (outputTail t vector s) := by
  let s1 := setIndex s t 7 ((vector + 1024 : Nat) : Int) 69
  have he := LarkReduction.eval_add_of (geometry p) t s (.ivar 7) (.const 1024)
    (vector : Int) 1024 ((vector + 1024 : Nat) : Int) hi (int32_cast 1024 (by decide))
    ((congrArg int32 (Int.natCast_add vector 1024).symm).trans (int32_cast _ (by omega)))
  have h1 := execute_index_of ops (layout p) (geometry p) t 7 69 (.add (.ivar 7) (.const 1024)) s
    ((vector + 1024 : Nat) : Int) he (by omega)
  have h2 : execute ops (layout p) (geometry p) t (.jump 58) s1 = some (outputTail t vector s) := rfl
  rewrite [output_scalar_step p ops t 68 _ _ s s1 output_tail_code hp h1,
    output_scalar_step p ops t 69 _ _ s1 _ output_jump_code (by simp [s1, setIndex, advance]) h2]
  rfl

def outputVector (ops : Ops α) (input : Nat → Nat → α) (row vector t : Nat) (inverse : α) (s : State α) : State α :=
  outputTail t vector (outputComponents ops input row vector t inverse 0 8 (outputBegin t s))

theorem output_vector_cycle (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row vector t extra : Nat) (inverse : α) (s : State α)
    (reads : Reads p input s) (hr : row < p.rows) (hv : vector < 2048)
    (hi0 : s.indices t 0 = some (row : Int)) (hi7 : s.indices t 7 = some (vector : Int))
    (hx : s.regs t 4 = some inverse) (hp : s.pc t = 58) :
    LarkCollective.runLane ops (layout p) (geometry p) program t (extra + 69) s =
      LarkCollective.runLane ops (layout p) (geometry p) program t extra
        (outputVector ops input row vector t inverse s) := by
  have hf := output_components_fields ops input row vector t 0 8 inverse (outputBegin t s)
  have hb0 : (outputBegin t s).indices t 0 = some (row : Int) := by simpa [outputBegin, setIndex, advance] using hi0
  have hb7 : (outputBegin t s).indices t 7 = some (vector : Int) := by simpa [outputBegin, setIndex, advance] using hi7
  have hb8 : (outputBegin t s).indices t 8 = some 0 := by simp [outputBegin, setIndex, advance]
  have hbx : (outputBegin t s).regs t 4 = some inverse := hx
  have hbp : (outputBegin t s).pc t = 60 := by simp [outputBegin, setIndex, advance]
  rewrite [show extra + 69 = (extra + 67) + 2 by omega, output_begin_eq p ops t vector (extra + 67) s hv hi7 hp]
  rewrite [show extra + 67 = (extra + 2) + 8 * 8 + 1 by omega,
    output_components_eq p ops input row vector 0 8 t (extra + 2) inverse (outputBegin t s)
      (by decide) reads hr hv hb0 hb7 hb8 hbx hbp]
  exact output_tail_eq p ops t vector extra _ hv (hf.2.2.1.trans hb7) hf.1

theorem output_vector_fields (ops : Ops α) (input : Nat → Nat → α)
    (row vector t : Nat) (inverse : α) (s : State α) :
    (outputVector ops input row vector t inverse s).pc t = 58 ∧
    (outputVector ops input row vector t inverse s).indices t 0 = s.indices t 0 ∧
    (outputVector ops input row vector t inverse s).indices t 7 = some ((vector + 1024 : Nat) : Int) ∧
    (outputVector ops input row vector t inverse s).regs t 4 = s.regs t 4 ∧
    (outputVector ops input row vector t inverse s).epochs = s.epochs := by
  have h := output_components_fields ops input row vector t 0 8 inverse (outputBegin t s)
  refine ⟨by simp [outputVector, outputTail, advance], ?_, by simp [outputVector, outputTail, setIndex, advance], h.2.2.2.1, h.2.2.2.2⟩
  exact (show (outputVector ops input row vector t inverse s).indices t 0 =
    (outputComponents ops input row vector t inverse 0 8 (outputBegin t s)).indices t 0 by
      simp [outputVector, outputTail, setIndex, advance]).trans
    (h.2.1.trans (by simp [outputBegin, setIndex, advance]))

theorem output_vector_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row vector t : Nat) (inverse : α) (s : State α) (reads : Reads p input s) :
    Reads p input (outputVector ops input row vector t inverse s) :=
  output_components_reads p ops input row vector t 0 8 inverse (outputBegin t s) reads

theorem output_vector_value (ops : Ops α) (input : Nat → Nat → α)
    (row vector t c : Nat) (inverse : α) (s : State α) (hc : c < 8) :
    (outputVector ops input row vector t inverse s).memory (globalCell 0 (scalarAddress row vector c)) =
      some (ops.toHalf (outputWeighted ops input row vector c inverse)) :=
  output_components_value ops input row vector t 0 8 c inverse (outputBegin t s) (by omega) (by omega)

theorem output_vector_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row vector t : Nat) (inverse : α) (s : State α)
    (hv : vector < 2048) (ht : t = row * 1024 + vector % 1024)
    (good : ∀ a ∈ s.trace, LarkReductionFootprint.Good (traversal p) 0 a) :
    ∀ a ∈ (outputVector ops input row vector t inverse s).trace,
      LarkReductionFootprint.Good (traversal p) 0 a :=
  output_components_good p ops input row vector t 0 8 inverse (outputBegin t s) (by decide) hv ht good

#print axioms output_vector_cycle
#print axioms output_vector_fields
#print axioms output_vector_value
#print axioms output_vector_good
end LarkNativeRmsNorm
