import LarkReal.BenchmarkReferenceImports
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace LarkCertificate
open LarkNonlinear
open LarkPointwise (Scalar)
def body : Scalar := (.bin .max .input (.lit (0) 1))
def referenceBody : Scalar := (.bin .max .input (.lit (0) 1))
def layout : Layout := LarkPointwise.layout 16384
def geometry : Geometry := LarkPointwise.geometry 16384 64
def fuel : Fuel := LarkPointwise.fuel
def program : List Instr := [(.index 0 .bid), (.assign 0 (.un .fromHalf (.load .global 0 (.ivar (0))))), (.store .global 1 (.ivar (0)) (.un .toHalf (.bin .max (.reg (0)) (.lit (0) 1)))), .halt]
def spec (ops : Ops α) (input : Nat → Nat → α) : List α :=
  LarkPointwise.spec ops referenceBody 16384 input
def finalState (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) : State α :=
  LarkPointwise.partialState ops body 16384 input outside 16384

theorem segmentation_data : program = LarkPointwise.program body := by rfl
run_meta Lean.logInfo "LARK_HARMLESS_COMMAND_BOUNDARY_CONTROL"

theorem segmentation (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) :
    runLaunch ops layout geometry fuel program (initial layout input outside) =
      some (finalState ops input outside) := by
  rw [segmentation_data]
  exact LarkPointwise.launch_eq ops body 16384 64 input outside
    (by simp [LarkPointwise.Valid, body]) (by decide) (by decide) (by decide)

theorem race_free (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) :
    raceFree geometry (finalState ops input outside).trace = true := by
  exact LarkPointwise.owned_raceFree geometry _
    (LarkPointwise.partialState_owned ops body 16384 input outside 16384)

theorem segment_equivalence (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) :
    extract layout (finalState ops input outside) = some (spec ops input) := by
  exact LarkPointwise.partialState_extract ops body 16384 input outside

theorem kernel_eq_spec (ops : Ops α) :
    Correct ops layout geometry fuel program (spec ops) := by
  intro input outside
  exact ⟨finalState ops input outside, segmentation ops input outside,
    race_free ops input outside, segment_equivalence ops input outside⟩
theorem kernel_eq_spec_pre (ops : Ops α) (input : Nat → Nat → α) (s : State α)
    (pre : StdPre layout input s) :
    ∃ final, runLaunch ops layout geometry fuel program s = some final ∧
      raceFree geometry final.trace = true ∧ extract layout final = some (spec ops input) := by
  exact correct_from_pre ops layout geometry fuel program (spec ops)
    (kernel_eq_spec ops) input s pre
#print axioms segmentation_data
#print axioms segmentation
#print axioms race_free
#print axioms segment_equivalence
#print axioms kernel_eq_spec
#print axioms kernel_eq_spec_pre
end LarkCertificate
