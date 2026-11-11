import Lark.NativeRopeCorrect
namespace LarkCertificate
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
def shape : LarkNativeRope.Shape := ⟨256, by decide, by decide⟩
def neox : Bool := true
def layout : Layout := ⟨[⟨.output, 1048576⟩, ⟨.output, 262144⟩, ⟨.input, 32768⟩], [], []⟩
def mutableBuffers : List Nat := [0, 1]
def geometry : Geometry := ⟨256, 512, 64⟩
def fuel : Fuel := ⟨256, 1, 1, 1⟩
def program : List Instr := [(.index 0 .bid), (.index 1 .tid), (.branch (.lt (.ivar (1)) (.const (2048))) 25), (.index 2 (.div (.ivar (1)) (.const (64)))), (.index 3 (.mod (.ivar (1)) (.const (64)))), (.index 4 (.ivar (3))), (.index 5 (.add (.ivar (3)) (.const (64)))), (.index 6 (.add (.mul (.ivar (0)) (.const (128))) (.ivar (3)))), (.index 7 (.add (.ivar (6)) (.const (64)))), (.assign 0 (.un .fromHalf (.load .global 2 (.ivar (6))))), (.assign 1 (.un .fromHalf (.load .global 2 (.ivar (7))))), (.index 8 (.add (.add (.mul (.ivar (0)) (.const (4096))) (.mul (.ivar (2)) (.const (128)))) (.ivar (4)))), (.index 9 (.add (.add (.mul (.ivar (0)) (.const (4096))) (.mul (.ivar (2)) (.const (128)))) (.ivar (5)))), (.assign 2 (.un .fromHalf (.load .global 0 (.ivar (8))))), (.assign 3 (.un .fromHalf (.load .global 0 (.ivar (9))))), (.assign 4 (.bin .mul (.reg (2)) (.reg (0)))), (.assign 5 (.bin .mul (.reg (3)) (.reg (1)))), (.assign 6 (.bin .mul (.reg (3)) (.reg (0)))), (.assign 7 (.bin .mul (.reg (2)) (.reg (1)))), (.assign 8 (.bin .sub (.reg (4)) (.reg (5)))), (.assign 9 (.bin .add (.reg (6)) (.reg (7)))), (.store .global 0 (.ivar (8)) (.un .toHalf (.reg (8)))), (.store .global 0 (.ivar (9)) (.un .toHalf (.reg (9)))), (.index 1 (.add (.ivar (1)) (.const (512)))), (.jump 2), (.index 10 .tid), (.branch (.lt (.ivar (10)) (.const (512))) 49), (.index 11 (.div (.ivar (10)) (.const (64)))), (.index 12 (.mod (.ivar (10)) (.const (64)))), (.index 13 (.ivar (12))), (.index 14 (.add (.ivar (12)) (.const (64)))), (.index 15 (.add (.mul (.ivar (0)) (.const (128))) (.ivar (12)))), (.index 16 (.add (.ivar (15)) (.const (64)))), (.assign 10 (.un .fromHalf (.load .global 2 (.ivar (15))))), (.assign 11 (.un .fromHalf (.load .global 2 (.ivar (16))))), (.index 17 (.add (.add (.mul (.ivar (0)) (.const (1024))) (.mul (.ivar (11)) (.const (128)))) (.ivar (13)))), (.index 18 (.add (.add (.mul (.ivar (0)) (.const (1024))) (.mul (.ivar (11)) (.const (128)))) (.ivar (14)))), (.assign 12 (.un .fromHalf (.load .global 1 (.ivar (17))))), (.assign 13 (.un .fromHalf (.load .global 1 (.ivar (18))))), (.assign 14 (.bin .mul (.reg (12)) (.reg (10)))), (.assign 15 (.bin .mul (.reg (13)) (.reg (11)))), (.assign 16 (.bin .mul (.reg (13)) (.reg (10)))), (.assign 17 (.bin .mul (.reg (12)) (.reg (11)))), (.assign 18 (.bin .sub (.reg (14)) (.reg (15)))), (.assign 19 (.bin .add (.reg (16)) (.reg (17)))), (.store .global 1 (.ivar (17)) (.un .toHalf (.reg (18)))), (.store .global 1 (.ivar (18)) (.un .toHalf (.reg (19)))), (.index 10 (.add (.ivar (10)) (.const (512)))), (.jump 26), .halt]
-- The complete closed two-output reference AST is checked before interpretation.
def reference (ops : Ops α) (input : Nat → Nat → α) (buffer row col : Nat) : α :=
  let rowWidth := if buffer = 0 then 4096 else 1024
  let head := col / 128
  let j := if neox then col % 64 else col % 128 / 2
  let a := head * 128 + if neox then j else 2 * j
  let b := head * 128 + if neox then j + 64 else 2 * j + 1
  let x := ops.fromHalf (input buffer (row * rowWidth + a))
  let y := ops.fromHalf (input buffer (row * rowWidth + b))
  let c := ops.fromHalf (input 2 (row * 128 + j))
  let sn := ops.fromHalf (input 2 (row * 128 + j + 64))
  let imaginary := if neox then decide (64 ≤ col % 128) else decide (col % 2 = 1)
  ops.toHalf (if imaginary then ops.add (ops.mul y c) (ops.mul x sn) else ops.sub (ops.mul x c) (ops.mul y sn))
def spec (ops : Ops α) (input : Nat → Nat → α) : List α :=
  (List.range (256 * 4096)).map (fun i => reference ops input 0 (i / 4096) (i % 4096)) ++
  (List.range (256 * 1024)).map (fun i => reference ops input 1 (i / 1024) (i % 1024))
theorem reference_data (ops : Ops α) (input : Nat → Nat → α) :
    spec ops input = LarkNativeRope.spec shape neox ops input := by rfl
theorem layout_data : layout = LarkNativeRope.layout shape := by rfl
theorem mutable_data : mutableBuffers = LarkNativeRope.mutableBuffers := by decide
theorem geometry_data : geometry = LarkNativeRope.geometry shape := by rfl
theorem fuel_data : fuel = LarkNativeRope.fuel := by rfl
theorem program_data : program = LarkNativeRope.program neox := by decide
theorem interface_data : LarkInOut.Valid layout mutableBuffers := by
  rw [layout_data, mutable_data]
  exact LarkNativeRope.interface_valid shape
theorem segmentation_data : program = LarkNativeRope.program neox := program_data
theorem segmentation (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) :
    runLaunch ops layout geometry fuel program (LarkInOut.initial layout mutableBuffers input outside) =
      some (LarkNativeRope.finalState shape neox ops input outside) := by
  rw [segmentation_data, layout_data, mutable_data, geometry_data, fuel_data]
  exact (LarkNativeRope.final_launch shape neox ops input outside).1
theorem race_free (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) :
    raceFree geometry (LarkNativeRope.finalState shape neox ops input outside).trace = true := by
  rw [geometry_data]
  exact LarkNativeRope.final_race_free shape neox ops input outside
theorem segment_equivalence (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) :
    extract layout (LarkNativeRope.finalState shape neox ops input outside) = some (spec ops input) := by
  rw [layout_data]
  exact (LarkNativeRope.final_extract shape neox ops input outside).trans (congrArg some (reference_data ops input).symm)
theorem kernel_eq_spec (ops : Ops α) :
    LarkInOutScalar.Correct ops layout mutableBuffers geometry fuel program (spec ops) := by
  refine ⟨interface_data, ?_⟩
  intro input outside
  exact ⟨LarkNativeRope.finalState shape neox ops input outside,
    segmentation ops input outside, race_free ops input outside, segment_equivalence ops input outside⟩
theorem kernel_eq_spec_pre (ops : Ops α) (input : Nat → Nat → α) (s : State α)
    (pre : LarkInOut.StdPre layout mutableBuffers input s) :
    ∃ final, runLaunch ops layout geometry fuel program s = some final ∧
      raceFree geometry final.trace = true ∧ extract layout final = some (spec ops input) :=
  LarkInOutScalar.correct_from_pre ops layout mutableBuffers geometry fuel program (spec ops)
    (kernel_eq_spec ops) input s pre
#print axioms reference_data
#print axioms mutable_data
#print axioms program_data
#print axioms interface_data
#print axioms segmentation_data
#print axioms segmentation
#print axioms race_free
#print axioms segment_equivalence
#print axioms kernel_eq_spec
#print axioms kernel_eq_spec_pre
end LarkCertificate
