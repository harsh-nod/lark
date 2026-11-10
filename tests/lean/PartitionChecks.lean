import Lark.PartitionCollective
namespace PartitionChecks
open LarkNonlinear
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def geometry : Geometry := ⟨1, 64, 64⟩
def layout : Layout := ⟨[], [], []⟩
def program : List LarkCollective.Instr :=
  [.shuffle .up 0 0 (.const 1) 16, .scalar .halt]
def state (input : Nat → α) : State α where
  pc := fun t => if t < 16 then 0 else 1
  indices := fun _ _ => none
  regs := fun t r => if r = 0 then some (input t) else none
  memory := fun _ => none
  epochs := fun _ => {}
  trace := []

def observe (s : State α) :=
  (s.regs 0 0, s.regs 1 0, s.regs 15 0, s.regs 16 0, s.pc 0, s.pc 15, s.pc 16)

theorem snapshot (input : Nat → α) :
    (LarkPartitionCollective.runShuffle geometry program (List.range 16) (state input)).map observe =
      some (some (input 0), some (input 0), some (input 14), some (input 16), 1, 1, 1) := by rfl

theorem cohort (input : Nat → α) :
    LarkPartitionCollective.nextCohort program (List.range 64) (state input) =
      some (List.range 16) := by rfl

theorem warp (ops : Ops α) (input : Nat → α) :
    (LarkPartitionCollective.runWarp ops layout geometry ⟨1, 2, 1, 1⟩ program
      (List.range 64) 2 (state input)).map observe =
      some (some (input 0), some (input 0), some (input 14), some (input 16), 1, 1, 1) := by rfl

theorem incomplete (input : Nat → α) :
    LarkPartitionCollective.runShuffle geometry program (List.range 15) (state input) = none := by rfl

theorem fullWidthRejected (input : Nat → α) :
    LarkPartitionCollective.runShuffle geometry [.shuffle .up 0 0 (.const 1) 64]
      (List.range 16) (state input) = none := by rfl

theorem duplicated (input : Nat → α) :
    LarkPartitionCollective.runShuffle geometry program
      (List.range 16 ++ List.range 16) (state input) = none := by rfl

theorem mixedPc (input : Nat → α) :
    LarkPartitionCollective.runShuffle geometry program
      (List.range 17) (state input) = none := by rfl

#print axioms snapshot
#print axioms cohort
#print axioms warp
#print axioms incomplete
#print axioms fullWidthRejected
#print axioms duplicated
#print axioms mixedPc
end PartitionChecks
