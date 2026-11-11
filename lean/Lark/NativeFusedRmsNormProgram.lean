import Lark.InOut
import Lark.PartitionCollective
import Lark.VectorStride

/-! Fixed development program and in-out interface. No full launch theorem is
asserted here; source execution and actual-trace classification remain separate.
-/
namespace LarkNativeFusedRmsNorm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

structure Shape where
  rows : Nat
  positive : 0 < rows
  bound : rows < 256

def layout (p : Shape) : Layout :=
  ⟨[⟨.output, p.rows * 16384⟩, ⟨.output, p.rows * 16384⟩, ⟨.input, 16384⟩], [32, 16384], []⟩
def geometry (p : Shape) : Geometry := ⟨p.rows, 1024, 64⟩
def fuel : Fuel := ⟨512, 8, 3, 1⟩
def mutableBuffers : List Nat := [0, 1]
def initial (p : Shape) (input : Nat → Nat → α) (outside : Location → Option α) : State α :=
  LarkInOut.initial (layout p) mutableBuffers input outside

def traversal (p : Shape) : LarkVectorStride.Shape :=
  ⟨p.rows, 16384, 1024, 8, p.positive, by decide, by decide, by decide,
    by decide, by have h := p.bound; omega⟩

def program : List LarkCollective.Instr := [
  (.scalar (.index 0 .bid)),
  (.scalar (.index 1 .tid)),
  (.scalar (.index 2 (.mod (.ivar (1)) (.const (32))))),
  (.scalar (.index 3 (.div (.ivar (1)) (.const (32))))),
  (.scalar (.assign 0 (.lit (0) 1))),
  (.scalar (.assign 1 (.lit (0) 1))),
  (.scalar (.index 4 (.const (0)))),
  (.scalar (.branch (.lt (.ivar (4)) (.const (2))) 23)),
  (.scalar (.index 5 (.const (0)))),
  (.scalar (.branch (.lt (.ivar (5)) (.const (8))) 21)),
  (.scalar (.index 6 (.add (.mul (.add (.mul (.ivar (4)) (.const (1024))) (.ivar (1))) (.const (8))) (.ivar (5))))),
  (.scalar (.index 7 (.add (.mul (.ivar (0)) (.const (16384))) (.ivar (6))))),
  (.scalar (.assign 2 (.un .fromHalf (.load .global 0 (.ivar (7)))))),
  (.scalar (.assign 3 (.un .fromHalf (.load .global 1 (.ivar (7)))))),
  (.scalar (.assign 2 (.bin .add (.reg (2)) (.reg (3))))),
  (.scalar (.assign 4 (.bin .mul (.reg (2)) (.reg (2))))),
  (.scalar (.assign 0 (.bin .add (.reg (0)) (.reg (4))))),
  (.scalar (.store .global 1 (.ivar (7)) (.un .toHalf (.reg (2))))),
  (.scalar (.store .shared 1 (.ivar (6)) (.reg (2)))),
  (.scalar (.index 5 (.add (.ivar (5)) (.const (1))))),
  (.scalar (.jump 9)),
  (.scalar (.index 4 (.add (.ivar (4)) (.const (1))))),
  (.scalar (.jump 7)),
  (.shuffle .xor 1 0 (.const (16)) 32),
  (.scalar (.assign 0 (.bin .add (.reg (0)) (.reg (1))))),
  (.shuffle .xor 1 0 (.const (8)) 32),
  (.scalar (.assign 0 (.bin .add (.reg (0)) (.reg (1))))),
  (.shuffle .xor 1 0 (.const (4)) 32),
  (.scalar (.assign 0 (.bin .add (.reg (0)) (.reg (1))))),
  (.shuffle .xor 1 0 (.const (2)) 32),
  (.scalar (.assign 0 (.bin .add (.reg (0)) (.reg (1))))),
  (.shuffle .xor 1 0 (.const (1)) 32),
  (.scalar (.assign 0 (.bin .add (.reg (0)) (.reg (1))))),
  (.scalar (.branch (.eq (.ivar (2)) (.const (0))) 35)),
  (.scalar (.store .shared 0 (.ivar (3)) (.reg (0)))),
  (.scalar (.barrier .block)),
  (.scalar (.branch (.lt (.ivar (1)) (.const (32))) 50)),
  (.scalar (.assign 0 (.load .shared 0 (.ivar (1))))),
  (.shuffle .xor 1 0 (.const (16)) 32),
  (.scalar (.assign 0 (.bin .add (.reg (0)) (.reg (1))))),
  (.shuffle .xor 1 0 (.const (8)) 32),
  (.scalar (.assign 0 (.bin .add (.reg (0)) (.reg (1))))),
  (.shuffle .xor 1 0 (.const (4)) 32),
  (.scalar (.assign 0 (.bin .add (.reg (0)) (.reg (1))))),
  (.shuffle .xor 1 0 (.const (2)) 32),
  (.scalar (.assign 0 (.bin .add (.reg (0)) (.reg (1))))),
  (.shuffle .xor 1 0 (.const (1)) 32),
  (.scalar (.assign 0 (.bin .add (.reg (0)) (.reg (1))))),
  (.scalar (.branch (.eq (.ivar (1)) (.const (0))) 50)),
  (.scalar (.store .shared 0 (.const (0)) (.reg (0)))),
  (.scalar (.barrier .block)),
  (.scalar (.assign 5 (.load .shared 0 (.const (0))))),
  (.scalar (.assign 6 (.bin .div (.reg (5)) (.lit (16384) 1)))),
  (.scalar (.assign 7 (.bin .add (.reg (6)) (.lit (1) 100000)))),
  (.scalar (.assign 8 (.un .rsqrt (.reg (7))))),
  (.scalar (.index 8 (.const (0)))),
  (.scalar (.branch (.lt (.ivar (8)) (.const (2))) 71)),
  (.scalar (.index 9 (.const (0)))),
  (.scalar (.branch (.lt (.ivar (9)) (.const (8))) 69)),
  (.scalar (.index 10 (.add (.mul (.add (.mul (.ivar (8)) (.const (1024))) (.ivar (1))) (.const (8))) (.ivar (9))))),
  (.scalar (.index 11 (.add (.mul (.ivar (0)) (.const (16384))) (.ivar (10))))),
  (.scalar (.assign 9 (.load .shared 1 (.ivar (10))))),
  (.scalar (.assign 10 (.un .fromHalf (.load .global 2 (.ivar (10)))))),
  (.scalar (.assign 11 (.bin .add (.lit (0) 1) (.reg (10))))),
  (.scalar (.assign 12 (.bin .mul (.reg (9)) (.reg (8))))),
  (.scalar (.assign 13 (.bin .mul (.reg (12)) (.reg (11))))),
  (.scalar (.store .global 0 (.ivar (11)) (.un .toHalf (.reg (13))))),
  (.scalar (.index 9 (.add (.ivar (9)) (.const (1))))),
  (.scalar (.jump 58)),
  (.scalar (.index 8 (.add (.ivar (8)) (.const (1))))),
  (.scalar (.jump 56)),
  (.scalar .halt)
]

theorem program_length : program.length = 72 := by decide
theorem first_barrier : program[35]? = some (.scalar (.barrier .block)) := by decide
theorem second_barrier : program[50]? = some (.scalar (.barrier .block)) := by decide
theorem final_halt : program[71]? = some (.scalar .halt) := by decide

theorem interface_valid (p : Shape) : LarkInOut.Valid (layout p) mutableBuffers := by
  constructor
  · decide
  · intro id hi
    simp [mutableBuffers] at hi
    rcases hi with rfl | rfl
    · exact ⟨⟨.output, p.rows * 16384⟩, rfl, rfl⟩
    · exact ⟨⟨.output, p.rows * 16384⟩, rfl, rfl⟩

theorem initial_values (p : Shape) (input : Nat → Nat → α) (outside : Location → Option α)
    (i : Nat) (hi : i < p.rows * 16384) :
    (initial p input outside).memory ⟨.global, 0, 0, i⟩ = some (input 0 i) ∧
    (initial p input outside).memory ⟨.global, 0, 1, i⟩ = some (input 1 i) := by
  constructor
  · exact LarkInOut.initial_mutable (layout p) mutableBuffers input outside 0 i
      ⟨.output, p.rows * 16384⟩ (by simp [mutableBuffers]) rfl rfl hi
  · exact LarkInOut.initial_mutable (layout p) mutableBuffers input outside 1 i
      ⟨.output, p.rows * 16384⟩ (by simp [mutableBuffers]) rfl rfl hi

theorem initial_weight (p : Shape) (input : Nat → Nat → α) (outside : Location → Option α)
    (i : Nat) (hi : i < 16384) :
    (initial p input outside).memory ⟨.global, 0, 2, i⟩ = some (input 2 i) :=
  LarkInOut.initial_readonly (layout p) mutableBuffers input outside 2 i
    ⟨.input, 16384⟩ rfl rfl hi

theorem readonly_weight (p : Shape) (t : Nat) (i : Int) :
    location (layout p) (geometry p) t .global 2 i true = none := by
  by_cases h : i < 0 <;>
    simp [location, layout, h, show (Role.input == Role.input) = true from rfl]

#print axioms program_length
#print axioms first_barrier
#print axioms second_barrier
#print axioms final_halt
#print axioms interface_valid
#print axioms initial_values
#print axioms initial_weight
#print axioms readonly_weight
end LarkNativeFusedRmsNorm
