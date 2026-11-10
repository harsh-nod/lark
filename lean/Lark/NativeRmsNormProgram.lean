import Lark.PartitionCollective
import Lark.ReductionFootprint

/-! Fixed source program for the development native RMSNorm case.
This module binds the actual IR and geometry; it does not assert completion.
-/
namespace LarkNativeRmsNorm
open LarkNonlinear
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

structure Shape where
  rows : Nat
  positive : 0 < rows
  bound : rows < 256

def traversal (p : Shape) : LarkVectorStride.Shape :=
  ⟨p.rows, 16384, 1024, 8, p.positive, by decide, by decide, by decide,
    by decide, by have h := p.bound; omega⟩

def layout (p : Shape) : Layout :=
  ⟨[⟨.output, p.rows * 16384⟩, ⟨.input, p.rows * 16384⟩, ⟨.input, 16384⟩], [16, 1], []⟩
def geometry (p : Shape) : Geometry := ⟨p.rows, 1024, 64⟩
def fuel : Fuel := ⟨256, 8, 3, 1⟩
def columnIndex (v c : Nat) : Index := .add (.mul (.ivar v) (.const 8)) (.ivar c)
def rowIndex (v c : Nat) : Index :=
  .add (.add (.mul (.ivar 0) (.const 16384)) (.mul (.ivar v) (.const 8))) (.ivar c)

def stage (pc width : Nat) (bound : Index) (distance : Nat) : List LarkCollective.Instr :=
  [.shuffle .down 1 0 (.const (distance : Int)) width,
   .scalar (.branch (.lt (.add (.ivar 2) (.const (distance : Int))) bound) (pc + 3)),
   .scalar (.assign 0 (.bin .add (.reg 0) (.reg 1)))]

def program : List LarkCollective.Instr :=
  [.scalar (.index 0 .bid), .scalar (.index 1 .tid),
   .scalar (.index 2 (.mod (.ivar 1) (.const 64))),
   .scalar (.index 3 (.div (.ivar 1) (.const 64))),
   .scalar (.index 4 (.sub (.const 1024) (.mul (.ivar 3) (.const 64)))),
   .scalar (.assign 0 (.lit 0 1)), .scalar (.assign 1 (.lit 0 1)),
   .scalar (.index 5 (.ivar 1)),
   .scalar (.branch (.lt (.ivar 5) (.const 2048)) 18),
   .scalar (.index 6 (.const 0)),
   .scalar (.branch (.lt (.ivar 6) (.const 8)) 16),
   .scalar (.assign 2 (.un .fromHalf (.load .global 1 (rowIndex 5 6)))),
   .scalar (.assign 3 (.bin .mul (.reg 2) (.reg 2))),
   .scalar (.assign 0 (.bin .add (.reg 0) (.reg 3))),
   .scalar (.index 6 (.add (.ivar 6) (.const 1))), .scalar (.jump 10),
   .scalar (.index 5 (.add (.ivar 5) (.const 1024))), .scalar (.jump 8)] ++
  (List.range 6).flatMap (fun n => stage (18 + 3 * n) 64 (.ivar 4) (2 ^ n)) ++
  [.scalar (.branch (.eq (.ivar 2) (.const 0)) 38),
   .scalar (.store .shared 0 (.ivar 3) (.reg 0)), .scalar (.barrier .block),
   .scalar (.branch (.lt (.ivar 1) (.const 16)) 55),
   .scalar (.assign 0 (.load .shared 0 (.ivar 2)))] ++
  (List.range 4).flatMap (fun n => stage (41 + 3 * n) 16 (.const 16) (2 ^ n)) ++
  [.scalar (.branch (.eq (.ivar 1) (.const 0)) 55),
   .scalar (.store .shared 1 (.const 0)
     (.un .rsqrt (.bin .add (.bin .div (.reg 0) (.lit 16384 1)) (.lit 1 100000)))),
   .scalar (.barrier .block), .scalar (.assign 4 (.load .shared 1 (.const 0))),
   .scalar (.index 7 (.ivar 1)),
   .scalar (.branch (.lt (.ivar 7) (.const 2048)) 70),
   .scalar (.index 8 (.const 0)),
   .scalar (.branch (.lt (.ivar 8) (.const 8)) 68),
   .scalar (.assign 5 (.un .fromHalf (.load .global 1 (rowIndex 7 8)))),
   .scalar (.assign 6 (.un .fromHalf (.load .global 2 (columnIndex 7 8)))),
   .scalar (.assign 7 (.bin .mul (.reg 5) (.reg 4))),
   .scalar (.assign 8 (.bin .mul (.reg 7) (.reg 6))),
   .scalar (.store .global 0 (rowIndex 7 8) (.un .toHalf (.reg 8))),
   .scalar (.index 8 (.add (.ivar 8) (.const 1))), .scalar (.jump 60),
   .scalar (.index 7 (.add (.ivar 7) (.const 1024))), .scalar (.jump 58),
   .scalar .halt]

theorem program_length : program.length = 71 := by decide
theorem first_barrier : program[38]? = some (.scalar (.barrier .block)) := by decide
theorem second_barrier : program[55]? = some (.scalar (.barrier .block)) := by decide
theorem halt : program[70]? = some (.scalar .halt) := by decide

theorem first_shuffle (n : Nat) (hn : n < 6) :
    program[18 + 3 * n]? = some (.shuffle .down 1 0 (.const (2 ^ n : Nat)) 64) := by
  have all : ∀ n : Fin 6,
      program[18 + 3 * n.val]? = some (.shuffle .down 1 0 (.const (2 ^ n.val : Nat)) 64) := by decide
  exact all ⟨n, hn⟩

theorem final_shuffle (n : Nat) (hn : n < 4) :
    program[41 + 3 * n]? = some (.shuffle .down 1 0 (.const (2 ^ n : Nat)) 16) := by
  have all : ∀ n : Fin 4,
      program[41 + 3 * n.val]? = some (.shuffle .down 1 0 (.const (2 ^ n.val : Nat)) 16) := by decide
  exact all ⟨n, hn⟩

theorem native_geometry (p : Shape) :
    geometry p = LarkReductionFootprint.geometry (traversal p) := rfl

#print axioms first_shuffle
#print axioms final_shuffle
end LarkNativeRmsNorm
