import Lark.PartitionCollective

/-! Fixed native FlashInfer RMSNorm program. Whole-source execution and
actual-trace classification are separate obligations, not proved here. -/
namespace LarkNativeFlashInferRmsNorm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

structure Shape where
  rows : Nat
  positive : 0 < rows
  bound : rows ≤ 131072

def layout (p : Shape) : Layout :=
  ⟨[⟨.output, p.rows * 16384⟩, ⟨.input, p.rows * 16384⟩,
    ⟨.input, 16384⟩], [32], []⟩
def geometry (p : Shape) : Geometry := ⟨p.rows, 1024, 64⟩
def fuel : Fuel := ⟨512, 8, 3, 1⟩

def program : List LarkCollective.Instr := [
  (.scalar (.index 0 .bid)),
  (.scalar (.index 1 .tid)),
  (.scalar (.index 2 (.mod (.ivar (1)) (.const (32))))),
  (.scalar (.index 3 (.div (.ivar (1)) (.const (32))))),
  (.scalar (.assign 0 (.lit (0) 1))),
  (.scalar (.assign 1 (.lit (0) 1))),
  (.scalar (.index 4 (.const (0)))),
  (.scalar (.branch (.lt (.ivar (4)) (.const (2))) 19)),
  (.scalar (.index 5 (.const (0)))),
  (.scalar (.branch (.lt (.ivar (5)) (.const (8))) 17)),
  (.scalar (.index 6 (.add (.mul (.add (.mul (.ivar (4)) (.const (1024))) (.ivar (1))) (.const (8))) (.ivar (5))))),
  (.scalar (.index 7 (.add (.mul (.ivar (0)) (.const (16384))) (.ivar (6))))),
  (.scalar (.assign 2 (.un .fromHalf (.load .global 1 (.ivar (7)))))),
  (.scalar (.assign 3 (.bin .mul (.reg (2)) (.reg (2))))),
  (.scalar (.assign 0 (.bin .add (.reg (0)) (.reg (3))))),
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
  (.scalar (.branch (.eq (.ivar (2)) (.const (0))) 31)),
  (.scalar (.store .shared 0 (.ivar (3)) (.reg (0)))),
  (.scalar (.barrier .block)),
  (.scalar (.branch (.lt (.ivar (1)) (.const (32))) 46)),
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
  (.scalar (.branch (.eq (.ivar (1)) (.const (0))) 46)),
  (.scalar (.store .shared 0 (.const (0)) (.reg (0)))),
  (.scalar (.barrier .block)),
  (.scalar (.assign 4 (.load .shared 0 (.const (0))))),
  (.scalar (.assign 5 (.bin .div (.reg (4)) (.lit (16384) 1)))),
  (.scalar (.assign 6 (.bin .add (.reg (5)) (.lit (1) 100000)))),
  (.scalar (.assign 7 (.un .rsqrt (.reg (6))))),
  (.scalar (.index 8 (.const (0)))),
  (.scalar (.branch (.lt (.ivar (8)) (.const (2))) 67)),
  (.scalar (.index 9 (.const (0)))),
  (.scalar (.branch (.lt (.ivar (9)) (.const (8))) 65)),
  (.scalar (.index 10 (.add (.mul (.add (.mul (.ivar (8)) (.const (1024))) (.ivar (1))) (.const (8))) (.ivar (9))))),
  (.scalar (.index 11 (.add (.mul (.ivar (0)) (.const (16384))) (.ivar (10))))),
  (.scalar (.assign 8 (.un .fromHalf (.load .global 1 (.ivar (11)))))),
  (.scalar (.assign 9 (.un .fromHalf (.load .global 2 (.ivar (10)))))),
  (.scalar (.assign 10 (.bin .add (.lit (0) 1) (.reg (9))))),
  (.scalar (.assign 11 (.bin .mul (.reg (8)) (.reg (7))))),
  (.scalar (.assign 12 (.bin .mul (.reg (11)) (.reg (10))))),
  (.scalar (.store .global 0 (.ivar (11)) (.un .toHalf (.reg (12))))),
  (.scalar (.index 9 (.add (.ivar (9)) (.const (1))))),
  (.scalar (.jump 54)),
  (.scalar (.index 8 (.add (.ivar (8)) (.const (1))))),
  (.scalar (.jump 52)),
  (.scalar .halt)
]

theorem program_length : program.length = 68 := by decide
theorem first_barrier : program[31]? = some (.scalar (.barrier .block)) := by decide
theorem second_barrier : program[46]? = some (.scalar (.barrier .block)) := by decide
theorem final_halt : program[67]? = some (.scalar .halt) := by decide

#print axioms program_length
#print axioms first_barrier
#print axioms second_barrier
#print axioms final_halt
end LarkNativeFlashInferRmsNorm
