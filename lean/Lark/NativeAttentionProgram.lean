import Lark.Nonlinear

/-! Fixed native tiled attention development program. Identity and layout facts
are components; no whole-launch correctness theorem is asserted here. -/
namespace LarkNativeAttention
open LarkNonlinear
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

structure Shape where
  groups : Nat
  positive : 0 < groups
  bound : groups ≤ 65535

def layout (p : Shape) : Layout :=
  ⟨[⟨.output, p.groups * 32768⟩, ⟨.input, p.groups * 32768⟩,
    ⟨.input, p.groups * 32768⟩, ⟨.input, p.groups * 32768⟩],
    [8192, 8192, 8192, 1024], [4, 4]⟩
def geometry (p : Shape) : Geometry := ⟨p.groups, 32, 64⟩
def fuel : Fuel := ⟨1000000, 1, 9, 1⟩

/-- This fixed IR was lowered once from the complete pinned development source. -/
def program : List Instr := [
  (.index 0 .bid),
  (.index 1 .tid),
  (.index 2 (.mul (.ivar (0)) (.const (32768)))),
  (.index 3 (.const (0))),
  (.branch (.lt (.ivar (3)) (.const (4))) 12),
  (.index 4 (.const (0))),
  (.branch (.lt (.ivar (4)) (.const (256))) 10),
  (.store .global 0 (.add (.add (.ivar (2)) (.mul (.add (.mul (.ivar (3)) (.const (32))) (.ivar (1))) (.const (256)))) (.ivar (4))) (.un .toHalf (.lit (0) 1))),
  (.index 4 (.add (.ivar (4)) (.const (1)))),
  (.jump 6),
  (.index 3 (.add (.ivar (3)) (.const (1)))),
  (.jump 4),
  (.index 5 (.const (0))),
  (.branch (.lt (.ivar (5)) (.const (4))) 90),
  (.index 6 (.const (0))),
  (.branch (.lt (.ivar (6)) (.const (256))) 20),
  (.store .shared 1 (.add (.mul (.ivar (1)) (.const (256))) (.ivar (6))) (.un .fromHalf (.load .global 2 (.add (.add (.add (.ivar (2)) (.mul (.ivar (5)) (.const (8192)))) (.mul (.ivar (1)) (.const (256)))) (.ivar (6)))))),
  (.store .shared 2 (.add (.mul (.ivar (1)) (.const (256))) (.ivar (6))) (.un .fromHalf (.load .global 3 (.add (.add (.add (.ivar (2)) (.mul (.ivar (5)) (.const (8192)))) (.mul (.ivar (1)) (.const (256)))) (.ivar (6)))))),
  (.index 6 (.add (.ivar (6)) (.const (1)))),
  (.jump 15),
  (.barrier .block),
  (.index 7 (.const (0))),
  (.branch (.lt (.ivar (7)) (.const (4))) 87),
  (.index 8 (.const (0))),
  (.branch (.lt (.ivar (8)) (.const (256))) 28),
  (.store .shared 0 (.add (.mul (.ivar (1)) (.const (256))) (.ivar (8))) (.un .fromHalf (.load .global 1 (.add (.add (.add (.ivar (2)) (.mul (.ivar (7)) (.const (8192)))) (.mul (.ivar (1)) (.const (256)))) (.ivar (8)))))),
  (.index 8 (.add (.ivar (8)) (.const (1)))),
  (.jump 24),
  (.assign 0 (.lit (0) 1)),
  (.index 9 (.const (0))),
  (.branch (.lt (.ivar (9)) (.const (32))) 48),
  (.assign 1 (.lit (0) 1)),
  (.index 10 (.const (0))),
  (.branch (.lt (.ivar (10)) (.const (256))) 40),
  (.assign 2 (.load .shared 0 (.add (.mul (.ivar (1)) (.const (256))) (.ivar (10))))),
  (.assign 3 (.load .shared 1 (.add (.mul (.ivar (9)) (.const (256))) (.ivar (10))))),
  (.assign 4 (.bin .mul (.reg (2)) (.reg (3)))),
  (.assign 1 (.bin .add (.reg (1)) (.reg (4)))),
  (.index 10 (.add (.ivar (10)) (.const (1)))),
  (.jump 33),
  (.assign 1 (.bin .mul (.reg (1)) (.lit (1) 16))),
  (.store .shared 3 (.add (.mul (.ivar (1)) (.const (32))) (.ivar (9))) (.reg (1))),
  (.branch (.eq (.ivar (9)) (.const (0))) 45),
  (.assign 0 (.reg (1))),
  (.jump 46),
  (.assign 0 (.bin .max (.reg (0)) (.reg (1)))),
  (.index 9 (.add (.ivar (9)) (.const (1)))),
  (.jump 30),
  (.assign 5 (.lit (0) 1)),
  (.index 11 (.const (0))),
  (.branch (.lt (.ivar (11)) (.const (32))) 56),
  (.assign 6 (.un .exp (.bin .sub (.load .shared 3 (.add (.mul (.ivar (1)) (.const (32))) (.ivar (11)))) (.reg (0))))),
  (.store .shared 3 (.add (.mul (.ivar (1)) (.const (32))) (.ivar (11))) (.reg (6))),
  (.assign 5 (.bin .add (.reg (5)) (.reg (6)))),
  (.index 11 (.add (.ivar (11)) (.const (1)))),
  (.jump 50),
  (.assign 7 (.reg (0))),
  (.assign 8 (.lit (0) 1)),
  (.branch (.lt (.const (0)) (.ivar (5))) 61),
  (.assign 7 (.load .local 0 (.ivar (7)))),
  (.assign 8 (.load .local 1 (.ivar (7)))),
  (.assign 9 (.bin .max (.reg (7)) (.reg (0)))),
  (.assign 10 (.un .exp (.bin .sub (.reg (7)) (.reg (9))))),
  (.assign 11 (.un .exp (.bin .sub (.reg (0)) (.reg (9))))),
  (.assign 12 (.bin .add (.bin .mul (.reg (10)) (.reg (8))) (.bin .mul (.reg (11)) (.reg (5))))),
  (.index 12 (.const (0))),
  (.branch (.lt (.ivar (12)) (.const (256))) 83),
  (.assign 13 (.lit (0) 1)),
  (.index 13 (.const (0))),
  (.branch (.lt (.ivar (13)) (.const (32))) 76),
  (.assign 14 (.load .shared 3 (.add (.mul (.ivar (1)) (.const (32))) (.ivar (13))))),
  (.assign 15 (.load .shared 2 (.add (.mul (.ivar (13)) (.const (256))) (.ivar (12))))),
  (.assign 16 (.bin .mul (.reg (14)) (.reg (15)))),
  (.assign 13 (.bin .add (.reg (13)) (.reg (16)))),
  (.index 13 (.add (.ivar (13)) (.const (1)))),
  (.jump 69),
  (.assign 17 (.un .fromHalf (.load .global 0 (.add (.add (.add (.ivar (2)) (.mul (.ivar (7)) (.const (8192)))) (.mul (.ivar (1)) (.const (256)))) (.ivar (12)))))),
  (.assign 18 (.bin .mul (.bin .mul (.reg (8)) (.reg (10))) (.reg (17)))),
  (.assign 19 (.bin .mul (.reg (11)) (.reg (13)))),
  (.assign 20 (.bin .mul (.bin .div (.lit (1) 1) (.reg (12))) (.bin .add (.reg (18)) (.reg (19))))),
  (.store .global 0 (.add (.add (.add (.ivar (2)) (.mul (.ivar (7)) (.const (8192)))) (.mul (.ivar (1)) (.const (256)))) (.ivar (12))) (.un .toHalf (.reg (20)))),
  (.index 12 (.add (.ivar (12)) (.const (1)))),
  (.jump 66),
  (.store .local 0 (.ivar (7)) (.reg (9))),
  (.store .local 1 (.ivar (7)) (.reg (12))),
  (.index 7 (.add (.ivar (7)) (.const (1)))),
  (.jump 22),
  (.barrier .block),
  (.index 5 (.add (.ivar (5)) (.const (1)))),
  (.jump 13),
  .halt
]

theorem program_length : program.length = 91 := by decide
theorem load_barrier : program[20]? = some (.barrier .block) := by decide
theorem tile_barrier : program[87]? = some (.barrier .block) := by decide
theorem halt : program[90]? = some .halt := by decide

theorem global_span_int32 (p : Shape) : p.groups * 32768 < 2147483648 := by
  have hb := p.bound
  omega

#print axioms program_length
#print axioms global_span_int32
end LarkNativeAttention
