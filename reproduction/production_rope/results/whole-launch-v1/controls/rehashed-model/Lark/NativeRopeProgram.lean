import Lark.InOut

/-! Native in-place vLLM rotary profile. These declarations bind full programs
and initialize both mutable buffers; complete launch correctness is separate. -/
namespace LarkNativeRope
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

structure Shape where
  rows : Nat
  positive : 0 < rows
  bound : rows < 65536

def layout (p : Shape) : Layout :=
  ⟨[⟨.output, p.rows * 4096⟩, ⟨.output, p.rows * 1024⟩,
    ⟨.input, p.rows * 128⟩], [], []⟩
def geometry (p : Shape) : Geometry := ⟨p.rows, 512, 64⟩
def fuel : Fuel := ⟨256, 1, 1, 1⟩
def mutableBuffers : List Nat := [0, 1]
def initial (p : Shape) (input : Nat → Nat → α) (outside : Location → Option α) : State α :=
  LarkInOut.initial (layout p) mutableBuffers input outside

def program (neox : Bool) : List Instr :=
  if neox then [
(.index 0 .bid),
(.index 1 .tid),
(.branch (.lt (.ivar (1)) (.const (2048))) 25),
(.index 2 (.div (.ivar (1)) (.const (64)))),
(.index 3 (.mod (.ivar (1)) (.const (64)))),
(.index 4 (.ivar (3))),
(.index 5 (.add (.ivar (3)) (.const (64)))),
(.index 6 (.add (.mul (.ivar (0)) (.const (128))) (.ivar (3)))),
(.index 7 (.add (.ivar (6)) (.const (64)))),
(.assign 0 (.un .fromHalf (.load .global 2 (.ivar (6))))),
(.assign 1 (.un .fromHalf (.load .global 2 (.ivar (7))))),
(.index 8 (.add (.add (.mul (.ivar (0)) (.const (4096))) (.mul (.ivar (2)) (.const (128)))) (.ivar (4)))),
(.index 9 (.add (.add (.mul (.ivar (0)) (.const (4096))) (.mul (.ivar (2)) (.const (128)))) (.ivar (5)))),
(.assign 2 (.un .fromHalf (.load .global 0 (.ivar (8))))),
(.assign 3 (.un .fromHalf (.load .global 0 (.ivar (9))))),
(.assign 4 (.bin .mul (.reg (2)) (.reg (0)))),
(.assign 5 (.bin .mul (.reg (3)) (.reg (1)))),
(.assign 6 (.bin .mul (.reg (3)) (.reg (0)))),
(.assign 7 (.bin .mul (.reg (2)) (.reg (1)))),
(.assign 8 (.bin .sub (.reg (4)) (.reg (5)))),
(.assign 9 (.bin .add (.reg (6)) (.reg (7)))),
(.store .global 0 (.ivar (8)) (.un .toHalf (.reg (8)))),
(.store .global 0 (.ivar (9)) (.un .toHalf (.reg (9)))),
(.index 1 (.add (.ivar (1)) (.const (512)))),
(.jump 2),
(.index 10 .tid),
(.branch (.lt (.ivar (10)) (.const (512))) 49),
(.index 11 (.div (.ivar (10)) (.const (64)))),
(.index 12 (.mod (.ivar (10)) (.const (64)))),
(.index 13 (.ivar (12))),
(.index 14 (.add (.ivar (12)) (.const (64)))),
(.index 15 (.add (.mul (.ivar (0)) (.const (128))) (.ivar (12)))),
(.index 16 (.add (.ivar (15)) (.const (64)))),
(.assign 10 (.un .fromHalf (.load .global 2 (.ivar (15))))),
(.assign 11 (.un .fromHalf (.load .global 2 (.ivar (16))))),
(.index 17 (.add (.add (.mul (.ivar (0)) (.const (1024))) (.mul (.ivar (11)) (.const (128)))) (.ivar (13)))),
(.index 18 (.add (.add (.mul (.ivar (0)) (.const (1024))) (.mul (.ivar (11)) (.const (128)))) (.ivar (14)))),
(.assign 12 (.un .fromHalf (.load .global 1 (.ivar (17))))),
(.assign 13 (.un .fromHalf (.load .global 1 (.ivar (18))))),
(.assign 14 (.bin .mul (.reg (12)) (.reg (10)))),
(.assign 15 (.bin .mul (.reg (13)) (.reg (11)))),
(.assign 16 (.bin .mul (.reg (13)) (.reg (10)))),
(.assign 17 (.bin .mul (.reg (12)) (.reg (11)))),
(.assign 18 (.bin .sub (.reg (14)) (.reg (15)))),
(.assign 19 (.bin .add (.reg (16)) (.reg (17)))),
(.store .global 1 (.ivar (17)) (.un .toHalf (.reg (18)))),
(.store .global 1 (.ivar (18)) (.un .toHalf (.reg (19)))),
(.index 10 (.add (.ivar (10)) (.const (512)))),
(.jump 26),
.halt
  ] else [
(.index 0 .bid),
(.index 1 .tid),
(.branch (.lt (.ivar (1)) (.const (2048))) 25),
(.index 2 (.div (.ivar (1)) (.const (64)))),
(.index 3 (.mod (.ivar (1)) (.const (64)))),
(.index 4 (.mul (.const (2)) (.ivar (3)))),
(.index 5 (.add (.mul (.const (2)) (.ivar (3))) (.const (1)))),
(.index 6 (.add (.mul (.ivar (0)) (.const (128))) (.ivar (3)))),
(.index 7 (.add (.ivar (6)) (.const (64)))),
(.assign 0 (.un .fromHalf (.load .global 2 (.ivar (6))))),
(.assign 1 (.un .fromHalf (.load .global 2 (.ivar (7))))),
(.index 8 (.add (.add (.mul (.ivar (0)) (.const (4096))) (.mul (.ivar (2)) (.const (128)))) (.ivar (4)))),
(.index 9 (.add (.add (.mul (.ivar (0)) (.const (4096))) (.mul (.ivar (2)) (.const (128)))) (.ivar (5)))),
(.assign 2 (.un .fromHalf (.load .global 0 (.ivar (8))))),
(.assign 3 (.un .fromHalf (.load .global 0 (.ivar (9))))),
(.assign 4 (.bin .mul (.reg (2)) (.reg (0)))),
(.assign 5 (.bin .mul (.reg (3)) (.reg (1)))),
(.assign 6 (.bin .mul (.reg (3)) (.reg (0)))),
(.assign 7 (.bin .mul (.reg (2)) (.reg (1)))),
(.assign 8 (.bin .sub (.reg (4)) (.reg (5)))),
(.assign 9 (.bin .add (.reg (6)) (.reg (7)))),
(.store .global 0 (.ivar (8)) (.un .toHalf (.reg (8)))),
(.store .global 0 (.ivar (9)) (.un .toHalf (.reg (9)))),
(.index 1 (.add (.ivar (1)) (.const (512)))),
(.jump 2),
(.index 10 .tid),
(.branch (.lt (.ivar (10)) (.const (512))) 49),
(.index 11 (.div (.ivar (10)) (.const (64)))),
(.index 12 (.mod (.ivar (10)) (.const (64)))),
(.index 13 (.mul (.const (2)) (.ivar (12)))),
(.index 14 (.add (.mul (.const (2)) (.ivar (12))) (.const (1)))),
(.index 15 (.add (.mul (.ivar (0)) (.const (128))) (.ivar (12)))),
(.index 16 (.add (.ivar (15)) (.const (64)))),
(.assign 10 (.un .fromHalf (.load .global 2 (.ivar (15))))),
(.assign 11 (.un .fromHalf (.load .global 2 (.ivar (16))))),
(.index 17 (.add (.add (.mul (.ivar (0)) (.const (1024))) (.mul (.ivar (11)) (.const (128)))) (.ivar (13)))),
(.index 18 (.add (.add (.mul (.ivar (0)) (.const (1024))) (.mul (.ivar (11)) (.const (128)))) (.ivar (14)))),
(.assign 12 (.un .fromHalf (.load .global 1 (.ivar (17))))),
(.assign 13 (.un .fromHalf (.load .global 1 (.ivar (18))))),
(.assign 14 (.bin .mul (.reg (12)) (.reg (10)))),
(.assign 15 (.bin .mul (.reg (13)) (.reg (11)))),
(.assign 16 (.bin .mul (.reg (13)) (.reg (10)))),
(.assign 17 (.bin .mul (.reg (12)) (.reg (11)))),
(.assign 18 (.bin .sub (.reg (14)) (.reg (15)))),
(.assign 19 (.bin .add (.reg (16)) (.reg (17)))),
(.store .global 1 (.ivar (17)) (.un .toHalf (.reg (18)))),
(.store .global 1 (.ivar (18)) (.un .toHalf (.reg (19)))),
(.index 10 (.add (.ivar (10)) (.const (512)))),
(.jump 26),
.halt
  ]

theorem program_length (neox : Bool) : (program neox).length = 50 := by cases neox <;> decide
theorem final_halt (neox : Bool) : (program neox)[49]? = some .halt := by cases neox <;> decide
theorem query_loop (neox : Bool) :
    (program neox)[2]? = some (.branch (.lt (.ivar 1) (.const 2048)) 25) := by cases neox <;> decide
theorem key_loop (neox : Bool) :
    (program neox)[26]? = some (.branch (.lt (.ivar 10) (.const 512)) 49) := by cases neox <;> decide

theorem interface_valid (p : Shape) : LarkInOut.Valid (layout p) mutableBuffers := by
  constructor
  · decide
  · intro id hi
    simp [mutableBuffers] at hi
    rcases hi with rfl | rfl
    · exact ⟨⟨.output, p.rows * 4096⟩, rfl, rfl⟩
    · exact ⟨⟨.output, p.rows * 1024⟩, rfl, rfl⟩

theorem initial_query (p : Shape) (input : Nat → Nat → α) (outside : Location → Option α)
    (i : Nat) (hi : i < p.rows * 4096) :
    (initial p input outside).memory ⟨.global, 0, 0, i⟩ = some (input 0 i) :=
  LarkInOut.initial_mutable (layout p) mutableBuffers input outside 0 i
    ⟨.output, p.rows * 4096⟩ (by simp [mutableBuffers]) rfl rfl hi

theorem initial_key (p : Shape) (input : Nat → Nat → α) (outside : Location → Option α)
    (i : Nat) (hi : i < p.rows * 1024) :
    (initial p input outside).memory ⟨.global, 0, 1, i⟩ = some (input 1 i) :=
  LarkInOut.initial_mutable (layout p) mutableBuffers input outside 1 i
    ⟨.output, p.rows * 1024⟩ (by simp [mutableBuffers]) rfl rfl hi

theorem initial_cache (p : Shape) (input : Nat → Nat → α) (outside : Location → Option α)
    (i : Nat) (hi : i < p.rows * 128) :
    (initial p input outside).memory ⟨.global, 0, 2, i⟩ = some (input 2 i) :=
  LarkInOut.initial_readonly (layout p) mutableBuffers input outside 2 i
    ⟨.input, p.rows * 128⟩ rfl rfl hi

theorem cache_readonly (p : Shape) (t : Nat) (i : Int) :
    location (layout p) (geometry p) t .global 2 i true = none := by
  by_cases h : i < 0 <;>
    simp [location, layout, h, show (Role.input == Role.input) = true from rfl]

#print axioms program_length
#print axioms final_halt
#print axioms query_loop
#print axioms key_loop
#print axioms interface_valid
#print axioms initial_query
#print axioms initial_key
#print axioms initial_cache
#print axioms cache_readonly
end LarkNativeRope
