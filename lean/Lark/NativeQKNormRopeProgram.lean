import Lark.PartitionCollective

/-! Closed native out-of-place Q32/K8/V8 fused RMSNorm + RoPE interface.
These are full source programs; complete execution/reference proofs are separate. -/
namespace LarkNativeQKNormRope
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

structure Shape where
  rows : Nat
  positive : 0 < rows
  bound : rows < 65536

def layout (p : Shape) : Layout :=
  ⟨[⟨.output, p.rows * 5120⟩, ⟨.input, p.rows * 6144⟩,
    ⟨.input, 128⟩, ⟨.input, 128⟩, ⟨.input, p.rows * 128⟩], [], []⟩
def geometry (p : Shape) : Geometry := ⟨p.rows * 5, 256, 64⟩
def fuel : Fuel := ⟨256, 16, 1, 1⟩

def program (neox : Bool) : List LarkCollective.Instr :=
  if neox then [
(.scalar (.index 0 (.add (.mul .bid (.const (8))) (.div .tid (.const (32)))))),
(.scalar (.index 1 (.div (.ivar (0)) (.const (40))))),
(.scalar (.index 2 (.mod (.ivar (0)) (.const (40))))),
(.scalar (.index 3 (.mod .tid (.const (32))))),
(.scalar (.index 4 (.mul (.ivar (3)) (.const (4))))),
(.scalar (.index 5 (.add (.add (.mul (.ivar (1)) (.const (6144))) (.mul (.ivar (2)) (.const (128)))) (.ivar (4))))),
(.scalar (.index 6 (.add (.add (.mul (.ivar (1)) (.const (5120))) (.mul (.ivar (2)) (.const (128)))) (.ivar (4))))),
(.scalar (.index 7 (.add (.ivar (5)) (.const (0))))),
(.scalar (.assign 0 (.un .fromHalf (.load .global 1 (.ivar (7)))))),
(.scalar (.index 8 (.add (.ivar (5)) (.const (1))))),
(.scalar (.assign 1 (.un .fromHalf (.load .global 1 (.ivar (8)))))),
(.scalar (.index 9 (.add (.ivar (5)) (.const (2))))),
(.scalar (.assign 2 (.un .fromHalf (.load .global 1 (.ivar (9)))))),
(.scalar (.index 10 (.add (.ivar (5)) (.const (3))))),
(.scalar (.assign 3 (.un .fromHalf (.load .global 1 (.ivar (10)))))),
(.scalar (.assign 4 (.lit (0) 1))),
(.scalar (.assign 5 (.bin .mul (.reg (0)) (.reg (0))))),
(.scalar (.assign 4 (.bin .add (.reg (4)) (.reg (5))))),
(.scalar (.assign 6 (.bin .mul (.reg (1)) (.reg (1))))),
(.scalar (.assign 4 (.bin .add (.reg (4)) (.reg (6))))),
(.scalar (.assign 7 (.bin .mul (.reg (2)) (.reg (2))))),
(.scalar (.assign 4 (.bin .add (.reg (4)) (.reg (7))))),
(.scalar (.assign 8 (.bin .mul (.reg (3)) (.reg (3))))),
(.scalar (.assign 4 (.bin .add (.reg (4)) (.reg (8))))),
(.shuffle .xor 9 4 (.const (16)) 32),
(.scalar (.assign 4 (.bin .add (.reg (4)) (.reg (9))))),
(.shuffle .xor 9 4 (.const (8)) 32),
(.scalar (.assign 4 (.bin .add (.reg (4)) (.reg (9))))),
(.shuffle .xor 9 4 (.const (4)) 32),
(.scalar (.assign 4 (.bin .add (.reg (4)) (.reg (9))))),
(.shuffle .xor 9 4 (.const (2)) 32),
(.scalar (.assign 4 (.bin .add (.reg (4)) (.reg (9))))),
(.shuffle .xor 9 4 (.const (1)) 32),
(.scalar (.assign 4 (.bin .add (.reg (4)) (.reg (9))))),
(.scalar (.assign 10 (.bin .div (.reg (4)) (.lit (128) 1)))),
(.scalar (.assign 11 (.bin .add (.reg (10)) (.lit (1) 100000)))),
(.scalar (.assign 12 (.un .rsqrt (.reg (11))))),
(.scalar (.index 11 (.add (.ivar (4)) (.const (0))))),
(.scalar (.index 12 (.add (.ivar (4)) (.const (1))))),
(.scalar (.index 13 (.add (.ivar (4)) (.const (2))))),
(.scalar (.index 14 (.add (.ivar (4)) (.const (3))))),
(.scalar (.branch (.lt (.ivar (2)) (.const (32))) 47)),
(.scalar (.assign 13 (.un .fromHalf (.load .global 2 (.ivar (11)))))),
(.scalar (.assign 14 (.un .fromHalf (.load .global 2 (.ivar (12)))))),
(.scalar (.assign 15 (.un .fromHalf (.load .global 2 (.ivar (13)))))),
(.scalar (.assign 16 (.un .fromHalf (.load .global 2 (.ivar (14)))))),
(.scalar (.jump 51)),
(.scalar (.assign 13 (.un .fromHalf (.load .global 3 (.ivar (11)))))),
(.scalar (.assign 14 (.un .fromHalf (.load .global 3 (.ivar (12)))))),
(.scalar (.assign 15 (.un .fromHalf (.load .global 3 (.ivar (13)))))),
(.scalar (.assign 16 (.un .fromHalf (.load .global 3 (.ivar (14)))))),
(.scalar (.assign 17 (.bin .mul (.reg (12)) (.reg (13))))),
(.scalar (.assign 18 (.bin .mul (.reg (0)) (.reg (17))))),
(.scalar (.assign 19 (.bin .mul (.reg (12)) (.reg (14))))),
(.scalar (.assign 20 (.bin .mul (.reg (1)) (.reg (19))))),
(.scalar (.assign 21 (.bin .mul (.reg (12)) (.reg (15))))),
(.scalar (.assign 22 (.bin .mul (.reg (2)) (.reg (21))))),
(.scalar (.assign 23 (.bin .mul (.reg (12)) (.reg (16))))),
(.scalar (.assign 24 (.bin .mul (.reg (3)) (.reg (23))))),
(.scalar (.barrier .warp)),
(.shuffle .xor 25 18 (.const (16)) 32),
(.shuffle .xor 26 20 (.const (16)) 32),
(.shuffle .xor 27 22 (.const (16)) 32),
(.shuffle .xor 28 24 (.const (16)) 32),
(.scalar (.branch (.lt (.ivar (3)) (.const (16))) 69)),
(.scalar (.assign 25 (.bin .sub (.lit (0) 1) (.reg (25))))),
(.scalar (.assign 26 (.bin .sub (.lit (0) 1) (.reg (26))))),
(.scalar (.assign 27 (.bin .sub (.lit (0) 1) (.reg (27))))),
(.scalar (.assign 28 (.bin .sub (.lit (0) 1) (.reg (28))))),
(.scalar (.index 15 (.add (.mul (.ivar (1)) (.const (128))) (.mod (.add (.ivar (4)) (.const (0))) (.const (64)))))),
(.scalar (.index 16 (.add (.ivar (15)) (.const (64))))),
(.scalar (.assign 29 (.un .fromHalf (.load .global 4 (.ivar (15)))))),
(.scalar (.assign 30 (.un .fromHalf (.load .global 4 (.ivar (16)))))),
(.scalar (.assign 31 (.bin .mul (.reg (18)) (.reg (29))))),
(.scalar (.assign 32 (.bin .mul (.reg (25)) (.reg (30))))),
(.scalar (.assign 33 (.bin .add (.reg (31)) (.reg (32))))),
(.scalar (.index 17 (.add (.mul (.ivar (1)) (.const (128))) (.mod (.add (.ivar (4)) (.const (1))) (.const (64)))))),
(.scalar (.index 18 (.add (.ivar (17)) (.const (64))))),
(.scalar (.assign 34 (.un .fromHalf (.load .global 4 (.ivar (17)))))),
(.scalar (.assign 35 (.un .fromHalf (.load .global 4 (.ivar (18)))))),
(.scalar (.assign 36 (.bin .mul (.reg (20)) (.reg (34))))),
(.scalar (.assign 37 (.bin .mul (.reg (26)) (.reg (35))))),
(.scalar (.assign 38 (.bin .add (.reg (36)) (.reg (37))))),
(.scalar (.index 19 (.add (.mul (.ivar (1)) (.const (128))) (.mod (.add (.ivar (4)) (.const (2))) (.const (64)))))),
(.scalar (.index 20 (.add (.ivar (19)) (.const (64))))),
(.scalar (.assign 39 (.un .fromHalf (.load .global 4 (.ivar (19)))))),
(.scalar (.assign 40 (.un .fromHalf (.load .global 4 (.ivar (20)))))),
(.scalar (.assign 41 (.bin .mul (.reg (22)) (.reg (39))))),
(.scalar (.assign 42 (.bin .mul (.reg (27)) (.reg (40))))),
(.scalar (.assign 43 (.bin .add (.reg (41)) (.reg (42))))),
(.scalar (.index 21 (.add (.mul (.ivar (1)) (.const (128))) (.mod (.add (.ivar (4)) (.const (3))) (.const (64)))))),
(.scalar (.index 22 (.add (.ivar (21)) (.const (64))))),
(.scalar (.assign 44 (.un .fromHalf (.load .global 4 (.ivar (21)))))),
(.scalar (.assign 45 (.un .fromHalf (.load .global 4 (.ivar (22)))))),
(.scalar (.assign 46 (.bin .mul (.reg (24)) (.reg (44))))),
(.scalar (.assign 47 (.bin .mul (.reg (28)) (.reg (45))))),
(.scalar (.assign 48 (.bin .add (.reg (46)) (.reg (47))))),
(.scalar (.barrier .warp)),
(.scalar (.index 23 (.add (.ivar (6)) (.const (0))))),
(.scalar (.store .global 0 (.ivar (23)) (.un .toHalf (.reg (33))))),
(.scalar (.index 24 (.add (.ivar (6)) (.const (1))))),
(.scalar (.store .global 0 (.ivar (24)) (.un .toHalf (.reg (38))))),
(.scalar (.index 25 (.add (.ivar (6)) (.const (2))))),
(.scalar (.store .global 0 (.ivar (25)) (.un .toHalf (.reg (43))))),
(.scalar (.index 26 (.add (.ivar (6)) (.const (3))))),
(.scalar (.store .global 0 (.ivar (26)) (.un .toHalf (.reg (48))))),
(.scalar .halt)
] else [
(.scalar (.index 0 (.add (.mul .bid (.const (8))) (.div .tid (.const (32)))))),
(.scalar (.index 1 (.div (.ivar (0)) (.const (40))))),
(.scalar (.index 2 (.mod (.ivar (0)) (.const (40))))),
(.scalar (.index 3 (.mod .tid (.const (32))))),
(.scalar (.index 4 (.mul (.ivar (3)) (.const (4))))),
(.scalar (.index 5 (.add (.add (.mul (.ivar (1)) (.const (6144))) (.mul (.ivar (2)) (.const (128)))) (.ivar (4))))),
(.scalar (.index 6 (.add (.add (.mul (.ivar (1)) (.const (5120))) (.mul (.ivar (2)) (.const (128)))) (.ivar (4))))),
(.scalar (.index 7 (.add (.ivar (5)) (.const (0))))),
(.scalar (.assign 0 (.un .fromHalf (.load .global 1 (.ivar (7)))))),
(.scalar (.index 8 (.add (.ivar (5)) (.const (1))))),
(.scalar (.assign 1 (.un .fromHalf (.load .global 1 (.ivar (8)))))),
(.scalar (.index 9 (.add (.ivar (5)) (.const (2))))),
(.scalar (.assign 2 (.un .fromHalf (.load .global 1 (.ivar (9)))))),
(.scalar (.index 10 (.add (.ivar (5)) (.const (3))))),
(.scalar (.assign 3 (.un .fromHalf (.load .global 1 (.ivar (10)))))),
(.scalar (.assign 4 (.lit (0) 1))),
(.scalar (.assign 5 (.bin .mul (.reg (0)) (.reg (0))))),
(.scalar (.assign 4 (.bin .add (.reg (4)) (.reg (5))))),
(.scalar (.assign 6 (.bin .mul (.reg (1)) (.reg (1))))),
(.scalar (.assign 4 (.bin .add (.reg (4)) (.reg (6))))),
(.scalar (.assign 7 (.bin .mul (.reg (2)) (.reg (2))))),
(.scalar (.assign 4 (.bin .add (.reg (4)) (.reg (7))))),
(.scalar (.assign 8 (.bin .mul (.reg (3)) (.reg (3))))),
(.scalar (.assign 4 (.bin .add (.reg (4)) (.reg (8))))),
(.shuffle .xor 9 4 (.const (16)) 32),
(.scalar (.assign 4 (.bin .add (.reg (4)) (.reg (9))))),
(.shuffle .xor 9 4 (.const (8)) 32),
(.scalar (.assign 4 (.bin .add (.reg (4)) (.reg (9))))),
(.shuffle .xor 9 4 (.const (4)) 32),
(.scalar (.assign 4 (.bin .add (.reg (4)) (.reg (9))))),
(.shuffle .xor 9 4 (.const (2)) 32),
(.scalar (.assign 4 (.bin .add (.reg (4)) (.reg (9))))),
(.shuffle .xor 9 4 (.const (1)) 32),
(.scalar (.assign 4 (.bin .add (.reg (4)) (.reg (9))))),
(.scalar (.assign 10 (.bin .div (.reg (4)) (.lit (128) 1)))),
(.scalar (.assign 11 (.bin .add (.reg (10)) (.lit (1) 100000)))),
(.scalar (.assign 12 (.un .rsqrt (.reg (11))))),
(.scalar (.index 11 (.add (.ivar (4)) (.const (0))))),
(.scalar (.index 12 (.add (.ivar (4)) (.const (1))))),
(.scalar (.index 13 (.add (.ivar (4)) (.const (2))))),
(.scalar (.index 14 (.add (.ivar (4)) (.const (3))))),
(.scalar (.branch (.lt (.ivar (2)) (.const (32))) 47)),
(.scalar (.assign 13 (.un .fromHalf (.load .global 2 (.ivar (11)))))),
(.scalar (.assign 14 (.un .fromHalf (.load .global 2 (.ivar (12)))))),
(.scalar (.assign 15 (.un .fromHalf (.load .global 2 (.ivar (13)))))),
(.scalar (.assign 16 (.un .fromHalf (.load .global 2 (.ivar (14)))))),
(.scalar (.jump 51)),
(.scalar (.assign 13 (.un .fromHalf (.load .global 3 (.ivar (11)))))),
(.scalar (.assign 14 (.un .fromHalf (.load .global 3 (.ivar (12)))))),
(.scalar (.assign 15 (.un .fromHalf (.load .global 3 (.ivar (13)))))),
(.scalar (.assign 16 (.un .fromHalf (.load .global 3 (.ivar (14)))))),
(.scalar (.assign 17 (.bin .mul (.reg (12)) (.reg (13))))),
(.scalar (.assign 18 (.bin .mul (.reg (0)) (.reg (17))))),
(.scalar (.assign 19 (.bin .mul (.reg (12)) (.reg (14))))),
(.scalar (.assign 20 (.bin .mul (.reg (1)) (.reg (19))))),
(.scalar (.assign 21 (.bin .mul (.reg (12)) (.reg (15))))),
(.scalar (.assign 22 (.bin .mul (.reg (2)) (.reg (21))))),
(.scalar (.assign 23 (.bin .mul (.reg (12)) (.reg (16))))),
(.scalar (.assign 24 (.bin .mul (.reg (3)) (.reg (23))))),
(.scalar (.index 15 (.add (.add (.mul (.ivar (1)) (.const (128))) (.mul (.ivar (3)) (.const (2)))) (.const (0))))),
(.scalar (.index 16 (.add (.ivar (15)) (.const (64))))),
(.scalar (.assign 25 (.un .fromHalf (.load .global 4 (.ivar (15)))))),
(.scalar (.assign 26 (.un .fromHalf (.load .global 4 (.ivar (16)))))),
(.scalar (.assign 27 (.bin .mul (.reg (18)) (.reg (25))))),
(.scalar (.assign 28 (.bin .mul (.reg (20)) (.reg (26))))),
(.scalar (.assign 29 (.bin .mul (.reg (18)) (.reg (26))))),
(.scalar (.assign 30 (.bin .mul (.reg (20)) (.reg (25))))),
(.scalar (.assign 31 (.bin .sub (.reg (27)) (.reg (28))))),
(.scalar (.assign 32 (.bin .add (.reg (29)) (.reg (30))))),
(.scalar (.index 17 (.add (.add (.mul (.ivar (1)) (.const (128))) (.mul (.ivar (3)) (.const (2)))) (.const (1))))),
(.scalar (.index 18 (.add (.ivar (17)) (.const (64))))),
(.scalar (.assign 33 (.un .fromHalf (.load .global 4 (.ivar (17)))))),
(.scalar (.assign 34 (.un .fromHalf (.load .global 4 (.ivar (18)))))),
(.scalar (.assign 35 (.bin .mul (.reg (22)) (.reg (33))))),
(.scalar (.assign 36 (.bin .mul (.reg (24)) (.reg (34))))),
(.scalar (.assign 37 (.bin .mul (.reg (22)) (.reg (34))))),
(.scalar (.assign 38 (.bin .mul (.reg (24)) (.reg (33))))),
(.scalar (.assign 39 (.bin .sub (.reg (35)) (.reg (36))))),
(.scalar (.assign 40 (.bin .add (.reg (37)) (.reg (38))))),
(.scalar (.index 19 (.add (.ivar (6)) (.const (0))))),
(.scalar (.store .global 0 (.ivar (19)) (.un .toHalf (.reg (31))))),
(.scalar (.index 20 (.add (.ivar (6)) (.const (1))))),
(.scalar (.store .global 0 (.ivar (20)) (.un .toHalf (.reg (32))))),
(.scalar (.index 21 (.add (.ivar (6)) (.const (2))))),
(.scalar (.store .global 0 (.ivar (21)) (.un .toHalf (.reg (39))))),
(.scalar (.index 22 (.add (.ivar (6)) (.const (3))))),
(.scalar (.store .global 0 (.ivar (22)) (.un .toHalf (.reg (40))))),
(.scalar .halt)
]

def isShuffle : LarkCollective.Instr → Bool
  | .shuffle .. => true
  | _ => false
def isWarpBarrier : LarkCollective.Instr → Bool
  | .scalar (.barrier .warp) => true
  | _ => false

theorem program_length (neox : Bool) : (program neox).length = if neox then 107 else 88 := by
  cases neox <;> decide
theorem program_shuffles (neox : Bool) : ((program neox).filter isShuffle).length = if neox then 9 else 5 := by
  cases neox <;> decide
theorem program_warp_barriers (neox : Bool) : ((program neox).filter isWarpBarrier).length = if neox then 2 else 0 := by
  cases neox <;> decide
theorem program_halt (neox : Bool) : (program neox).getLast? = some (.scalar .halt) := by
  cases neox <;> decide
theorem native_threads (p : Shape) : (geometry p).grid * (geometry p).block = p.rows * 1280 := by
  simp [geometry, Nat.mul_assoc]
theorem native_complete_waves (p : Shape) :
    (geometry p).block % (geometry p).warp = 0 ∧ (geometry p).block / (geometry p).warp = 4 := by
  change (256 : Nat) % 64 = 0 ∧ (256 : Nat) / 64 = 4
  decide
theorem output_size (p : Shape) : (layout p).global[0]? = some ⟨.output, p.rows * 5120⟩ := rfl

#print axioms program_length
#print axioms program_shuffles
#print axioms program_warp_barriers
#print axioms program_halt
#print axioms native_threads
#print axioms native_complete_waves
#print axioms output_size
end LarkNativeQKNormRope
