import Lark.PtxMatrix

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/- The two additional operations in the unchanged compiled FP16 Linear source.
   Signed integers represent signed register bit patterns. cvt.s64.s32 preserves
   a guarded signed32 value; shl.b64 zero-fills, discards overflowing bits and
   clamps its unsigned32 shift amount to 64, then reinterprets the signed64
   destination. See NVIDIA PTX ISA 8.8 sections 9.7.8.8 and 9.7.9.21.
   https://docs.nvidia.com/cuda/archive/12.9.0/parallel-thread-execution/index.html
   This module is development evidence, not a complete kernel certificate. -/
namespace LarkPtxLinear
open LarkNonlinear LarkPtxPointwise
open LarkPtxDot (Machine setPointer setIndex32 setFloat unsigned32)
open LarkPtxMatrix (setIndex64)

inductive Instruction where
  | base : LarkPtxMatrix.Instruction → Instruction
  | signExtend32 : Nat → Nat → Instruction
  | shiftLeft64 : Nat → Nat → Nat → Instruction
  deriving DecidableEq, Repr

def signedBits64 (x : Int) : Int :=
  let bits := x % 18446744073709551616
  if bits < 9223372036854775808 then bits else bits - 18446744073709551616

def shiftLeftValue64 (x : Int) (count : Nat) : Int :=
  signedBits64 ((x % 18446744073709551616) * (2 : Int) ^ min count 64)

def execute (ops : Ops α) (layout : Layout) (g : Geometry) (t : Nat)
    (instruction : Instruction) (s : Machine α) : Option (Machine α) := do
  match instruction with
  | .base instruction => LarkPtxMatrix.execute ops layout g t instruction s
  | .signExtend32 d a =>
      let x ← s.registers.i32 a
      if signed32 x then some (setIndex64 s d x) else none
  | .shiftLeft64 d a count =>
      let x ← s.registers.i64 a
      if signed64 x ∧ count < 4294967296 then
        some (setIndex64 s d (shiftLeftValue64 x count))
      else none

def transition (ops : Ops α) (layout : Layout) (g : Geometry) (t : Nat)
    (program : List Instruction) (s : Machine α) : Option (Machine α) := do
  if s.registers.stopped then none else do
    let instruction ← program[s.pc]?
    execute ops layout g t instruction s

inductive Steps (ops : Ops α) (layout : Layout) (g : Geometry) (t : Nat)
    (program : List Instruction) : Machine α → Machine α → Prop where
  | refl (s) : Steps ops layout g t program s s
  | next {s u f} : transition ops layout g t program s = some u →
      Steps ops layout g t program u f → Steps ops layout g t program s f

theorem steps_trans (ops : Ops α) (layout : Layout) (g : Geometry) (t : Nat)
    (program : List Instruction) (s u f : Machine α)
    (first : Steps ops layout g t program s u) (second : Steps ops layout g t program u f) :
    Steps ops layout g t program s f := by
  induction first with
  | refl => exact second
  | next h _ ih => exact .next h (ih second)

theorem one_step (ops : Ops α) (layout : Layout) (g : Geometry) (t : Nat)
    (program : List Instruction) (s u : Machine α)
    (h : transition ops layout g t program s = some u) :
    Steps ops layout g t program s u := .next h (.refl u)

theorem transition_at (ops : Ops α) (layout : Layout) (g : Geometry) (t : Nat)
    (program : List Instruction) (s : Machine α) (instruction : Instruction)
    (hs : s.registers.stopped = false) (hf : program[s.pc]? = some instruction) :
    transition ops layout g t program s = execute ops layout g t instruction s := by
  simp [transition, hs, hf]

theorem base_step (ops : Ops α) (layout : Layout) (g : Geometry) (t : Nat)
    (instruction : LarkPtxMatrix.Instruction) (s : Machine α) :
    execute ops layout g t (.base instruction) s =
      LarkPtxMatrix.execute ops layout g t instruction s := rfl

theorem dot_step (ops : Ops α) (layout : Layout) (g : Geometry) (t : Nat)
    (instruction : LarkPtxDot.Instruction) (s : Machine α) :
    execute ops layout g t (.base (.base instruction)) s =
      LarkPtxDot.execute ops layout g t instruction s := rfl

theorem signExtend32_step (ops : Ops α) (layout : Layout) (g : Geometry)
    (t d a : Nat) (x : Int) (s : Machine α)
    (hx : s.registers.i32 a = some x) (hb : signed32 x) :
    execute ops layout g t (.signExtend32 d a) s = some (setIndex64 s d x) := by
  simp [execute, hx, hb]

theorem signExtend32_result_signed64 (x : Int) (hb : signed32 x) : signed64 x := by
  unfold signed32 at hb
  unfold signed64
  omega

theorem signedBits64_range (x : Int) : signed64 (signedBits64 x) := by
  have lo := Int.emod_nonneg x (by decide : (18446744073709551616 : Int) ≠ 0)
  have hi := Int.emod_lt_of_pos x (by decide : (0 : Int) < 18446744073709551616)
  by_cases h : x % 18446744073709551616 < 9223372036854775808
  · simp only [signedBits64, if_pos h, signed64]
    omega
  · simp only [signedBits64, if_neg h, signed64]
    omega

theorem shiftLeft64_step (ops : Ops α) (layout : Layout) (g : Geometry)
    (t d a count : Nat) (x : Int) (s : Machine α)
    (hx : s.registers.i64 a = some x) (hb : signed64 x ∧ count < 4294967296) :
    execute ops layout g t (.shiftLeft64 d a count) s =
      some (setIndex64 s d (shiftLeftValue64 x count)) := by
  simp [execute, hx, hb]

theorem shiftLeft64_result_signed64 (x : Int) (count : Nat) :
    signed64 (shiftLeftValue64 x count) := signedBits64_range _

theorem column_shift_value (column : Nat) (hc : column < 512) :
    shiftLeftValue64 (column : Int) 1 = ((2*column : Nat) : Int) := by
  have h1 : (column : Int) % 18446744073709551616 = (column : Int) := by omega
  have h2 : ((column : Int)*2) % 18446744073709551616 = (column : Int)*2 := by omega
  have h3 : (column : Int)*2 < 9223372036854775808 := by omega
  simp only [shiftLeftValue64, h1]
  change signedBits64 ((column : Int)*2) = _
  simp only [signedBits64, h2, if_pos h3, Int.natCast_mul]
  omega

theorem shift_negative_one : shiftLeftValue64 (-1) 1 = -2 := by decide
theorem shift_sign_bit : shiftLeftValue64 1 63 = -9223372036854775808 := by decide
theorem shift_width : shiftLeftValue64 (-1) 64 = 0 := by decide
theorem shift_clamped : shiftLeftValue64 (-1) 4294967295 = 0 := by decide

namespace Linear

def program : List Instruction := [
  (.base (.base (.parameter (27) (0)))),
  (.base (.base (.parameter (28) (1)))),
  (.base (.base (.parameter (26) (2)))),
  (.base (.base (.parameter (29) (3)))),
  (.base (.base (.toGlobal (53) (28)))),
  (.base (.base (.toGlobal (52) (27)))),
  (.base (.base (.toGlobal (3) (29)))),
  (.base (.base (.blockId (1)))),
  (.base (.shiftRightSigned32 5 1 31)),
  (.base (.shiftRightUnsigned32 6 5 23)),
  (.base (.base (.addSigned32 (7) (1) (.reg (6))))),
  (.base (.shiftRightSigned32 8 7 9)),
  (.base (.base (.shiftLeft32 (9) (8) (8)))),
  (.base (.andBits32 10 7 (.imm (-512)))),
  (.base (.subSigned32 11 1 (.reg (10)))),
  (.base (.base (.addSigned32 (12) (11) (.imm (7680))))),
  (.base (.mulWideUnsigned32 4 12 2)),
  (.base (.base (.addSigned32 (13) (11) (.imm (7168))))),
  (.base (.mulWideUnsigned32 5 13 2)),
  (.base (.base (.addSigned32 (14) (11) (.imm (6656))))),
  (.base (.mulWideUnsigned32 6 14 2)),
  (.base (.base (.addSigned32 (15) (11) (.imm (6144))))),
  (.base (.mulWideUnsigned32 7 15 2)),
  (.base (.base (.addSigned32 (16) (11) (.imm (5632))))),
  (.base (.mulWideUnsigned32 8 16 2)),
  (.base (.base (.addSigned32 (17) (11) (.imm (5120))))),
  (.base (.mulWideUnsigned32 9 17 2)),
  (.base (.base (.addSigned32 (18) (11) (.imm (4608))))),
  (.base (.mulWideUnsigned32 10 18 2)),
  (.base (.base (.addSigned32 (19) (11) (.imm (4096))))),
  (.base (.mulWideUnsigned32 11 19 2)),
  (.base (.base (.addSigned32 (20) (11) (.imm (3584))))),
  (.base (.mulWideUnsigned32 12 20 2)),
  (.base (.base (.addSigned32 (21) (11) (.imm (3072))))),
  (.base (.mulWideUnsigned32 13 21 2)),
  (.base (.base (.addSigned32 (22) (11) (.imm (2560))))),
  (.base (.mulWideUnsigned32 14 22 2)),
  (.base (.base (.addSigned32 (23) (11) (.imm (2048))))),
  (.base (.mulWideUnsigned32 15 23 2)),
  (.base (.base (.addSigned32 (24) (11) (.imm (1536))))),
  (.base (.mulWideUnsigned32 16 24 2)),
  (.base (.base (.addSigned32 (25) (11) (.imm (1024))))),
  (.base (.mulWideUnsigned32 17 25 2)),
  (.signExtend32 18 11),
  (.base (.base (.mulWideSigned32 (19) (11) (2)))),
  (.base (.base (.addSigned32 (26) (11) (.imm (512))))),
  (.base (.mulWideUnsigned32 20 26 2)),
  (.base (.base (.mulWideSigned32 (21) (9) (2)))),
  (.base (.base (.literalFloat (69) (0) (1)))),
  (.base (.base (.literal32 (27) (0)))),
  (.base (.base (.addSigned64 (30) (52) (.reg (21))))),
  (.base (.base (.loadHalf (1) (30) (0)))),
  (.base (.base (.fromHalf (4) (1)))),
  (.base (.base (.addSigned64 (31) (53) (.reg (19))))),
  (.base (.base (.loadHalf (2) (31) (0)))),
  (.base (.base (.fromHalf (5) (2)))),
  (.base (.base (.binaryFloat (36) .mul (4) (5)))),
  (.base (.base (.binaryFloat (37) .add (69) (36)))),
  (.base (.base (.loadHalf (3) (30) (2)))),
  (.base (.base (.fromHalf (6) (3)))),
  (.base (.base (.addSigned64 (32) (53) (.reg (20))))),
  (.base (.base (.loadHalf (4) (32) (0)))),
  (.base (.base (.fromHalf (7) (4)))),
  (.base (.base (.binaryFloat (38) .mul (6) (7)))),
  (.base (.base (.binaryFloat (39) .add (37) (38)))),
  (.base (.base (.loadHalf (5) (30) (4)))),
  (.base (.base (.fromHalf (8) (5)))),
  (.base (.base (.addSigned64 (33) (53) (.reg (17))))),
  (.base (.base (.loadHalf (6) (33) (0)))),
  (.base (.base (.fromHalf (9) (6)))),
  (.base (.base (.binaryFloat (40) .mul (8) (9)))),
  (.base (.base (.binaryFloat (41) .add (39) (40)))),
  (.base (.base (.loadHalf (7) (30) (6)))),
  (.base (.base (.fromHalf (10) (7)))),
  (.base (.base (.addSigned64 (34) (53) (.reg (16))))),
  (.base (.base (.loadHalf (8) (34) (0)))),
  (.base (.base (.fromHalf (11) (8)))),
  (.base (.base (.binaryFloat (42) .mul (10) (11)))),
  (.base (.base (.binaryFloat (43) .add (41) (42)))),
  (.base (.base (.loadHalf (9) (30) (8)))),
  (.base (.base (.fromHalf (12) (9)))),
  (.base (.base (.addSigned64 (35) (53) (.reg (15))))),
  (.base (.base (.loadHalf (10) (35) (0)))),
  (.base (.base (.fromHalf (13) (10)))),
  (.base (.base (.binaryFloat (44) .mul (12) (13)))),
  (.base (.base (.binaryFloat (45) .add (43) (44)))),
  (.base (.base (.loadHalf (11) (30) (10)))),
  (.base (.base (.fromHalf (14) (11)))),
  (.base (.base (.addSigned64 (36) (53) (.reg (14))))),
  (.base (.base (.loadHalf (12) (36) (0)))),
  (.base (.base (.fromHalf (15) (12)))),
  (.base (.base (.binaryFloat (46) .mul (14) (15)))),
  (.base (.base (.binaryFloat (47) .add (45) (46)))),
  (.base (.base (.loadHalf (13) (30) (12)))),
  (.base (.base (.fromHalf (16) (13)))),
  (.base (.base (.addSigned64 (37) (53) (.reg (13))))),
  (.base (.base (.loadHalf (14) (37) (0)))),
  (.base (.base (.fromHalf (17) (14)))),
  (.base (.base (.binaryFloat (48) .mul (16) (17)))),
  (.base (.base (.binaryFloat (49) .add (47) (48)))),
  (.base (.base (.loadHalf (15) (30) (14)))),
  (.base (.base (.fromHalf (18) (15)))),
  (.base (.base (.addSigned64 (38) (53) (.reg (12))))),
  (.base (.base (.loadHalf (16) (38) (0)))),
  (.base (.base (.fromHalf (19) (16)))),
  (.base (.base (.binaryFloat (50) .mul (18) (19)))),
  (.base (.base (.binaryFloat (51) .add (49) (50)))),
  (.base (.base (.loadHalf (17) (30) (16)))),
  (.base (.base (.fromHalf (20) (17)))),
  (.base (.base (.addSigned64 (39) (53) (.reg (11))))),
  (.base (.base (.loadHalf (18) (39) (0)))),
  (.base (.base (.fromHalf (21) (18)))),
  (.base (.base (.binaryFloat (52) .mul (20) (21)))),
  (.base (.base (.binaryFloat (53) .add (51) (52)))),
  (.base (.base (.loadHalf (19) (30) (18)))),
  (.base (.base (.fromHalf (22) (19)))),
  (.base (.base (.addSigned64 (40) (53) (.reg (10))))),
  (.base (.base (.loadHalf (20) (40) (0)))),
  (.base (.base (.fromHalf (23) (20)))),
  (.base (.base (.binaryFloat (54) .mul (22) (23)))),
  (.base (.base (.binaryFloat (55) .add (53) (54)))),
  (.base (.base (.loadHalf (21) (30) (20)))),
  (.base (.base (.fromHalf (24) (21)))),
  (.base (.base (.addSigned64 (41) (53) (.reg (9))))),
  (.base (.base (.loadHalf (22) (41) (0)))),
  (.base (.base (.fromHalf (25) (22)))),
  (.base (.base (.binaryFloat (56) .mul (24) (25)))),
  (.base (.base (.binaryFloat (57) .add (55) (56)))),
  (.base (.base (.loadHalf (23) (30) (22)))),
  (.base (.base (.fromHalf (26) (23)))),
  (.base (.base (.addSigned64 (42) (53) (.reg (8))))),
  (.base (.base (.loadHalf (24) (42) (0)))),
  (.base (.base (.fromHalf (27) (24)))),
  (.base (.base (.binaryFloat (58) .mul (26) (27)))),
  (.base (.base (.binaryFloat (59) .add (57) (58)))),
  (.base (.base (.loadHalf (25) (30) (24)))),
  (.base (.base (.fromHalf (28) (25)))),
  (.base (.base (.addSigned64 (43) (53) (.reg (7))))),
  (.base (.base (.loadHalf (26) (43) (0)))),
  (.base (.base (.fromHalf (29) (26)))),
  (.base (.base (.binaryFloat (60) .mul (28) (29)))),
  (.base (.base (.binaryFloat (61) .add (59) (60)))),
  (.base (.base (.loadHalf (27) (30) (26)))),
  (.base (.base (.fromHalf (30) (27)))),
  (.base (.base (.addSigned64 (44) (53) (.reg (6))))),
  (.base (.base (.loadHalf (28) (44) (0)))),
  (.base (.base (.fromHalf (31) (28)))),
  (.base (.base (.binaryFloat (62) .mul (30) (31)))),
  (.base (.base (.binaryFloat (63) .add (61) (62)))),
  (.base (.base (.loadHalf (29) (30) (28)))),
  (.base (.base (.fromHalf (32) (29)))),
  (.base (.base (.addSigned64 (45) (53) (.reg (5))))),
  (.base (.base (.loadHalf (30) (45) (0)))),
  (.base (.base (.fromHalf (33) (30)))),
  (.base (.base (.binaryFloat (64) .mul (32) (33)))),
  (.base (.base (.binaryFloat (65) .add (63) (64)))),
  (.base (.base (.loadHalf (31) (30) (30)))),
  (.base (.base (.fromHalf (34) (31)))),
  (.base (.base (.addSigned64 (46) (53) (.reg (4))))),
  (.base (.base (.loadHalf (32) (46) (0)))),
  (.base (.base (.fromHalf (35) (32)))),
  (.base (.base (.binaryFloat (66) .mul (34) (35)))),
  (.base (.base (.binaryFloat (69) .add (65) (66)))),
  (.base (.base (.addSigned64 (53) (53) (.imm (16384))))),
  (.base (.base (.addSigned64 (52) (52) (.imm (32))))),
  (.base (.base (.addSigned32 (27) (27) (.imm (16))))),
  (.base (.base (.compareNeSigned32 (1) (27) (.imm (256))))),
  (.base (.base (.branch (1) (50)))),
  (.base (.base (.toGlobal (47) (26)))),
  (.shiftLeft64 48 18 1),
  (.base (.base (.addSigned64 (49) (47) (.reg (48))))),
  (.base (.base (.loadHalf (33) (49) (0)))),
  (.base (.base (.fromHalf (67) (33)))),
  (.base (.base (.binaryFloat (68) .add (69) (67)))),
  (.base (.base (.toHalf (34) (68)))),
  (.base (.base (.mulWideSigned32 (50) (1) (2)))),
  (.base (.base (.addSigned64 (51) (3) (.reg (50))))),
  (.base (.base (.storeHalf (51) (0) (34)))),
  (.base (.base (.ret)))
]

theorem program_length : program.length = 179 := by decide
theorem program_branch : program[167]? = some (.base (.base (.branch 1 50))) := by decide
theorem program_ret : program[178]? = some (.base (.base .ret)) := by decide
theorem program_cvt : program[43]? = some (.signExtend32 18 11) := by decide
theorem program_shl : program[169]? = some (.shiftLeft64 48 18 1) := by decide

def layout : Layout :=
  ⟨[⟨.input, 64*256⟩, ⟨.input, 256*512⟩, ⟨.input, 512⟩, ⟨.output, 64*512⟩], [], []⟩
def geometry : Geometry := ⟨32768, 1, 32⟩
def start (s : State α) : Machine α := { registers := { base := s } }
def parameterA (s : State α) : Machine α := setPointer (start s) 27 ⟨0, 0, false⟩
def parameterB (s : State α) : Machine α := setPointer (parameterA s) 28 ⟨1, 0, false⟩
def parameterBias (s : State α) : Machine α := setPointer (parameterB s) 26 ⟨2, 0, false⟩
def parameters (s : State α) : Machine α := setPointer (parameterBias s) 29 ⟨3, 0, false⟩
def globalB (s : State α) : Machine α := setPointer (parameters s) 53 ⟨1, 0, true⟩
def globalA (s : State α) : Machine α := setPointer (globalB s) 52 ⟨0, 0, true⟩
def globals (s : State α) : Machine α := setPointer (globalA s) 3 ⟨3, 0, true⟩
def indexed (t : Nat) (s : State α) : Machine α := setIndex32 (globals s) 1 (t : Int)
def signed (t : Nat) (s : State α) : Machine α := setIndex32 (indexed t s) 5 0
def corrected (t : Nat) (s : State α) : Machine α := setIndex32 (signed t s) 6 0
def adjusted (t : Nat) (s : State α) : Machine α := setIndex32 (corrected t s) 7 (t : Int)
def row (t : Nat) (s : State α) : Machine α := setIndex32 (adjusted t s) 8 ((t/512 : Nat) : Int)
def rowOffset (t : Nat) (s : State α) : Machine α :=
  setIndex32 (row t s) 9 ((t/512*256 : Nat) : Int)
def masked (t : Nat) (s : State α) : Machine α :=
  setIndex32 (rowOffset t s) 10 ((t/512*512 : Nat) : Int)
def coordinates (t : Nat) (s : State α) : Machine α :=
  setIndex32 (masked t s) 11 ((t%512 : Nat) : Int)

open LarkPtxDot (blockId_step add32_step shiftLeft_step)
open LarkPtxMatrix (signed_right_step unsigned_right_step and_step sub_step bits32
  bits32_negative512 clear_low9)

theorem parameters_execute (ops : Ops α) (t : Nat) (s : State α) :
    Steps ops layout geometry t program (start s) (parameters s) :=
  .next (by rfl) (.next (by rfl) (.next (by rfl) (.next (by rfl) (.refl _))))

theorem globals_execute (ops : Ops α) (t : Nat) (s : State α) :
    Steps ops layout geometry t program (parameters s) (globals s) :=
  .next (by rfl) (.next (by rfl) (.next (by rfl) (.refl _)))

theorem index_execute (ops : Ops α) (t : Nat) (s : State α) (ht : t < 32768) :
    Steps ops layout geometry t program (globals s) (indexed t s) := by
  have hb : 0 < geometry.block ∧ t / geometry.block < 4294967296 := by
    simp only [geometry, Nat.div_one]; omega
  have e := blockId_step ops layout geometry t 1 (globals s) hb
  have e' : execute ops layout geometry t (.base (.base (.blockId 1))) (globals s) =
      some (indexed t s) := by
    simpa only [dot_step, geometry, Nat.div_one] using e
  apply one_step
  rw [transition_at ops layout geometry t program (globals s) (.base (.base (.blockId 1))) (by rfl) (by rfl)]
  exact e'

theorem sign_execute (ops : Ops α) (t : Nat) (s : State α) (ht : t < 32768) :
    Steps ops layout geometry t program (indexed t s) (signed t s) := by
  have hb : signed32 (t : Int) := by unfold signed32; omega
  have e := signed_right_step ops layout geometry t 5 1 31 (t : Int) (indexed t s) (by rfl) hb
  have hp : (2 : Int)^min 31 32 = 2147483648 := by decide
  have hz : (t : Int) / 2147483648 = 0 := by omega
  rw [hp, hz] at e
  apply one_step
  rw [transition_at ops layout geometry t program (indexed t s) (.base (.shiftRightSigned32 5 1 31))
    (by rfl) (by rfl)]
  exact e

theorem correction_execute (ops : Ops α) (t : Nat) (s : State α) :
    Steps ops layout geometry t program (signed t s) (corrected t s) :=
  .next (by rfl) (.refl _)

theorem adjust_execute (ops : Ops α) (t : Nat) (s : State α) (ht : t < 32768) :
    Steps ops layout geometry t program (corrected t s) (adjusted t s) := by
  have hb : signed32 (t : Int) ∧ signed32 0 ∧ signed32 ((t : Int)+0) := by
    unfold signed32; omega
  have e := add32_step ops layout geometry t 7 1 (.reg 6) (corrected t s) (t : Int) 0
    (by rfl) (by rfl) hb
  simp only [Int.add_zero] at e
  apply one_step
  rw [transition_at ops layout geometry t program (corrected t s) (.base (.base (.addSigned32 7 1 (.reg 6))))
    (by rfl) (by rfl), dot_step]
  exact e

theorem row_execute (ops : Ops α) (t : Nat) (s : State α) (ht : t < 32768) :
    Steps ops layout geometry t program (adjusted t s) (row t s) := by
  have hb : signed32 (t : Int) := by unfold signed32; omega
  have e := signed_right_step ops layout geometry t 8 7 9 (t : Int) (adjusted t s) (by rfl) hb
  have hp : (2 : Int)^min 9 32 = 512 := by decide
  have he : (t : Int)/512 = ((t/512 : Nat) : Int) := by omega
  rw [hp, he] at e
  apply one_step
  rw [transition_at ops layout geometry t program (adjusted t s) (.base (.shiftRightSigned32 8 7 9))
    (by rfl) (by rfl)]
  exact e

theorem row_offset_execute (ops : Ops α) (t : Nat) (s : State α) (ht : t < 32768) :
    Steps ops layout geometry t program (row t s) (rowOffset t s) := by
  have hr : t/512 < 64 := by omega
  have hb : unsigned32 ((t/512 : Nat) : Int) := by unfold unsigned32; omega
  have e := shiftLeft_step ops layout geometry t 9 8 8 (row t s) ((t/512 : Nat) : Int) (by rfl) hb
  have hp : (2 : Int)^min 8 32 = 256 := by decide
  have he : (((t/512 : Nat) : Int)*256) % 4294967296 = ((t/512*256 : Nat) : Int) := by
    simp only [Int.natCast_mul]; omega
  rw [hp, he] at e
  apply one_step
  rw [transition_at ops layout geometry t program (row t s) (.base (.base (.shiftLeft32 9 8 8)))
    (by rfl) (by rfl), dot_step]
  exact e

theorem mask_execute (ops : Ops α) (t : Nat) (s : State α) (ht : t < 32768) :
    Steps ops layout geometry t program (rowOffset t s) (masked t s) := by
  have hb : unsigned32 (t : Int) ∧ signed32 (-512) := by unfold unsigned32 signed32; omega
  have e := and_step ops layout geometry t 10 7 (.imm (-512)) (t : Int) (-512) (rowOffset t s)
    (by rfl) (by rfl) hb
  have htbits : bits32 (t : Int) = t := by
    unfold bits32
    have he : (t : Int) % 4294967296 = (t : Int) := by omega
    rw [he]; simp
  rw [htbits, bits32_negative512, clear_low9 t (by omega)] at e
  apply one_step
  rw [transition_at ops layout geometry t program (rowOffset t s) (.base (.andBits32 10 7 (.imm (-512))))
    (by rfl) (by rfl)]
  exact e

theorem column_execute (ops : Ops α) (t : Nat) (s : State α) (ht : t < 32768) :
    Steps ops layout geometry t program (masked t s) (coordinates t s) := by
  have hr : t/512 < 64 := by omega
  have hb : signed32 (t : Int) ∧ signed32 ((t/512*512 : Nat) : Int) ∧
      signed32 ((t : Int)-((t/512*512 : Nat) : Int)) := by
    unfold signed32; simp only [Int.natCast_mul]; omega
  have e := sub_step ops layout geometry t 11 1 (.reg 10) (t : Int) ((t/512*512 : Nat) : Int)
    (masked t s) (by rfl) (by rfl) hb
  have he : (t : Int)-((t/512*512 : Nat) : Int) = ((t%512 : Nat) : Int) := by
    simp only [Int.natCast_mul]; omega
  rw [he] at e
  apply one_step
  rw [transition_at ops layout geometry t program (masked t s) (.base (.subSigned32 11 1 (.reg 10)))
    (by rfl) (by rfl)]
  exact e

theorem coordinates_execute (ops : Ops α) (t : Nat) (s : State α) (ht : t < 32768) :
    Steps ops layout geometry t program (start s) (coordinates t s) := by
  apply steps_trans _ _ _ _ _ _ _ _ (parameters_execute ops t s)
  apply steps_trans _ _ _ _ _ _ _ _ (globals_execute ops t s)
  apply steps_trans _ _ _ _ _ _ _ _ (index_execute ops t s ht)
  apply steps_trans _ _ _ _ _ _ _ _ (sign_execute ops t s ht)
  apply steps_trans _ _ _ _ _ _ _ _ (correction_execute ops t s)
  apply steps_trans _ _ _ _ _ _ _ _ (adjust_execute ops t s ht)
  apply steps_trans _ _ _ _ _ _ _ _ (row_execute ops t s ht)
  apply steps_trans _ _ _ _ _ _ _ _ (row_offset_execute ops t s ht)
  exact steps_trans _ _ _ _ _ _ _ _ (mask_execute ops t s ht) (column_execute ops t s ht)

theorem coordinates_pc (t : Nat) (s : State α) : (coordinates t s).pc = 15 := rfl
theorem coordinates_base (t : Nat) (s : State α) : (coordinates t s).registers.base = s := rfl

end Linear
end LarkPtxLinear

#print axioms LarkPtxLinear.steps_trans
#print axioms LarkPtxLinear.one_step
#print axioms LarkPtxLinear.transition_at
#print axioms LarkPtxLinear.base_step
#print axioms LarkPtxLinear.dot_step
#print axioms LarkPtxLinear.signExtend32_step
#print axioms LarkPtxLinear.signExtend32_result_signed64
#print axioms LarkPtxLinear.signedBits64_range
#print axioms LarkPtxLinear.shiftLeft64_step
#print axioms LarkPtxLinear.shiftLeft64_result_signed64
#print axioms LarkPtxLinear.column_shift_value
#print axioms LarkPtxLinear.shift_negative_one
#print axioms LarkPtxLinear.shift_sign_bit
#print axioms LarkPtxLinear.shift_width
#print axioms LarkPtxLinear.shift_clamped
#print axioms LarkPtxLinear.Linear.program_length
#print axioms LarkPtxLinear.Linear.program_branch
#print axioms LarkPtxLinear.Linear.program_ret
#print axioms LarkPtxLinear.Linear.program_cvt
#print axioms LarkPtxLinear.Linear.program_shl
#print axioms LarkPtxLinear.Linear.coordinates_execute
#print axioms LarkPtxLinear.Linear.coordinates_pc
#print axioms LarkPtxLinear.Linear.coordinates_base
