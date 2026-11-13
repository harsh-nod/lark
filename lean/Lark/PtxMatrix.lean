import Lark.PtxDot
import Init.Data.Nat.Bitwise.Lemmas

/-!
Additional guarded PTX integer operations required by the unchanged compiled
64x256 times 256x512 FP16 GEMM development program. Existing GEMV and ReLU
models remain unchanged. These definitions alone establish no matrix-kernel
correctness theorem, compiler conformance or IEEE result.
-/
namespace LarkPtxMatrix
open LarkNonlinear LarkPtxPointwise LarkPtxDot
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

inductive Instruction where
  | base : LarkPtxDot.Instruction → Instruction
  | shiftRightSigned32 : Nat → Nat → Nat → Instruction
  | shiftRightUnsigned32 : Nat → Nat → Nat → Instruction
  | andBits32 : Nat → Nat → Operand → Instruction
  | subSigned32 : Nat → Nat → Operand → Instruction
  | mulWideUnsigned32 : Nat → Nat → Int → Instruction
  deriving DecidableEq, Repr

def bits32 (x : Int) : Nat := (x % 4294967296).toNat

def execute (ops : Ops α) (layout : Layout) (g : Geometry) (t : Nat)
    (instruction : Instruction) (s : Machine α) : Option (Machine α) := do
  match instruction with
  | .base instruction => LarkPtxDot.execute ops layout g t instruction s
  | .shiftRightSigned32 d a count =>
      let x ← s.registers.i32 a
      if signed32 x then
        some (setIndex32 s d (x / (2 : Int) ^ min count 32))
      else none
  | .shiftRightUnsigned32 d a count =>
      let x ← s.registers.i32 a
      if unsigned32 x then
        some (setIndex32 s d (x / (2 : Int) ^ min count 32))
      else none
  | .andBits32 d a b =>
      let x ← s.registers.i32 a
      let y ← operand32 s.registers b
      if unsigned32 x ∧ signed32 y then
        some (setIndex32 s d ((bits32 x &&& bits32 y : Nat) : Int))
      else none
  | .subSigned32 d a b =>
      let x ← s.registers.i32 a
      let y ← operand32 s.registers b
      if signed32 x ∧ signed32 y ∧ signed32 (x-y) then
        some (setIndex32 s d (x-y))
      else none
  | .mulWideUnsigned32 d a c =>
      let x ← s.registers.i32 a
      if unsigned32 x ∧ unsigned32 c ∧ signed64 (x*c) then
        some (advance s (putI64 s.registers d (x*c)))
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
    (instruction : LarkPtxDot.Instruction) (s : Machine α) :
    execute ops layout g t (.base instruction) s =
      LarkPtxDot.execute ops layout g t instruction s := rfl

theorem signed_right_step (ops : Ops α) (layout : Layout) (g : Geometry)
    (t d a count : Nat) (x : Int) (s : Machine α)
    (hx : s.registers.i32 a = some x) (hb : signed32 x) :
    execute ops layout g t (.shiftRightSigned32 d a count) s =
      some (setIndex32 s d (x / (2 : Int) ^ min count 32)) := by
  simp [execute, hx, hb]

theorem unsigned_right_step (ops : Ops α) (layout : Layout) (g : Geometry)
    (t d a count : Nat) (x : Int) (s : Machine α)
    (hx : s.registers.i32 a = some x) (hb : unsigned32 x) :
    execute ops layout g t (.shiftRightUnsigned32 d a count) s =
      some (setIndex32 s d (x / (2 : Int) ^ min count 32)) := by
  simp [execute, hx, hb]

theorem and_step (ops : Ops α) (layout : Layout) (g : Geometry)
    (t d a : Nat) (b : Operand) (x y : Int) (s : Machine α)
    (hx : s.registers.i32 a = some x) (hy : operand32 s.registers b = some y)
    (hb : unsigned32 x ∧ signed32 y) :
    execute ops layout g t (.andBits32 d a b) s =
      some (setIndex32 s d ((bits32 x &&& bits32 y : Nat) : Int)) := by
  simp [execute, hx, hy, hb]

theorem sub_step (ops : Ops α) (layout : Layout) (g : Geometry)
    (t d a : Nat) (b : Operand) (x y : Int) (s : Machine α)
    (hx : s.registers.i32 a = some x) (hy : operand32 s.registers b = some y)
    (hb : signed32 x ∧ signed32 y ∧ signed32 (x-y)) :
    execute ops layout g t (.subSigned32 d a b) s = some (setIndex32 s d (x-y)) := by
  simp [execute, hx, hy, hb]

theorem unsigned_wide_step (ops : Ops α) (layout : Layout) (g : Geometry)
    (t d a : Nat) (c x : Int) (s : Machine α)
    (hx : s.registers.i32 a = some x)
    (hb : unsigned32 x ∧ unsigned32 c ∧ signed64 (x*c)) :
    execute ops layout g t (.mulWideUnsigned32 d a c) s =
      some (advance s (putI64 s.registers d (x*c))) := by
  simp [execute, hx, hb]

theorem zero_float_step (ops : Ops α) (layout : Layout) (g : Geometry)
    (t d : Nat) (s : Machine α) :
    LarkPtxDot.execute ops layout g t (.literalFloat d 0 1) s =
      some (setFloat s d (ops.literal 0 1)) := by
  simp [LarkPtxDot.execute, setFloat]

theorem zero_index_step (ops : Ops α) (layout : Layout) (g : Geometry)
    (t d : Nat) (s : Machine α) :
    LarkPtxDot.execute ops layout g t (.literal32 d 0) s = some (setIndex32 s d 0) := by
  simp [LarkPtxDot.execute, unsigned32, setIndex32]

def setIndex64 (s : Machine α) (d : Nat) (v : Int) : Machine α :=
  advance s (putI64 s.registers d v)

@[simp] theorem setIndex64_i32 (s : Machine α) (d r : Nat) (v : Int) :
    (setIndex64 s d v).registers.i32 r = s.registers.i32 r := rfl

@[simp] theorem setIndex64_pc (s : Machine α) (d : Nat) (v : Int) :
    (setIndex64 s d v).pc = s.pc+1 := rfl
@[simp] theorem setIndex64_stopped (s : Machine α) (d : Nat) (v : Int) :
    (setIndex64 s d v).registers.stopped = s.registers.stopped := rfl
@[simp] theorem setIndex32_stopped (s : Machine α) (d : Nat) (v : Int) :
    (setIndex32 s d v).registers.stopped = s.registers.stopped := rfl
@[simp] theorem setIndex64_base (s : Machine α) (d : Nat) (v : Int) :
    (setIndex64 s d v).registers.base = s.registers.base := rfl
@[simp] theorem setIndex32_base (s : Machine α) (d : Nat) (v : Int) :
    (setIndex32 s d v).registers.base = s.registers.base := rfl
@[simp] theorem setFloat_base (s : Machine α) (d : Nat) (v : α) :
    (setFloat s d v).registers.base = s.registers.base := rfl
@[simp] theorem setPointer_base (s : Machine α) (d : Nat) (p : Pointer) :
    (setPointer s d p).registers.base = s.registers.base := rfl
@[simp] theorem setPointer_stopped (s : Machine α) (d : Nat) (p : Pointer) :
    (setPointer s d p).registers.stopped = s.registers.stopped := rfl
@[simp] theorem setPointer_scalar (s : Machine α) (d r : Nat) (p : Pointer) :
    (setPointer s d p).registers.scalar r = s.registers.scalar r := rfl
@[simp] theorem setPointer_half (s : Machine α) (d r : Nat) (p : Pointer) :
    (setPointer s d p).registers.half r = s.registers.half r := rfl
@[simp] theorem setFloat_i64 (s : Machine α) (d r : Nat) (v : α) :
    (setFloat s d v).registers.i64 r = s.registers.i64 r := rfl
@[simp] theorem loadedHalf_i64 (s : Machine α) (t d r : Nat) (l : Location) (v : α) :
    (loadedHalf s t d l v).registers.i64 r = s.registers.i64 r := rfl
@[simp] theorem setFloat_i32 (s : Machine α) (d r : Nat) (v : α) :
    (setFloat s d v).registers.i32 r = s.registers.i32 r := rfl
@[simp] theorem loadedHalf_i32 (s : Machine α) (t d r : Nat) (l : Location) (v : α) :
    (loadedHalf s t d l v).registers.i32 r = s.registers.i32 r := rfl
@[simp] theorem setPointer_i32 (s : Machine α) (d r : Nat) (p : Pointer) :
    (setPointer s d p).registers.i32 r = s.registers.i32 r := rfl
@[simp] theorem setPointer_i64 (s : Machine α) (d r : Nat) (p : Pointer) :
    (setPointer s d p).registers.i64 r = if r = d then none else s.registers.i64 r := by
  by_cases h : r = d <;> simp [setPointer, LarkPtxDot.advance, putPointer, putValue, Registers.i64, h]
@[simp] theorem setIndex32_i64 (s : Machine α) (d r : Nat) (v : Int) :
    (setIndex32 s d v).registers.i64 r = s.registers.i64 r := rfl
@[simp] theorem setIndex64_i64 (s : Machine α) (d r : Nat) (v : Int) :
    (setIndex64 s d v).registers.i64 r = if r = d then some v else s.registers.i64 r := by
  by_cases h : r = d <;> simp [setIndex64, LarkPtxDot.advance, putI64, putValue, Registers.i64, h]
@[simp] theorem setIndex64_pointer (s : Machine α) (d r : Nat) (v : Int) :
    (setIndex64 s d v).registers.pointer r = if r = d then none else s.registers.pointer r := by
  by_cases h : r = d <;> simp [setIndex64, LarkPtxDot.advance, putI64, putValue, Registers.pointer, h]
@[simp] theorem setIndex32_pointer (s : Machine α) (d r : Nat) (v : Int) :
    (setIndex32 s d v).registers.pointer r = s.registers.pointer r := rfl
@[simp] theorem setIndex32_scalar (s : Machine α) (d r : Nat) (v : Int) :
    (setIndex32 s d v).registers.scalar r = s.registers.scalar r := rfl
@[simp] theorem setPredicate_registers (s : Machine α) (d : Nat) (v : Bool) :
    (setPredicate s d v).registers = s.registers := rfl

theorem bits32_negative512 : bits32 (-512) = 4294966784 := by decide

theorem clear_low9 (n : Nat) (hn : n < 4294967296) :
    n &&& 4294966784 = (n / 512) * 512 := by
  have hd : (n &&& 4294966784) / 512 = n / 512 := by
    have hdiv : n / 512 < 8388608 := by omega
    change (n &&& 4294966784) / 2^9 = n / 512
    rw [Nat.and_div_two_pow]
    change n / 512 &&& (2^23-1) = n / 512
    exact Nat.and_two_pow_sub_one_of_lt_two_pow hdiv
  have hm : (n &&& 4294966784) % 512 = 0 := by
    change (n &&& 4294966784) % 2^9 = 0
    rw [Nat.and_mod_two_pow]
    change n % 512 &&& 0 = 0
    simp
  have hs := Nat.mod_add_div (n &&& 4294966784) 512
  rw [hm, hd] at hs
  omega

namespace Gemm

def prologue : List Instruction :=
  [.base (.parameter 25 0), .base (.parameter 26 1), .base (.parameter 24 2),
   .base (.toGlobal 48 26), .base (.toGlobal 47 25), .base (.blockId 1),
   .shiftRightSigned32 5 1 31, .shiftRightUnsigned32 6 5 23,
   .base (.addSigned32 7 1 (.reg 6)), .shiftRightSigned32 8 7 9,
   .base (.shiftLeft32 9 8 8), .andBits32 10 7 (.imm (-512)),
   .subSigned32 11 1 (.reg 10)] ++
  (List.range 14).flatMap (fun j =>
    [.base (.addSigned32 (12+j) 11 (.imm (((15-j)*512 : Nat) : Int))),
     .mulWideUnsigned32 (3+j) (12+j) 2]) ++
  [.base (.mulWideSigned32 17 11 2), .base (.addSigned32 26 11 (.imm 512)),
   .mulWideUnsigned32 18 26 2, .base (.mulWideSigned32 19 9 2),
   .base (.literalFloat 68 0 1), .base (.literal32 27 0)]

def laterTerm (j : Nat) : List Instruction :=
  [.base (.loadHalf (2*j+1) 27 ((2*j : Nat) : Int)),
   .base (.fromHalf (4+2*j) (2*j+1)),
   .base (.addSigned64 (28+j) 48 (.reg (if j = 1 then 18 else 18-j))),
   .base (.loadHalf (2*j+2) (28+j) 0),
   .base (.fromHalf (5+2*j) (2*j+2)),
   .base (.binaryFloat (36+2*j) .mul (4+2*j) (5+2*j)),
   .base (.binaryFloat (if j = 15 then 68 else 37+2*j) .add (35+2*j) (36+2*j))]

def body : List Instruction :=
  [.base (.addSigned64 27 47 (.reg 19)), .base (.loadHalf 1 27 0),
   .base (.fromHalf 4 1), .base (.addSigned64 28 48 (.reg 17)),
   .base (.loadHalf 2 28 0), .base (.fromHalf 5 2),
   .base (.binaryFloat 36 .mul 4 5), .base (.binaryFloat 37 .add 68 36)] ++
  (List.range 15).flatMap (fun j => laterTerm (j+1))

def control : List Instruction :=
  [.base (.addSigned64 48 48 (.imm 16384)), .base (.addSigned64 47 47 (.imm 32)),
   .base (.addSigned32 27 27 (.imm 16)), .base (.compareNeSigned32 1 27 (.imm 256)),
   .base (.branch 1 47)]

def epilogue : List Instruction :=
  [.base (.toGlobal 44 24), .base (.toHalf 33 68),
   .base (.mulWideSigned32 45 1 2), .base (.addSigned64 46 44 (.reg 45)),
   .base (.storeHalf 46 0 33), .base .ret]

def program : List Instruction := prologue ++ body ++ control ++ epilogue

def layout : Layout :=
  ⟨[⟨.input, 64*256⟩, ⟨.input, 256*512⟩, ⟨.output, 64*512⟩], [], []⟩

def geometry : Geometry := ⟨32768, 1, 32⟩

def start (s : State α) : Machine α := { registers := { base := s } }
def parameterA (s : State α) : Machine α := setPointer (start s) 25 ⟨0, 0, false⟩
def parameterB (s : State α) : Machine α := setPointer (parameterA s) 26 ⟨1, 0, false⟩
def parameters (s : State α) : Machine α := setPointer (parameterB s) 24 ⟨2, 0, false⟩
def globalB (s : State α) : Machine α := setPointer (parameters s) 48 ⟨1, 0, true⟩
def globals (s : State α) : Machine α := setPointer (globalB s) 47 ⟨0, 0, true⟩
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

theorem parameters_execute (ops : Ops α) (t : Nat) (s : State α) :
    Steps ops layout geometry t program (start s) (parameters s) :=
  .next (by rfl) (.next (by rfl) (.next (by rfl) (.refl _)))

theorem globals_execute (ops : Ops α) (t : Nat) (s : State α) :
    Steps ops layout geometry t program (parameters s) (globals s) :=
  .next (by rfl) (.next (by rfl) (.refl _))

theorem index_execute (ops : Ops α) (t : Nat) (s : State α) (ht : t < 32768) :
    Steps ops layout geometry t program (globals s) (indexed t s) := by
  have hb : 0 < geometry.block ∧ t / geometry.block < 4294967296 := by
    simp only [geometry, Nat.div_one]; omega
  have e := blockId_step ops layout geometry t 1 (globals s) hb
  have e' : execute ops layout geometry t (.base (.blockId 1)) (globals s) =
      some (indexed t s) := by
    simpa only [base_step, geometry, Nat.div_one] using e
  apply one_step
  rw [transition_at ops layout geometry t program (globals s) (.base (.blockId 1)) (by rfl) (by rfl)]
  exact e'

theorem sign_execute (ops : Ops α) (t : Nat) (s : State α) (ht : t < 32768) :
    Steps ops layout geometry t program (indexed t s) (signed t s) := by
  have hb : signed32 (t : Int) := by unfold signed32; omega
  have e := signed_right_step ops layout geometry t 5 1 31 (t : Int) (indexed t s) (by rfl) hb
  have hp : (2 : Int)^min 31 32 = 2147483648 := by decide
  have hz : (t : Int) / 2147483648 = 0 := by omega
  rw [hp, hz] at e
  apply one_step
  rw [transition_at ops layout geometry t program (indexed t s) (.shiftRightSigned32 5 1 31)
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
  rw [transition_at ops layout geometry t program (corrected t s) (.base (.addSigned32 7 1 (.reg 6)))
    (by rfl) (by rfl), base_step]
  exact e

theorem row_execute (ops : Ops α) (t : Nat) (s : State α) (ht : t < 32768) :
    Steps ops layout geometry t program (adjusted t s) (row t s) := by
  have hb : signed32 (t : Int) := by unfold signed32; omega
  have e := signed_right_step ops layout geometry t 8 7 9 (t : Int) (adjusted t s) (by rfl) hb
  have hp : (2 : Int)^min 9 32 = 512 := by decide
  have he : (t : Int)/512 = ((t/512 : Nat) : Int) := by omega
  rw [hp, he] at e
  apply one_step
  rw [transition_at ops layout geometry t program (adjusted t s) (.shiftRightSigned32 8 7 9)
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
  rw [transition_at ops layout geometry t program (row t s) (.base (.shiftLeft32 9 8 8))
    (by rfl) (by rfl), base_step]
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
  rw [transition_at ops layout geometry t program (rowOffset t s) (.andBits32 10 7 (.imm (-512)))
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
  rw [transition_at ops layout geometry t program (masked t s) (.subSigned32 11 1 (.reg 10))
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

def addressPair (j t : Nat) (s : Machine α) : Machine α :=
  setIndex64 (setIndex32 s (12+j) ((t%512+(15-j)*512 : Nat) : Int))
    (3+j) (((t%512+(15-j)*512)*2 : Nat) : Int)

theorem program_pair : ∀ (j : Fin 14),
    program[13+2*j.val]? = some (.base (.addSigned32 (12+j.val) 11
      (.imm (((15-j.val)*512 : Nat) : Int)))) ∧
    program[14+2*j.val]? = some (.mulWideUnsigned32 (3+j.val) (12+j.val) 2) := by decide

theorem address_pair_execute (ops : Ops α) (t j : Nat) (s : Machine α)
    (hj : j < 14) (hpc : s.pc = 13+2*j) (hs : s.registers.stopped = false)
    (hc : s.registers.i32 11 = some ((t%512 : Nat) : Int)) :
    Steps ops layout geometry t program s (addressPair j t s) := by
  have hcol : t%512 < 512 := Nat.mod_lt _ (by decide)
  have hoff : (15-j)*512 ≤ 7680 := by omega
  have hb : signed32 ((t%512 : Nat) : Int) ∧ signed32 (((15-j)*512 : Nat) : Int) ∧
      signed32 (((t%512 : Nat) : Int)+(((15-j)*512 : Nat) : Int)) := by
    unfold signed32; omega
  have e1 := add32_step ops layout geometry t (12+j) 11 (.imm (((15-j)*512 : Nat) : Int))
    s ((t%512 : Nat) : Int) (((15-j)*512 : Nat) : Int) hc (by rfl) hb
  have e1' : LarkPtxDot.execute ops layout geometry t
      (.addSigned32 (12+j) 11 (.imm (((15-j)*512 : Nat) : Int))) s =
      some (setIndex32 s (12+j) ((t%512+(15-j)*512 : Nat) : Int)) := by
    simpa only [Int.natCast_add] using e1
  have h1 : Steps ops layout geometry t program s
      (setIndex32 s (12+j) ((t%512+(15-j)*512 : Nat) : Int)) := by
    apply one_step
    rw [transition_at ops layout geometry t program s
      (.base (.addSigned32 (12+j) 11 (.imm (((15-j)*512 : Nat) : Int)))) hs
      (by rw [hpc]; exact (program_pair ⟨j, hj⟩).1), base_step]
    exact e1'
  have hw : unsigned32 ((t%512+(15-j)*512 : Nat) : Int) ∧ unsigned32 2 ∧
      signed64 (((t%512+(15-j)*512 : Nat) : Int)*2) := by
    unfold unsigned32 signed64; simp only [Int.natCast_add]; omega
  have e2 := unsigned_wide_step ops layout geometry t (3+j) (12+j) 2
    ((t%512+(15-j)*512 : Nat) : Int)
    (setIndex32 s (12+j) ((t%512+(15-j)*512 : Nat) : Int)) (by simp) hw
  have e2' : execute ops layout geometry t (.mulWideUnsigned32 (3+j) (12+j) 2)
      (setIndex32 s (12+j) ((t%512+(15-j)*512 : Nat) : Int)) =
      some (addressPair j t s) := by
    simpa only [addressPair, setIndex64, Int.natCast_mul] using e2
  apply steps_trans _ _ _ _ _ _ _ _ h1
  apply one_step
  rw [transition_at ops layout geometry t program
    (setIndex32 s (12+j) ((t%512+(15-j)*512 : Nat) : Int))
    (.mulWideUnsigned32 (3+j) (12+j) 2)
    (by change s.registers.stopped = false; exact hs)]
  · exact e2'
  · change program[s.pc+1]? = _
    rw [hpc]
    have he : 13+2*j+1 = 14+2*j := by omega
    rw [he]
    exact (program_pair ⟨j, hj⟩).2

def addressPairs (t : Nat) (s : State α) : Nat → Machine α
  | 0 => coordinates t s
  | j+1 => addressPair j t (addressPairs t s j)

theorem addressPairs_pc (t j : Nat) (s : State α) :
    (addressPairs t s j).pc = 13+2*j := by
  induction j with
  | zero => rfl
  | succ j ih =>
      change ((addressPairs t s j).pc+1)+1 = 13+2*(j+1)
      omega

theorem addressPairs_stopped (t j : Nat) (s : State α) :
    (addressPairs t s j).registers.stopped = false := by
  induction j with
  | zero => rfl
  | succ j ih =>
      change (addressPairs t s j).registers.stopped = false
      exact ih

theorem addressPairs_column (t j : Nat) (s : State α) :
    (addressPairs t s j).registers.i32 11 = some ((t%512 : Nat) : Int) := by
  induction j with
  | zero => rfl
  | succ j ih =>
      simp only [addressPairs, addressPair, setIndex64_i32, setIndex32_i32]
      rw [if_neg (by omega)]
      exact ih

theorem addressPairs_execute (ops : Ops α) (t j : Nat) (s : State α)
    (ht : t < 32768) (hj : j ≤ 14) :
    Steps ops layout geometry t program (start s) (addressPairs t s j) := by
  induction j with
  | zero => exact coordinates_execute ops t s ht
  | succ j ih =>
      have hp := ih (by omega)
      have hn := address_pair_execute ops t j (addressPairs t s j) (by omega)
        (addressPairs_pc t j s) (addressPairs_stopped t j s) (addressPairs_column t j s)
      exact steps_trans _ _ _ _ _ _ _ _ hp hn

theorem addressPairs_row_offset (t j : Nat) (s : State α) :
    (addressPairs t s j).registers.i32 9 = some ((t/512*256 : Nat) : Int) := by
  induction j with
  | zero => rfl
  | succ j ih =>
      simp only [addressPairs, addressPair, setIndex64_i32, setIndex32_i32]
      rw [if_neg (by omega)]
      exact ih

theorem addressPairs_base (t j : Nat) (s : State α) :
    (addressPairs t s j).registers.base = s := by
  induction j with
  | zero =>
      simp only [addressPairs, coordinates, masked, rowOffset, row, adjusted, corrected,
        signed, indexed, globals, globalB, parameters, parameterB, parameterA, start,
        setIndex32_base, setPointer_base]
  | succ j ih =>
      simpa only [addressPairs, addressPair, setIndex64_base, setIndex32_base] using ih

def columnWide (t : Nat) (s : Machine α) : Machine α :=
  setIndex64 s 17 ((t%512*2 : Nat) : Int)
def nextColumn (t : Nat) (s : Machine α) : Machine α :=
  setIndex32 (columnWide t s) 26 ((t%512+512 : Nat) : Int)
def nextWide (t : Nat) (s : Machine α) : Machine α :=
  setIndex64 (nextColumn t s) 18 (((t%512+512)*2 : Nat) : Int)
def matrixWide (t : Nat) (s : Machine α) : Machine α :=
  setIndex64 (nextWide t s) 19 (((t/512*256)*2 : Nat) : Int)
def zeroAccumulator (ops : Ops α) (t : Nat) (s : Machine α) : Machine α :=
  setFloat (matrixWide t s) 68 (ops.literal 0 1)
def initializedSuffix (ops : Ops α) (t : Nat) (s : Machine α) : Machine α :=
  setIndex32 (zeroAccumulator ops t s) 27 0

theorem column_wide_execute (ops : Ops α) (t : Nat) (s : Machine α)
    (hpc : s.pc = 41) (hs : s.registers.stopped = false)
    (hcol : s.registers.i32 11 = some ((t%512 : Nat) : Int)) :
    Steps ops layout geometry t program s (columnWide t s) := by
  have hc : t%512 < 512 := Nat.mod_lt _ (by decide)
  have hb : signed32 ((t%512 : Nat) : Int) ∧ signed32 2 ∧
      signed64 (((t%512 : Nat) : Int)*2) := by unfold signed32 signed64; omega
  have e := wide_step ops layout geometry t 17 11 2 ((t%512 : Nat) : Int) s hcol hb
  have e' : LarkPtxDot.execute ops layout geometry t (.mulWideSigned32 17 11 2) s =
      some (columnWide t s) := by
    simpa only [columnWide, setIndex64, Int.natCast_mul] using e
  apply one_step
  rw [transition_at ops layout geometry t program s (.base (.mulWideSigned32 17 11 2))
    hs (by rw [hpc]; rfl), base_step]
  exact e'

#print axioms LarkPtxMatrix.Gemm.column_wide_execute

theorem next_column_execute (ops : Ops α) (t : Nat) (s : Machine α)
    (hpc : s.pc = 41) (hs : s.registers.stopped = false)
    (hcol : s.registers.i32 11 = some ((t%512 : Nat) : Int)) :
    Steps ops layout geometry t program (columnWide t s) (nextColumn t s) := by
  have hc : t%512 < 512 := Nat.mod_lt _ (by decide)
  have hb : signed32 ((t%512 : Nat) : Int) ∧ signed32 512 ∧
      signed32 (((t%512 : Nat) : Int)+512) := by unfold signed32; omega
  have hx : (columnWide t s).registers.i32 11 = some ((t%512 : Nat) : Int) := by
    simpa only [columnWide, setIndex64_i32] using hcol
  have e := add32_step ops layout geometry t 26 11 (.imm 512) (columnWide t s)
    ((t%512 : Nat) : Int) 512 hx (by rfl) hb
  have e' : LarkPtxDot.execute ops layout geometry t (.addSigned32 26 11 (.imm 512))
      (columnWide t s) = some (nextColumn t s) := by
    simpa only [nextColumn, Int.natCast_add] using e
  have hp : (columnWide t s).pc = 42 := by
    simp only [columnWide, setIndex64_pc, hpc]
  apply one_step
  rw [transition_at ops layout geometry t program (columnWide t s)
    (.base (.addSigned32 26 11 (.imm 512)))
    (by simpa only [columnWide, setIndex64_stopped] using hs) (by rw [hp]; rfl), base_step]
  exact e'

#print axioms LarkPtxMatrix.Gemm.next_column_execute

theorem next_wide_execute (ops : Ops α) (t : Nat) (s : Machine α)
    (hpc : s.pc = 41) (hs : s.registers.stopped = false) :
    Steps ops layout geometry t program (nextColumn t s) (nextWide t s) := by
  have hc : t%512 < 512 := Nat.mod_lt _ (by decide)
  have hb : unsigned32 ((t%512+512 : Nat) : Int) ∧ unsigned32 2 ∧
      signed64 (((t%512+512 : Nat) : Int)*2) := by
    unfold unsigned32 signed64; simp only [Int.natCast_add]; omega
  have e := unsigned_wide_step ops layout geometry t 18 26 2 ((t%512+512 : Nat) : Int)
    (nextColumn t s) (by simp [nextColumn]) hb
  have e' : execute ops layout geometry t (.mulWideUnsigned32 18 26 2) (nextColumn t s) =
      some (nextWide t s) := by
    simpa only [nextWide, setIndex64, Int.natCast_mul] using e
  have hp : (nextColumn t s).pc = 43 := by
    simp only [nextColumn, columnWide, setIndex32_pc, setIndex64_pc, hpc]
  apply one_step
  rw [transition_at ops layout geometry t program (nextColumn t s) (.mulWideUnsigned32 18 26 2)
    (by simpa only [nextColumn, columnWide, setIndex32_stopped, setIndex64_stopped] using hs)
    (by rw [hp]; rfl)]
  exact e'

#print axioms LarkPtxMatrix.Gemm.next_wide_execute

theorem matrix_wide_execute (ops : Ops α) (t : Nat) (s : Machine α)
    (ht : t < 32768) (hpc : s.pc = 41) (hs : s.registers.stopped = false)
    (hrow : s.registers.i32 9 = some ((t/512*256 : Nat) : Int)) :
    Steps ops layout geometry t program (nextWide t s) (matrixWide t s) := by
  have hr : t/512 < 64 := by omega
  have hb : signed32 ((t/512*256 : Nat) : Int) ∧ signed32 2 ∧
      signed64 (((t/512*256 : Nat) : Int)*2) := by
    unfold signed32 signed64; simp only [Int.natCast_mul]; omega
  have hx : (nextWide t s).registers.i32 9 = some ((t/512*256 : Nat) : Int) := by
    simpa only [nextWide, nextColumn, columnWide, setIndex64_i32, setIndex32_i32] using hrow
  have e := wide_step ops layout geometry t 19 9 2 ((t/512*256 : Nat) : Int) (nextWide t s) hx hb
  have e' : LarkPtxDot.execute ops layout geometry t (.mulWideSigned32 19 9 2) (nextWide t s) =
      some (matrixWide t s) := by
    simpa only [matrixWide, setIndex64, Int.natCast_mul] using e
  have hp : (nextWide t s).pc = 44 := by
    simp only [nextWide, nextColumn, columnWide, setIndex32_pc, setIndex64_pc, hpc]
  apply one_step
  rw [transition_at ops layout geometry t program (nextWide t s) (.base (.mulWideSigned32 19 9 2))
    (by simpa only [nextWide, nextColumn, columnWide, setIndex32_stopped, setIndex64_stopped] using hs)
    (by rw [hp]; rfl), base_step]
  exact e'

#print axioms LarkPtxMatrix.Gemm.matrix_wide_execute

theorem zero_execute (ops : Ops α) (t : Nat) (s : Machine α)
    (hpc : s.pc = 41) (hs : s.registers.stopped = false) :
    Steps ops layout geometry t program (matrixWide t s) (zeroAccumulator ops t s) := by
  have hp : (matrixWide t s).pc = 45 := by
    simp only [matrixWide, nextWide, nextColumn, columnWide, setIndex32_pc, setIndex64_pc, hpc]
  have hstop : (matrixWide t s).registers.stopped = false := by
    simpa only [matrixWide, nextWide, nextColumn, columnWide, setIndex32_stopped, setIndex64_stopped] using hs
  apply one_step
  rw [transition_at ops layout geometry t program (matrixWide t s) (.base (.literalFloat 68 0 1))
    hstop (by rw [hp]; rfl), base_step]
  exact zero_float_step ops layout geometry t 68 (matrixWide t s)

#print axioms LarkPtxMatrix.Gemm.zero_execute

theorem initialize_execute (ops : Ops α) (t : Nat) (s : Machine α)
    (hpc : s.pc = 41) (hs : s.registers.stopped = false) :
    Steps ops layout geometry t program (zeroAccumulator ops t s) (initializedSuffix ops t s) := by
  have hp : (zeroAccumulator ops t s).pc = 46 := by
    simp only [zeroAccumulator, matrixWide, nextWide, nextColumn, columnWide,
      setFloat_pc, setIndex32_pc, setIndex64_pc, hpc]
  have hstop : (zeroAccumulator ops t s).registers.stopped = false := by
    simpa only [zeroAccumulator, matrixWide, nextWide, nextColumn, columnWide,
      setFloat_stopped, setIndex32_stopped, setIndex64_stopped] using hs
  apply one_step
  rw [transition_at ops layout geometry t program (zeroAccumulator ops t s) (.base (.literal32 27 0))
    hstop (by rw [hp]; rfl), base_step]
  exact zero_index_step ops layout geometry t 27 (zeroAccumulator ops t s)

#print axioms LarkPtxMatrix.Gemm.initialize_execute

theorem suffix_execute (ops : Ops α) (t : Nat) (s : Machine α)
    (ht : t < 32768) (hpc : s.pc = 41) (hs : s.registers.stopped = false)
    (hcol : s.registers.i32 11 = some ((t%512 : Nat) : Int))
    (hrow : s.registers.i32 9 = some ((t/512*256 : Nat) : Int)) :
    Steps ops layout geometry t program s (initializedSuffix ops t s) := by
  apply steps_trans _ _ _ _ _ _ _ _ (column_wide_execute ops t s hpc hs hcol)
  apply steps_trans _ _ _ _ _ _ _ _ (next_column_execute ops t s hpc hs hcol)
  apply steps_trans _ _ _ _ _ _ _ _ (next_wide_execute ops t s hpc hs)
  apply steps_trans _ _ _ _ _ _ _ _ (matrix_wide_execute ops t s ht hpc hs hrow)
  exact steps_trans _ _ _ _ _ _ _ _ (zero_execute ops t s hpc hs) (initialize_execute ops t s hpc hs)

def initialized (ops : Ops α) (t : Nat) (s : State α) : Machine α :=
  initializedSuffix ops t (addressPairs t s 14)

theorem prologue_execute (ops : Ops α) (t : Nat) (s : State α) (ht : t < 32768) :
    Steps ops layout geometry t program (start s) (initialized ops t s) := by
  have hp := addressPairs_execute ops t 14 s ht (by decide)
  have hs := suffix_execute ops t (addressPairs t s 14) ht
    (by simp only [addressPairs_pc])
    (addressPairs_stopped t 14 s) (addressPairs_column t 14 s) (addressPairs_row_offset t 14 s)
  exact steps_trans _ _ _ _ _ _ _ _ hp hs

theorem initializedSuffix_pc (ops : Ops α) (t : Nat) (s : Machine α) :
    (initializedSuffix ops t s).pc = s.pc+6 := by
  simp only [initializedSuffix, zeroAccumulator, matrixWide, nextWide, nextColumn, columnWide,
    setFloat_pc, setIndex32_pc, setIndex64_pc]

theorem initialized_pc (ops : Ops α) (t : Nat) (s : State α) :
    (initialized ops t s).pc = 47 := by
  simp only [initialized, initializedSuffix_pc, addressPairs_pc]

theorem initializedSuffix_base (ops : Ops α) (t : Nat) (s : Machine α) :
    (initializedSuffix ops t s).registers.base = s.registers.base := by
  simp only [initializedSuffix, zeroAccumulator, matrixWide, nextWide, nextColumn, columnWide,
    setIndex32_base, setFloat_base, setIndex64_base]

theorem initialized_base (ops : Ops α) (t : Nat) (s : State α) :
    (initialized ops t s).registers.base = s := by
  simp only [initialized, initializedSuffix_base, addressPairs_base]

def aCell (t c j : Nat) : Location := ⟨.global, 0, 0, t/512*256+16*c+j⟩
def bCell (t c j : Nat) : Location := ⟨.global, 0, 1, (16*c+j)*512+t%512⟩
def aBase (c : Nat) : Pointer := ⟨0, ((32*c : Nat) : Int), true⟩
def bBase (c : Nat) : Pointer := ⟨1, ((16384*c : Nat) : Int), true⟩
def aPointer (t c : Nat) : Pointer := ⟨0, ((t/512*512+32*c : Nat) : Int), true⟩
def bStride (t j : Nat) : Int := (( (t%512+j*512)*2 : Nat) : Int)
def bPointer (t c j : Nat) : Pointer :=
  ⟨1, ((16384*c+(t%512+j*512)*2 : Nat) : Int), true⟩

theorem a_address (t c j : Nat) (ht : t < 32768) (hc : c < 16) (hj : j < 16) :
    address layout geometry t (aPointer t c) ((2*j : Nat) : Int) false =
      some (aCell t c j) := by
  have hr : t/512 < 64 := by omega
  have he : ((t/512*512+32*c : Nat) : Int) + ((2*j : Nat) : Int) =
      ((t/512*256+16*c+j : Nat) : Int)*2 := by
    simp only [Int.natCast_add, Int.natCast_mul]; omega
  have hs : signed64 (((t/512*256+16*c+j : Nat) : Int)*2) := by
    unfold signed64; simp only [Int.natCast_add, Int.natCast_mul]; omega
  have hb : t/512*256+16*c+j < 64*256 := by omega
  unfold aPointer
  rw [aligned_address layout geometry t 0 (t/512*256+16*c+j) _ _ false he hs]
  exact read_location layout geometry t 0 _ ⟨.input, 64*256⟩ (by rfl) hb

theorem b_address (t c j : Nat) (hc : c < 16) (hj : j < 16) :
    address layout geometry t (bPointer t c j) 0 false = some (bCell t c j) := by
  have hcol : t%512 < 512 := Nat.mod_lt _ (by decide)
  have he : ((16384*c+(t%512+j*512)*2 : Nat) : Int)+0 =
      (((16*c+j)*512+t%512 : Nat) : Int)*2 := by
    simp only [Int.natCast_add, Int.natCast_mul]; omega
  have hs : signed64 ((((16*c+j)*512+t%512 : Nat) : Int)*2) := by
    unfold signed64; simp only [Int.natCast_add, Int.natCast_mul]; omega
  have hb : (16*c+j)*512+t%512 < 256*512 := by omega
  unfold bPointer
  rw [aligned_address layout geometry t 1 ((16*c+j)*512+t%512) _ 0 false he hs]
  exact read_location layout geometry t 1 _ ⟨.input, 256*512⟩ (by rfl) hb

def inputRegister (j : Nat) : Nat := if j = 0 then 68 else 35+2*j
def sumRegister (j : Nat) : Nat := if j = 15 then 68 else 37+2*j
def strideRegister (j : Nat) : Nat := if j = 0 then 17 else if j = 1 then 18 else 18-j

def term (j : Nat) : List Instruction :=
  [.base (.loadHalf (2*j+1) 27 ((2*j : Nat) : Int)),
   .base (.fromHalf (4+2*j) (2*j+1)),
   .base (.addSigned64 (28+j) 48 (.reg (strideRegister j))),
   .base (.loadHalf (2*j+2) (28+j) 0),
   .base (.fromHalf (5+2*j) (2*j+2)),
   .base (.binaryFloat (36+2*j) .mul (4+2*j) (5+2*j)),
   .base (.binaryFloat (sumRegister j) .add (inputRegister j) (36+2*j))]

theorem program_term : ∀ (j : Fin 16) (q : Fin 7),
    program[48+7*j.val+q.val]? = (term j.val)[q.val]? := by decide

theorem base_step_in_term (ops : Ops α) (t j q : Nat) (s u : Machine α)
    (instruction : LarkPtxDot.Instruction) (hj : j < 16) (hq : q < 7)
    (hpc : s.pc = 48+7*j+q) (hs : s.registers.stopped = false)
    (hi : (term j)[q]? = some (.base instruction))
    (he : LarkPtxDot.execute ops layout geometry t instruction s = some u) :
    Steps ops layout geometry t program s u := by
  have hf := program_term ⟨j, hj⟩ ⟨q, hq⟩
  rw [hi] at hf
  apply one_step
  rw [transition_at ops layout geometry t program s (.base instruction) hs
    (by rw [hpc]; exact hf), base_step]
  exact he

def termLoadA (t c j : Nat) (a : α) (s : Machine α) : Machine α :=
  loadedHalf s t (2*j+1) (aCell t c j) a
def termCastA (ops : Ops α) (t c j : Nat) (a : α) (s : Machine α) : Machine α :=
  setFloat (termLoadA t c j a s) (4+2*j) (ops.fromHalf a)
def termAddressB (ops : Ops α) (t c j : Nat) (a : α) (s : Machine α) : Machine α :=
  setPointer (termCastA ops t c j a s) (28+j) (bPointer t c j)
def termLoadB (ops : Ops α) (t c j : Nat) (a b : α) (s : Machine α) : Machine α :=
  loadedHalf (termAddressB ops t c j a s) t (2*j+2) (bCell t c j) b
def termCastB (ops : Ops α) (t c j : Nat) (a b : α) (s : Machine α) : Machine α :=
  setFloat (termLoadB ops t c j a b s) (5+2*j) (ops.fromHalf b)
def termProduct (ops : Ops α) (t c j : Nat) (a b : α) (s : Machine α) : Machine α :=
  setFloat (termCastB ops t c j a b s) (36+2*j) (ops.mul (ops.fromHalf a) (ops.fromHalf b))
def termResult (ops : Ops α) (t c j : Nat) (a b acc : α) (s : Machine α) : Machine α :=
  setFloat (termProduct ops t c j a b s) (sumRegister j)
    (ops.add acc (ops.mul (ops.fromHalf a) (ops.fromHalf b)))

theorem term_execute (ops : Ops α) (t c j : Nat) (a b acc : α) (s : Machine α)
    (ht : t < 32768) (hc : c < 16) (hj : j < 16)
    (hpc : s.pc = 48+7*j) (hs : s.registers.stopped = false)
    (hpA : s.registers.pointer 27 = some (aPointer t c))
    (hpB : s.registers.pointer 48 = some (bBase c))
    (hstride : s.registers.i64 (strideRegister j) = some (bStride t j))
    (ha : s.registers.base.memory (aCell t c j) = some a)
    (hb : s.registers.base.memory (bCell t c j) = some b)
    (hacc : s.registers.scalar (inputRegister j) = some acc) :
    Steps ops layout geometry t program s (termResult ops t c j a b acc s) := by
  have h1 := base_step_in_term ops t j 0 s (termLoadA t c j a s)
    (.loadHalf (2*j+1) 27 ((2*j : Nat) : Int)) hj (by decide)
    (by simpa only [Nat.add_zero] using hpc) hs (by rfl)
    (loadHalf_step ops layout geometry t (2*j+1) 27 _ s _ _ a hpA (a_address t c j ht hc hj) ha)
  have h2 := base_step_in_term ops t j 1 (termLoadA t c j a s) (termCastA ops t c j a s)
    (.fromHalf (4+2*j) (2*j+1)) hj (by decide)
    (by simp only [termLoadA, loadedHalf_pc]; omega)
    (by simpa only [termLoadA, loadedHalf_stopped] using hs) (by rfl)
    (fromHalf_step ops layout geometry t (4+2*j) (2*j+1) _ a (by simp [termLoadA]))
  have hptr : (termCastA ops t c j a s).registers.values (.int64 48) = some (.address (bBase c)) := by
    apply pointer_values
    simpa only [termCastA, termLoadA, setFloat_pointer, loadedHalf_pointer] using hpB
  have hval : operand64 (termCastA ops t c j a s).registers (.reg (strideRegister j)) =
      some (bStride t j) := by
    simpa only [operand64, termCastA, termLoadA, setFloat_i64, loadedHalf_i64] using hstride
  have hcol : t%512 < 512 := Nat.mod_lt _ (by decide)
  have hbound : signed64 (bStride t j) ∧ signed64 ((bBase c).offset+bStride t j) := by
    unfold bStride bBase signed64
    simp only [Int.natCast_add, Int.natCast_mul]; omega
  have e3 := pointer_add_step ops layout geometry t (28+j) 48 (.reg (strideRegister j))
    (bBase c) (bStride t j) (termCastA ops t c j a s) hptr hval hbound
  have heq : { bBase c with offset := (bBase c).offset+bStride t j } = bPointer t c j := by
    simp only [bBase, bStride, bPointer, Int.natCast_add]
  rw [heq] at e3
  have h3 := base_step_in_term ops t j 2 (termCastA ops t c j a s) (termAddressB ops t c j a s)
    (.addSigned64 (28+j) 48 (.reg (strideRegister j))) hj (by decide)
    (by simp only [termCastA, termLoadA, setFloat_pc, loadedHalf_pc]; omega)
    (by simpa only [termCastA, termLoadA, setFloat_stopped, loadedHalf_stopped] using hs)
    (by rfl) e3
  have h4 := base_step_in_term ops t j 3 (termAddressB ops t c j a s) (termLoadB ops t c j a b s)
    (.loadHalf (2*j+2) (28+j) 0) hj (by decide)
    (by simp only [termAddressB, termCastA, termLoadA, setPointer_pc, setFloat_pc, loadedHalf_pc]; omega)
    (by simpa only [termAddressB, termCastA, termLoadA, setPointer_stopped, setFloat_stopped,
      loadedHalf_stopped] using hs) (by rfl)
    (loadHalf_step ops layout geometry t (2*j+2) (28+j) 0 _ _ _ b
      (by simp [termAddressB]) (b_address t c j hc hj)
      (by simpa only [termAddressB, termCastA, termLoadA, setPointer_base, setFloat_memory,
        loadedHalf_memory] using hb))
  have h5 := base_step_in_term ops t j 4 (termLoadB ops t c j a b s) (termCastB ops t c j a b s)
    (.fromHalf (5+2*j) (2*j+2)) hj (by decide)
    (by simp only [termLoadB, termAddressB, termCastA, termLoadA, setPointer_pc, setFloat_pc,
      loadedHalf_pc]; omega)
    (by simpa only [termLoadB, termAddressB, termCastA, termLoadA, loadedHalf_stopped,
      setPointer_stopped, setFloat_stopped] using hs) (by rfl)
    (fromHalf_step ops layout geometry t (5+2*j) (2*j+2) _ b (by simp [termLoadB]))
  have hrAB : 4+2*j ≠ 5+2*j := by omega
  have h6 := base_step_in_term ops t j 5 (termCastB ops t c j a b s) (termProduct ops t c j a b s)
    (.binaryFloat (36+2*j) .mul (4+2*j) (5+2*j)) hj (by decide)
    (by simp only [termCastB, termLoadB, termAddressB, termCastA, termLoadA,
      setPointer_pc, setFloat_pc, loadedHalf_pc]; omega)
    (by simpa only [termCastB, termLoadB, termAddressB, termCastA, termLoadA,
      setPointer_stopped, setFloat_stopped, loadedHalf_stopped] using hs) (by rfl)
    (binaryFloat_step ops layout geometry t (36+2*j) (4+2*j) (5+2*j) .mul _ _ _
      (by simp [termCastB, termLoadB, termAddressB, termCastA, hrAB])
      (by simp [termCastB]))
  have hrA : inputRegister j ≠ 4+2*j := by unfold inputRegister; split <;> omega
  have hrB : inputRegister j ≠ 5+2*j := by unfold inputRegister; split <;> omega
  have hrP : inputRegister j ≠ 36+2*j := by unfold inputRegister; split <;> omega
  have h7 := base_step_in_term ops t j 6 (termProduct ops t c j a b s) (termResult ops t c j a b acc s)
    (.binaryFloat (sumRegister j) .add (inputRegister j) (36+2*j)) hj (by decide)
    (by simp only [termProduct, termCastB, termLoadB, termAddressB, termCastA, termLoadA,
      setPointer_pc, setFloat_pc, loadedHalf_pc]; omega)
    (by simpa only [termProduct, termCastB, termLoadB, termAddressB, termCastA, termLoadA,
      setPointer_stopped, setFloat_stopped, loadedHalf_stopped] using hs) (by rfl)
    (binaryFloat_step ops layout geometry t (sumRegister j) (inputRegister j) (36+2*j) .add _ _ _
      (by simp [termProduct, termCastB, termLoadB, termAddressB, termCastA, termLoadA,
        hrA, hrB, hrP, hacc]) (by simp [termProduct]))
  apply steps_trans _ _ _ _ _ _ _ _ h1
  apply steps_trans _ _ _ _ _ _ _ _ h2
  apply steps_trans _ _ _ _ _ _ _ _ h3
  apply steps_trans _ _ _ _ _ _ _ _ h4
  apply steps_trans _ _ _ _ _ _ _ _ h5
  exact steps_trans _ _ _ _ _ _ _ _ h6 h7

theorem termResult_pc (ops : Ops α) (t c j : Nat) (a b acc : α) (s : Machine α) :
    (termResult ops t c j a b acc s).pc = s.pc+7 := by
  simp only [termResult, termProduct, termCastB, termLoadB, termAddressB, termCastA, termLoadA,
    setFloat_pc, loadedHalf_pc, setPointer_pc]

theorem termResult_stopped (ops : Ops α) (t c j : Nat) (a b acc : α) (s : Machine α) :
    (termResult ops t c j a b acc s).registers.stopped = s.registers.stopped := by
  simp only [termResult, termProduct, termCastB, termLoadB, termAddressB, termCastA, termLoadA,
    setFloat_stopped, loadedHalf_stopped, setPointer_stopped]

theorem termResult_i32 (ops : Ops α) (t c j r : Nat) (a b acc : α) (s : Machine α) :
    (termResult ops t c j a b acc s).registers.i32 r = s.registers.i32 r := by
  simp only [termResult, termProduct, termCastB, termLoadB, termAddressB, termCastA, termLoadA,
    setFloat_i32, loadedHalf_i32, setPointer_i32]

theorem termResult_pointer (ops : Ops α) (t c j r : Nat) (a b acc : α) (s : Machine α) :
    (termResult ops t c j a b acc s).registers.pointer r =
      if r = 28+j then some (bPointer t c j) else s.registers.pointer r := by
  simp only [termResult, termProduct, termCastB, termLoadB, termAddressB, termCastA, termLoadA,
    setFloat_pointer, loadedHalf_pointer, setPointer_pointer]

theorem termResult_i64 (ops : Ops α) (t c j r : Nat) (a b acc : α) (s : Machine α) :
    (termResult ops t c j a b acc s).registers.i64 r =
      if r = 28+j then none else s.registers.i64 r := by
  simp only [termResult, termProduct, termCastB, termLoadB, termAddressB, termCastA, termLoadA,
    setFloat_i64, loadedHalf_i64, setPointer_i64]

theorem termResult_memory (ops : Ops α) (t c j : Nat) (a b acc : α) (s : Machine α) :
    (termResult ops t c j a b acc s).registers.base.memory = s.registers.base.memory := by
  simp only [termResult, termProduct, termCastB, termLoadB, termAddressB, termCastA, termLoadA,
    setFloat_memory, loadedHalf_memory, setPointer_base]

theorem termResult_scalar (ops : Ops α) (t c j : Nat) (a b acc : α) (s : Machine α) :
    (termResult ops t c j a b acc s).registers.scalar (sumRegister j) =
      some (ops.add acc (ops.mul (ops.fromHalf a) (ops.fromHalf b))) := by
  simp [termResult]

def accumulatorRegister (j : Nat) : Nat := if j = 0 ∨ j = 16 then 68 else 35+2*j

theorem source_accumulator : ∀ j : Fin 16,
    inputRegister j.val = accumulatorRegister j.val ∧
    sumRegister j.val = accumulatorRegister (j.val+1) := by decide

theorem stride_register_bound (j : Nat) : strideRegister j < 19 := by
  unfold strideRegister
  split <;> try omega
  split <;> omega

def Reads (input : Nat → Nat → α) (s : Machine α) : Prop :=
  (∀ i, i < 64*256 → s.registers.base.memory ⟨.global, 0, 0, i⟩ = some (input 0 i)) ∧
  (∀ i, i < 256*512 → s.registers.base.memory ⟨.global, 0, 1, i⟩ = some (input 1 i))

structure BodyInvariant (input : Nat → Nat → α) (t c j : Nat) (acc : α) (s : Machine α) : Prop where
  pc : s.pc = 48+7*j
  stopped : s.registers.stopped = false
  a : s.registers.pointer 27 = some (aPointer t c)
  b : s.registers.pointer 48 = some (bBase c)
  strides : ∀ k, k < 16 → s.registers.i64 (strideRegister k) = some (bStride t k)
  accumulator : s.registers.scalar (accumulatorRegister j) = some acc
  reads : Reads input s
  thread : s.registers.i32 1 = some (t : Int)
  counter : s.registers.i32 27 = some ((16*c : Nat) : Int)
  output : s.registers.pointer 24 = some ⟨2, 0, false⟩
  abase : s.registers.pointer 47 = some (aBase c)
  rowOffset : s.registers.i64 19 = some ((t/512*512 : Nat) : Int)

def nextValue (ops : Ops α) (input : Nat → Nat → α) (t c j : Nat) (acc : α) : α :=
  ops.add acc (ops.mul (ops.fromHalf (input 0 (t/512*256+16*c+j)))
    (ops.fromHalf (input 1 ((16*c+j)*512+t%512))))

def chunkStep (ops : Ops α) (input : Nat → Nat → α) (t c j : Nat) (acc : α)
    (s : Machine α) : Machine α :=
  termResult ops t c j (input 0 (t/512*256+16*c+j)) (input 1 ((16*c+j)*512+t%512)) acc s

theorem chunk_step (ops : Ops α) (input : Nat → Nat → α) (t c j : Nat) (acc : α)
    (s : Machine α) (ht : t < 32768) (hc : c < 16) (hj : j < 16)
    (h : BodyInvariant input t c j acc s) :
    Steps ops layout geometry t program s (chunkStep ops input t c j acc s) ∧
    BodyInvariant input t c (j+1) (nextValue ops input t c j acc) (chunkStep ops input t c j acc s) := by
  have hr : t/512 < 64 := by omega
  have hcol : t%512 < 512 := Nat.mod_lt _ (by decide)
  have hreg := source_accumulator ⟨j, hj⟩
  have e := term_execute ops t c j _ _ acc s ht hc hj h.pc h.stopped h.a h.b (h.strides j hj)
    (h.reads.1 _ (by omega)) (h.reads.2 _ (by omega)) (by rw [hreg.1]; exact h.accumulator)
  refine ⟨e, ?_⟩
  constructor
  · rw [chunkStep, termResult_pc, h.pc]; omega
  · simpa only [chunkStep, termResult_stopped] using h.stopped
  · simpa only [chunkStep, termResult_pointer, if_neg (by omega : 27 ≠ 28+j)] using h.a
  · simpa only [chunkStep, termResult_pointer, if_neg (by omega : 48 ≠ 28+j)] using h.b
  · intro k hk
    have hkb := stride_register_bound k
    simpa only [chunkStep, termResult_i64, if_neg (by omega : strideRegister k ≠ 28+j)]
      using h.strides k hk
  · rw [← hreg.2]
    exact termResult_scalar ops t c j _ _ acc s
  · constructor
    · intro i hi
      rw [chunkStep, termResult_memory]
      exact h.reads.1 i hi
    · intro i hi
      rw [chunkStep, termResult_memory]
      exact h.reads.2 i hi
  · simpa only [chunkStep, termResult_i32] using h.thread
  · simpa only [chunkStep, termResult_i32] using h.counter
  · simpa only [chunkStep, termResult_pointer, if_neg (by omega : 24 ≠ 28+j)] using h.output
  · simpa only [chunkStep, termResult_pointer, if_neg (by omega : 47 ≠ 28+j)] using h.abase
  · simpa only [chunkStep, termResult_i64, if_neg (by omega : 19 ≠ 28+j)] using h.rowOffset

def foldTerms (ops : Ops α) (input : Nat → Nat → α) (t c j : Nat) : Nat → α → α
  | 0, acc => acc
  | n+1, acc => foldTerms ops input t c (j+1) n (nextValue ops input t c j acc)

def runTerms (ops : Ops α) (input : Nat → Nat → α) (t c j : Nat) : Nat → α → Machine α → Machine α
  | 0, _, s => s
  | n+1, acc, s => runTerms ops input t c (j+1) n (nextValue ops input t c j acc)
      (chunkStep ops input t c j acc s)

theorem runTerms_execute (ops : Ops α) (input : Nat → Nat → α) (t c j n : Nat) (acc : α)
    (s : Machine α) (ht : t < 32768) (hc : c < 16) (hjn : j+n ≤ 16)
    (h : BodyInvariant input t c j acc s) :
    Steps ops layout geometry t program s (runTerms ops input t c j n acc s) ∧
    BodyInvariant input t c (j+n) (foldTerms ops input t c j n acc) (runTerms ops input t c j n acc s) := by
  induction n generalizing j acc s with
  | zero => exact ⟨.refl _, h⟩
  | succ n ih =>
      have head := chunk_step ops input t c j acc s ht hc (by omega) h
      have tail := ih (j+1) (nextValue ops input t c j acc) (chunkStep ops input t c j acc s)
        (by omega) head.2
      refine ⟨steps_trans _ _ _ _ _ _ _ _ head.1 tail.1, ?_⟩
      have he : j+(n+1) = (j+1)+n := by omega
      rw [he]
      exact tail.2

structure LoopInvariant (input : Nat → Nat → α) (t c : Nat) (acc : α) (s : Machine α) : Prop where
  pc : s.pc = if c < 16 then 47 else 165
  stopped : s.registers.stopped = false
  a : s.registers.pointer 47 = some (aBase c)
  b : s.registers.pointer 48 = some (bBase c)
  strides : ∀ k, k < 16 → s.registers.i64 (strideRegister k) = some (bStride t k)
  accumulator : s.registers.scalar 68 = some acc
  reads : Reads input s
  thread : s.registers.i32 1 = some (t : Int)
  counter : s.registers.i32 27 = some ((16*c : Nat) : Int)
  output : s.registers.pointer 24 = some ⟨2, 0, false⟩
  rowOffset : s.registers.i64 19 = some ((t/512*512 : Nat) : Int)

def bodyStart (t c : Nat) (s : Machine α) : Machine α := setPointer s 27 (aPointer t c)

theorem body_entry (ops : Ops α) (input : Nat → Nat → α) (t c : Nat) (acc : α) (s : Machine α)
    (ht : t < 32768) (hc : c < 16) (h : LoopInvariant input t c acc s) :
    Steps ops layout geometry t program s (bodyStart t c s) ∧
    BodyInvariant input t c 0 acc (bodyStart t c s) := by
  have hr : t/512 < 64 := by omega
  have hp : s.pc = 47 := by simpa only [if_pos hc] using h.pc
  have hbound : signed64 ((t/512*512 : Nat) : Int) ∧
      signed64 ((aBase c).offset+((t/512*512 : Nat) : Int)) := by
    unfold aBase signed64
    simp only [Int.natCast_mul]; omega
  have e := pointer_add_step ops layout geometry t 27 47 (.reg 19) (aBase c)
    ((t/512*512 : Nat) : Int) s (pointer_values _ _ _ h.a) h.rowOffset hbound
  have heq : { aBase c with offset := (aBase c).offset+((t/512*512 : Nat) : Int) } =
      aPointer t c := by
    have he : ((32*c : Nat) : Int)+((t/512*512 : Nat) : Int) =
        ((t/512*512+32*c : Nat) : Int) := by
      simp only [Int.natCast_add]; omega
    simp only [aBase, aPointer, he]
  rw [heq] at e
  have hexe : Steps ops layout geometry t program s (bodyStart t c s) := by
    apply one_step
    rw [transition_at ops layout geometry t program s (.base (.addSigned64 27 47 (.reg 19)))
      h.stopped (by rw [hp]; rfl), base_step]
    exact e
  refine ⟨hexe, ?_⟩
  constructor
  · simp only [bodyStart, setPointer_pc, hp]
  · simpa only [bodyStart, setPointer_stopped] using h.stopped
  · simp [bodyStart]
  · simpa only [bodyStart, setPointer_pointer, if_neg (by decide : 48 ≠ 27)] using h.b
  · intro k hk
    have hkb := stride_register_bound k
    simpa only [bodyStart, setPointer_i64, if_neg (by omega : strideRegister k ≠ 27)] using h.strides k hk
  · simpa only [bodyStart, setPointer_scalar, accumulatorRegister, if_pos (by decide : 0 = 0 ∨ 0 = 16)]
      using h.accumulator
  · exact h.reads
  · simpa only [bodyStart, setPointer_i32] using h.thread
  · simpa only [bodyStart, setPointer_i32] using h.counter
  · simpa only [bodyStart, setPointer_pointer, if_neg (by decide : 24 ≠ 27)] using h.output
  · simpa only [bodyStart, setPointer_pointer, if_neg (by decide : 47 ≠ 27)] using h.a
  · simpa only [bodyStart, setPointer_i64, if_neg (by decide : 19 ≠ 27)] using h.rowOffset

def chunkValue (ops : Ops α) (input : Nat → Nat → α) (t c : Nat) (acc : α) : α :=
  foldTerms ops input t c 0 16 acc

def bodyEnd (ops : Ops α) (input : Nat → Nat → α) (t c : Nat) (acc : α)
    (s : Machine α) : Machine α := runTerms ops input t c 0 16 acc (bodyStart t c s)

theorem body_execute (ops : Ops α) (input : Nat → Nat → α) (t c : Nat) (acc : α)
    (s : Machine α) (ht : t < 32768) (hc : c < 16) (h : LoopInvariant input t c acc s) :
    Steps ops layout geometry t program s (bodyEnd ops input t c acc s) ∧
    BodyInvariant input t c 16 (chunkValue ops input t c acc) (bodyEnd ops input t c acc s) := by
  have head := body_entry ops input t c acc s ht hc h
  have tail := runTerms_execute ops input t c 0 16 acc (bodyStart t c s) ht hc (by decide) head.2
  exact ⟨steps_trans _ _ _ _ _ _ _ _ head.1 tail.1, tail.2⟩

def bAdvanced (c : Nat) (s : Machine α) : Machine α := setPointer s 48 (bBase (c+1))
def aAdvanced (c : Nat) (s : Machine α) : Machine α := setPointer (bAdvanced c s) 47 (aBase (c+1))
def counted (c : Nat) (s : Machine α) : Machine α :=
  setIndex32 (aAdvanced c s) 27 ((16*(c+1) : Nat) : Int)
def compared (c : Nat) (s : Machine α) : Machine α :=
  setPredicate (counted c s) 1 (((16*(c+1) : Nat) : Int) != (256 : Int))
def controlResult (c : Nat) (s : Machine α) : Machine α :=
  let next := compared c s
  { next with pc := if (((16*(c+1) : Nat) : Int) != (256 : Int)) then 47 else next.pc+1 }

theorem control_execute (ops : Ops α) (input : Nat → Nat → α) (t c : Nat) (acc : α)
    (s : Machine α) (hc : c < 16) (h : BodyInvariant input t c 16 acc s) :
    Steps ops layout geometry t program s (controlResult c s) := by
  have hpc : s.pc = 160 := h.pc
  have hb : signed64 16384 ∧ signed64 ((bBase c).offset+16384) := by
    unfold signed64 bBase; simp only [Int.natCast_mul]; omega
  have e1 := pointer_add_step ops layout geometry t 48 48 (.imm 16384) (bBase c) 16384 s
    (pointer_values _ _ _ h.b) (by rfl) hb
  have heB : { bBase c with offset := (bBase c).offset+16384 } = bBase (c+1) := by
    have he : ((16384*c : Nat) : Int)+16384 = ((16384*(c+1) : Nat) : Int) := by
      simp only [Int.natCast_add, Int.natCast_mul]; omega
    simp only [bBase, he]
  rw [heB] at e1
  have h1 : Steps ops layout geometry t program s (bAdvanced c s) := by
    apply one_step
    rw [transition_at ops layout geometry t program s (.base (.addSigned64 48 48 (.imm 16384)))
      h.stopped (by rw [hpc]; rfl), base_step]
    exact e1
  have ha : signed64 32 ∧ signed64 ((aBase c).offset+32) := by
    unfold signed64 aBase; simp only [Int.natCast_mul]; omega
  have hpA : (bAdvanced c s).registers.values (.int64 47) = some (.address (aBase c)) := by
    apply pointer_values
    simpa [bAdvanced] using h.abase
  have e2 := pointer_add_step ops layout geometry t 47 47 (.imm 32) (aBase c) 32 (bAdvanced c s)
    hpA (by rfl) ha
  have heA : { aBase c with offset := (aBase c).offset+32 } = aBase (c+1) := by
    have he : ((32*c : Nat) : Int)+32 = ((32*(c+1) : Nat) : Int) := by
      simp only [Int.natCast_add, Int.natCast_mul]; omega
    simp only [aBase, he]
  rw [heA] at e2
  have h2 : Steps ops layout geometry t program (bAdvanced c s) (aAdvanced c s) := by
    apply one_step
    rw [transition_at ops layout geometry t program (bAdvanced c s) (.base (.addSigned64 47 47 (.imm 32)))
      (by simpa only [bAdvanced, setPointer_stopped] using h.stopped)
      (by simp only [bAdvanced, setPointer_pc, hpc]; rfl), base_step]
    exact e2
  have hg : signed32 ((16*c : Nat) : Int) ∧ signed32 16 ∧
      signed32 (((16*c : Nat) : Int)+16) := by
    unfold signed32; simp only [Int.natCast_mul]; omega
  have hx : (aAdvanced c s).registers.i32 27 = some ((16*c : Nat) : Int) := by
    simpa only [aAdvanced, bAdvanced, setPointer_i32] using h.counter
  have e3 := add32_step ops layout geometry t 27 27 (.imm 16) (aAdvanced c s)
    ((16*c : Nat) : Int) 16 hx (by rfl) hg
  have heC : ((16*c : Nat) : Int)+16 = ((16*(c+1) : Nat) : Int) := by
    simp only [Int.natCast_add, Int.natCast_mul]; omega
  rw [heC] at e3
  have h3 : Steps ops layout geometry t program (aAdvanced c s) (counted c s) := by
    apply one_step
    rw [transition_at ops layout geometry t program (aAdvanced c s) (.base (.addSigned32 27 27 (.imm 16)))
      (by simpa only [aAdvanced, bAdvanced, setPointer_stopped] using h.stopped)
      (by simp only [aAdvanced, bAdvanced, setPointer_pc, hpc]; rfl), base_step]
    exact e3
  have hp : signed32 ((16*(c+1) : Nat) : Int) ∧ signed32 256 := by
    unfold signed32; simp only [Int.natCast_add, Int.natCast_mul]; omega
  have e4 := compare_ne_step ops layout geometry t 1 27 (.imm 256) (counted c s)
    ((16*(c+1) : Nat) : Int) 256 (by simp [counted]) (by rfl) hp
  have h4 : Steps ops layout geometry t program (counted c s) (compared c s) := by
    apply one_step
    rw [transition_at ops layout geometry t program (counted c s) (.base (.compareNeSigned32 1 27 (.imm 256)))
      (by change s.registers.stopped = false; exact h.stopped)
      (by simp only [counted, aAdvanced, bAdvanced, setIndex32_pc, setPointer_pc, hpc]; rfl), base_step]
    exact e4
  have h5 : Steps ops layout geometry t program (compared c s) (controlResult c s) := by
    apply one_step
    rw [transition_at ops layout geometry t program (compared c s) (.base (.branch 1 47))
      (by change s.registers.stopped = false; exact h.stopped)
      (by simp only [compared, counted, aAdvanced, bAdvanced, setPredicate_pc,
        setIndex32_pc, setPointer_pc, hpc]; rfl), base_step]
    simp only [LarkPtxDot.execute, compared, setPredicate, bind, pure, Option.bind]
    rfl
  apply steps_trans _ _ _ _ _ _ _ _ h1
  apply steps_trans _ _ _ _ _ _ _ _ h2
  apply steps_trans _ _ _ _ _ _ _ _ h3
  exact steps_trans _ _ _ _ _ _ _ _ h4 h5

theorem control_pc (c : Nat) (s : Machine α) (hc : c < 16) (hpc : s.pc = 160) :
    (controlResult c s).pc = if c+1 < 16 then 47 else 165 := by
  by_cases hn : c+1 < 16
  · have hne : (16 : Int)*((c : Int)+1) ≠ 256 := by omega
    simp [controlResult, hne, hn]
  · have he : c+1 = 16 := by omega
    simp [controlResult, compared, counted, aAdvanced, bAdvanced, he, hn, hpc]

theorem control_memory (c : Nat) (s : Machine α) :
    (controlResult c s).registers.base.memory = s.registers.base.memory := rfl

theorem control_i64 (c r : Nat) (s : Machine α) :
    (controlResult c s).registers.i64 r = if r = 47 then none else if r = 48 then none else s.registers.i64 r := by
  simp only [controlResult, compared, counted, aAdvanced, bAdvanced,
    setPredicate_registers, setIndex32_i64, setPointer_i64]

theorem control_invariant (input : Nat → Nat → α) (t c : Nat) (acc : α) (s : Machine α)
    (hc : c < 16) (h : BodyInvariant input t c 16 acc s) :
    LoopInvariant input t (c+1) acc (controlResult c s) := by
  constructor
  · exact control_pc c s hc h.pc
  · change s.registers.stopped = false
    exact h.stopped
  · rfl
  · rfl
  · intro k hk
    have hkb := stride_register_bound k
    rw [control_i64, if_neg (by omega), if_neg (by omega)]
    exact h.strides k hk
  · change s.registers.scalar 68 = some acc
    simpa only [accumulatorRegister, if_pos (by decide : 16 = 0 ∨ 16 = 16)] using h.accumulator
  · change Reads input s
    exact h.reads
  · change s.registers.i32 1 = some (t : Int)
    exact h.thread
  · rfl
  · change s.registers.pointer 24 = some ⟨2, 0, false⟩
    exact h.output
  · rw [control_i64, if_neg (by decide : 19 ≠ 47), if_neg (by decide : 19 ≠ 48)]
    exact h.rowOffset

def iteration (ops : Ops α) (input : Nat → Nat → α) (t c : Nat) (acc : α) (s : Machine α) : Machine α :=
  controlResult c (bodyEnd ops input t c acc s)

theorem iteration_execute (ops : Ops α) (input : Nat → Nat → α) (t c : Nat) (acc : α)
    (s : Machine α) (ht : t < 32768) (hc : c < 16) (h : LoopInvariant input t c acc s) :
    Steps ops layout geometry t program s (iteration ops input t c acc s) ∧
    LoopInvariant input t (c+1) (chunkValue ops input t c acc) (iteration ops input t c acc s) := by
  have hb := body_execute ops input t c acc s ht hc h
  have he := control_execute ops input t c _ _ hc hb.2
  exact ⟨steps_trans _ _ _ _ _ _ _ _ hb.1 he, control_invariant input t c _ _ hc hb.2⟩

def foldChunks (ops : Ops α) (input : Nat → Nat → α) (t : Nat) : Nat → Nat → α → α
  | _, 0, acc => acc
  | c, n+1, acc => foldChunks ops input t (c+1) n (chunkValue ops input t c acc)

def runChunks (ops : Ops α) (input : Nat → Nat → α) (t : Nat) : Nat → Nat → α → Machine α → Machine α
  | _, 0, _, s => s
  | c, n+1, acc, s => runChunks ops input t (c+1) n (chunkValue ops input t c acc)
      (iteration ops input t c acc s)

theorem runChunks_execute (ops : Ops α) (input : Nat → Nat → α) (t c n : Nat) (acc : α)
    (s : Machine α) (ht : t < 32768) (hcn : c+n ≤ 16) (h : LoopInvariant input t c acc s) :
    Steps ops layout geometry t program s (runChunks ops input t c n acc s) ∧
    LoopInvariant input t (c+n) (foldChunks ops input t c n acc) (runChunks ops input t c n acc s) := by
  induction n generalizing c acc s with
  | zero => exact ⟨.refl _, h⟩
  | succ n ih =>
      have head := iteration_execute ops input t c acc s ht (by omega) h
      have tail := ih (c+1) (chunkValue ops input t c acc) (iteration ops input t c acc s)
        (by omega) head.2
      refine ⟨steps_trans _ _ _ _ _ _ _ _ head.1 tail.1, ?_⟩
      have he : c+(n+1) = (c+1)+n := by omega
      rw [he]
      exact tail.2

theorem addressPairs_i64 (t n r : Nat) (s : State α) (hn : n ≤ 14) :
    (addressPairs t s n).registers.i64 r =
      if 3 ≤ r ∧ r < 3+n then some (((t%512+(18-r)*512)*2 : Nat) : Int)
      else (coordinates t s).registers.i64 r := by
  induction n with
  | zero => simp only [addressPairs, Nat.add_zero, if_neg (by omega : ¬(3 ≤ r ∧ r < 3))]
  | succ n ih =>
      simp only [addressPairs, addressPair, setIndex64_i64, setIndex32_i64]
      by_cases he : r = 3+n
      · subst r
        rw [if_pos rfl, if_pos (by omega)]
        have hs : 18-(3+n) = 15-n := by omega
        rw [hs]
      · rw [if_neg he, ih (by omega)]
        have hs : (3 ≤ r ∧ r < 3+(n+1)) ↔ (3 ≤ r ∧ r < 3+n) := by omega
        simp only [hs]

theorem addressPairs_pointer (t n r : Nat) (s : State α) (hn : n ≤ 14) (hr : 17 ≤ r) :
    (addressPairs t s n).registers.pointer r = (coordinates t s).registers.pointer r := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [addressPairs, addressPair, setIndex64_pointer, setIndex32_pointer]
      rw [if_neg (by omega)]
      exact ih (by omega)

theorem addressPairs_thread (t n : Nat) (s : State α) :
    (addressPairs t s n).registers.i32 1 = some (t : Int) := by
  induction n with
  | zero =>
      simp only [addressPairs, coordinates, masked, rowOffset, row, adjusted, corrected,
        signed, indexed, setIndex32_i32, if_neg (by decide : 1 ≠ 11),
        if_neg (by decide : 1 ≠ 10), if_neg (by decide : 1 ≠ 9), if_neg (by decide : 1 ≠ 8),
        if_neg (by decide : 1 ≠ 7), if_neg (by decide : 1 ≠ 6), if_neg (by decide : 1 ≠ 5),
        if_pos rfl, ite_true]
  | succ n ih =>
      simp only [addressPairs, addressPair, setIndex64_i32, setIndex32_i32]
      rw [if_neg (by omega)]
      exact ih

theorem coordinates_pointer (t r : Nat) (s : State α) :
    (coordinates t s).registers.pointer r = (globals s).registers.pointer r := by
  simp only [coordinates, masked, rowOffset, row, adjusted, corrected, signed, indexed,
    setIndex32_pointer]

theorem initializedSuffix_i64 (ops : Ops α) (t r : Nat) (s : Machine α) :
    (initializedSuffix ops t s).registers.i64 r =
      if r = 19 then some (((t/512*256)*2 : Nat) : Int)
      else if r = 18 then some (((t%512+512)*2 : Nat) : Int)
      else if r = 17 then some ((t%512*2 : Nat) : Int) else s.registers.i64 r := by
  simp only [initializedSuffix, zeroAccumulator, matrixWide, nextWide, nextColumn, columnWide,
    setIndex32_i64, setFloat_i64, setIndex64_i64]

theorem initializedSuffix_pointer (ops : Ops α) (t r : Nat) (s : Machine α) (hr : 20 ≤ r) :
    (initializedSuffix ops t s).registers.pointer r = s.registers.pointer r := by
  simp only [initializedSuffix, zeroAccumulator, matrixWide, nextWide, nextColumn, columnWide,
    setIndex32_pointer, setFloat_pointer, setIndex64_pointer,
    if_neg (by omega : r ≠ 19), if_neg (by omega : r ≠ 18), if_neg (by omega : r ≠ 17)]

theorem initializedSuffix_stopped (ops : Ops α) (t : Nat) (s : Machine α) :
    (initializedSuffix ops t s).registers.stopped = s.registers.stopped := by
  simp only [initializedSuffix, zeroAccumulator, matrixWide, nextWide, nextColumn, columnWide,
    setIndex32_stopped, setFloat_stopped, setIndex64_stopped]

theorem initializedSuffix_accumulator (ops : Ops α) (t : Nat) (s : Machine α) :
    (initializedSuffix ops t s).registers.scalar 68 = some (ops.literal 0 1) := by
  simp [initializedSuffix, zeroAccumulator]

theorem initializedSuffix_thread (ops : Ops α) (t : Nat) (s : Machine α) :
    (initializedSuffix ops t s).registers.i32 1 = s.registers.i32 1 := by
  simp only [initializedSuffix, zeroAccumulator, matrixWide, nextWide, nextColumn,
    columnWide, setIndex32_i32, setFloat_i32, setIndex64_i32,
    if_neg (by decide : 1 ≠ 27), if_neg (by decide : 1 ≠ 26)]

theorem initializedSuffix_counter (ops : Ops α) (t : Nat) (s : Machine α) :
    (initializedSuffix ops t s).registers.i32 27 = some 0 := by
  simp [initializedSuffix]

theorem initializedSuffix_row_offset (ops : Ops α) (t : Nat) (s : Machine α) :
    (initializedSuffix ops t s).registers.i64 19 = some ((t/512*512 : Nat) : Int) := by
  rw [initializedSuffix_i64, if_pos rfl]
  simp only [Int.natCast_mul]
  congr 1
  omega

theorem initialized_strides (ops : Ops α) (t k : Nat) (s : State α) (hk : k < 16) :
    (initialized ops t s).registers.i64 (strideRegister k) = some (bStride t k) := by
  rw [initialized, initializedSuffix_i64]
  by_cases h0 : k = 0
  · subst k
    simp [strideRegister, bStride]
  · by_cases h1 : k = 1
    · subst k
      simp [strideRegister, bStride]
    · have hreg : strideRegister k = 18-k := by simp only [strideRegister, if_neg h0, if_neg h1]
      rw [hreg, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      rw [addressPairs_i64 t 14 (18-k) s (by decide), if_pos (by omega)]
      have he : 18-(18-k) = k := by omega
      rw [he]
      rfl

theorem initialized_pointer (ops : Ops α) (t r : Nat) (s : State α) (hr : 20 ≤ r) :
    (initialized ops t s).registers.pointer r = (globals s).registers.pointer r := by
  rw [initialized, initializedSuffix_pointer ops t r _ hr,
    addressPairs_pointer t 14 r s (by decide) (by omega), coordinates_pointer]

theorem initialized_loop (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α)
    (hreads : Reads input (start s)) :
    LoopInvariant input t 0 (ops.literal 0 1) (initialized ops t s) := by
  constructor
  · exact initialized_pc ops t s
  · rw [initialized, initializedSuffix_stopped]
    exact addressPairs_stopped t 14 s
  · rw [initialized_pointer ops t 47 s (by decide)]
    rfl
  · rw [initialized_pointer ops t 48 s (by decide)]
    rfl
  · exact fun k hk => initialized_strides ops t k s hk
  · exact initializedSuffix_accumulator ops t (addressPairs t s 14)
  · constructor
    · intro i hi
      rw [initialized_base]
      exact hreads.1 i hi
    · intro i hi
      rw [initialized_base]
      exact hreads.2 i hi
  · rw [initialized, initializedSuffix_thread]
    exact addressPairs_thread t 14 s
  · exact initializedSuffix_counter ops t (addressPairs t s 14)
  · rw [initialized_pointer ops t 24 s (by decide)]
    rfl
  · exact initializedSuffix_row_offset ops t (addressPairs t s 14)

def dotValue (ops : Ops α) (input : Nat → Nat → α) (t : Nat) : α :=
  foldChunks ops input t 0 16 (ops.literal 0 1)

def loopExit (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) : Machine α :=
  runChunks ops input t 0 16 (ops.literal 0 1) (initialized ops t s)

theorem source_to_loop_exit (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α)
    (ht : t < 32768) (hreads : Reads input (start s)) :
    Steps ops layout geometry t program (start s) (loopExit ops input t s) ∧
    LoopInvariant input t 16 (dotValue ops input t) (loopExit ops input t s) := by
  have he := runChunks_execute ops input t 0 16 (ops.literal 0 1) (initialized ops t s) ht
    (by decide) (initialized_loop ops input t s hreads)
  exact ⟨steps_trans _ _ _ _ _ _ _ _ (prologue_execute ops t s ht) he.1, he.2⟩

end Gemm

#print axioms steps_trans
#print axioms base_step
#print axioms signed_right_step
#print axioms unsigned_right_step
#print axioms and_step
#print axioms sub_step
#print axioms unsigned_wide_step
#print axioms bits32_negative512
#print axioms clear_low9
#print axioms one_step
#print axioms transition_at
#print axioms Gemm.coordinates_execute
#print axioms Gemm.addressPairs_execute
#print axioms Gemm.prologue_execute
#print axioms Gemm.initialized_pc
#print axioms Gemm.initialized_base
#print axioms Gemm.a_address
#print axioms Gemm.b_address
#print axioms Gemm.program_term
#print axioms Gemm.term_execute
#print axioms Gemm.chunk_step
#print axioms Gemm.runTerms_execute
#print axioms Gemm.body_entry
#print axioms Gemm.body_execute
#print axioms Gemm.control_execute
#print axioms Gemm.control_invariant
#print axioms Gemm.runChunks_execute
#print axioms Gemm.initialized_loop
#print axioms Gemm.source_to_loop_exit
end LarkPtxMatrix
