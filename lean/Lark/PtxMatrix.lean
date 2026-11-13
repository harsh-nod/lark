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
end LarkPtxMatrix
