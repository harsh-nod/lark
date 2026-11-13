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

def setIndex64 (s : Machine α) (d : Nat) (v : Int) : Machine α :=
  advance s (putI64 s.registers d v)

@[simp] theorem setIndex64_i32 (s : Machine α) (d r : Nat) (v : Int) :
    (setIndex64 s d v).registers.i32 r = s.registers.i32 r := rfl

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
end LarkPtxMatrix
