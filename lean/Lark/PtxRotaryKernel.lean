import Lark.PtxRotary

/-!
The complete unchanged 51-instruction compiled interleaved RoPE program.
The following proofs build actual successful transitions at the original
32768-lane launch. No new execution fuel or reduced CUDA contract is used.
-/
namespace LarkPtxRotary
namespace Kernel
open LarkNonlinear LarkPtxPointwise LarkPtxDot
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def program : List Instruction :=
  [(.base (.base (.parameter (4) (0)))),
   (.base (.base (.parameter (5) (1)))),
   (.base (.base (.parameter (6) (2)))),
   (.base (.base (.parameter (7) (3)))),
   (.base (.base (.toGlobal (8) (7)))),
   (.base (.base (.blockId (1)))),
   (.base (.shiftRightUnsigned32 2 1 31)),
   (.base (.base (.addSigned32 (3) (1) (.reg (2))))),
   (.base (.shiftRightSigned32 4 3 1)),
   (.base (.andBits32 5 3 (.imm (-2)))),
   (.base (.base (.toGlobal (9) (4)))),
   (.base (.base (.mulWideSigned32 (10) (5) (2)))),
   (.base (.base (.addSigned64 (11) (9) (.reg (10))))),
   (.base (.base (.loadHalf (1) (11) (0)))),
   (.base (.base (.fromHalf (3) (1)))),
   (.base (.base (.loadHalf (2) (11) (2)))),
   (.base (.base (.fromHalf (4) (2)))),
   (.base (.andBits32 6 1 (.imm (1)))),
   (.compareEqBits32 1 6 (.imm (1))),
   (.predicateLiteral 2 false),
   (.predicateXor 3 1 2),
   (.predicateNot 4 3),
   (.base (.base (.toGlobal (12) (6)))),
   (.base (.base (.mulWideSigned32 (13) (4) (2)))),
   (.base (.base (.addSigned64 (1) (12) (.reg (13))))),
   (.base (.base (.toGlobal (14) (5)))),
   (.base (.base (.addSigned64 (2) (14) (.reg (13))))),
   (.base (.base (.mulWideSigned32 (15) (1) (2)))),
   (.base (.base (.addSigned64 (3) (8) (.reg (15))))),
   (.base (.base (.branch (4) (31)))),
   (.branchAlways 41),
   (.base (.base (.loadHalf (6) (2) (0)))),
   (.base (.base (.fromHalf (10) (6)))),
   (.base (.base (.binaryFloat (13) .mul (3) (10)))),
   (.base (.base (.loadHalf (7) (1) (0)))),
   (.base (.base (.fromHalf (11) (7)))),
   (.base (.base (.binaryFloat (14) .mul (4) (11)))),
   (.base (.base (.binaryFloat (12) .sub (13) (14)))),
   (.base (.base (.toHalf (8) (12)))),
   (.base (.base (.storeHalf (3) (0) (8)))),
   (.branchAlways 50),
   (.base (.base (.loadHalf (3) (1) (0)))),
   (.base (.base (.fromHalf (5) (3)))),
   (.base (.base (.binaryFloat (8) .mul (3) (5)))),
   (.base (.base (.loadHalf (4) (2) (0)))),
   (.base (.base (.fromHalf (6) (4)))),
   (.base (.base (.binaryFloat (9) .mul (4) (6)))),
   (.base (.base (.binaryFloat (7) .add (8) (9)))),
   (.base (.base (.toHalf (5) (7)))),
   (.base (.base (.storeHalf (3) (0) (5)))),
   (.base (.base (.ret)))]

def layout : Layout :=
  ⟨[⟨.input, 256*128⟩, ⟨.input, 256*64⟩, ⟨.input, 256*64⟩,
     ⟨.output, 256*128⟩], [], []⟩

def geometry : Geometry := ⟨32768, 1, 32⟩

theorem bits32_negative2 : LarkPtxMatrix.bits32 (-2) = 4294967294 := by decide

theorem clear_low1 (n : Nat) (hn : n < 4294967296) :
    n &&& 4294967294 = (n / 2) * 2 := by
  have hd : (n &&& 4294967294) / 2 = n / 2 := by
    have hdiv : n / 2 < 2147483648 := by omega
    change (n &&& 4294967294) / 2^1 = n / 2
    rw [Nat.and_div_two_pow]
    change n / 2 &&& (2^31-1) = n / 2
    exact Nat.and_two_pow_sub_one_of_lt_two_pow hdiv
  have hm : (n &&& 4294967294) % 2 = 0 := by
    change (n &&& 4294967294) % 2^1 = 0
    rw [Nat.and_mod_two_pow]
    change n % 2 &&& 0 = 0
    simp
  have hs := Nat.mod_add_div (n &&& 4294967294) 2
  rw [hm, hd] at hs
  omega

def start (s : State α) : Machine α := { registers := { base := s } }
def parameterX (s : State α) : Machine α := setPointer (start s) 4 ⟨0, 0, false⟩
def parameterCosine (s : State α) : Machine α := setPointer (parameterX s) 5 ⟨1, 0, false⟩
def parameterSine (s : State α) : Machine α := setPointer (parameterCosine s) 6 ⟨2, 0, false⟩
def parameters (s : State α) : Machine α := setPointer (parameterSine s) 7 ⟨3, 0, false⟩
def globalOutput (s : State α) : Machine α := setPointer (parameters s) 8 ⟨3, 0, true⟩
def indexed (t : Nat) (s : State α) : Machine α := setIndex32 (globalOutput s) 1 (t : Int)
def corrected (t : Nat) (s : State α) : Machine α := setIndex32 (indexed t s) 2 0
def adjusted (t : Nat) (s : State α) : Machine α := setIndex32 (corrected t s) 3 (t : Int)
def paired (t : Nat) (s : State α) : Machine α := setIndex32 (adjusted t s) 4 ((t/2 : Nat) : Int)
def masked (t : Nat) (s : State α) : Machine α := setIndex32 (paired t s) 5 ((t/2*2 : Nat) : Int)
def globalX (t : Nat) (s : State α) : Machine α := setPointer (masked t s) 9 ⟨0, 0, true⟩
def wideX (t : Nat) (s : State α) : Machine α :=
  LarkPtxMatrix.setIndex64 (globalX t s) 10 ((t/2*4 : Nat) : Int)
def xPointer (t : Nat) (s : State α) : Machine α :=
  setPointer (wideX t s) 11 ⟨0, ((t/2*4 : Nat) : Int), true⟩

theorem parameters_execute (ops : Ops α) (t : Nat) (s : State α) :
    Steps ops layout geometry t program (start s) (globalOutput s) :=
  .next (by rfl) (.next (by rfl) (.next (by rfl) (.next (by rfl) (.next (by rfl) (.refl _)))))

theorem index_execute (ops : Ops α) (t : Nat) (s : State α) (ht : t < 32768) :
    Steps ops layout geometry t program (globalOutput s) (indexed t s) := by
  have hb : 0 < geometry.block ∧ t / geometry.block < 4294967296 := by
    simp only [geometry, Nat.div_one]; omega
  have e := blockId_step ops layout geometry t 1 (globalOutput s) hb
  apply one_step
  rw [transition_at ops layout geometry t program (globalOutput s)
    (.base (.base (.blockId 1))) (by rfl) (by rfl)]
  change LarkPtxDot.execute ops layout geometry t (.blockId 1) (globalOutput s) = some (indexed t s)
  simpa only [geometry, Nat.div_one] using e

theorem correction_execute (ops : Ops α) (t : Nat) (s : State α) (ht : t < 32768) :
    Steps ops layout geometry t program (indexed t s) (corrected t s) := by
  have hb : unsigned32 (t : Int) := by unfold unsigned32; omega
  have e := LarkPtxMatrix.unsigned_right_step ops layout geometry t 2 1 31
    (t : Int) (indexed t s) (by rfl) hb
  have hp : (2 : Int)^min 31 32 = 2147483648 := by decide
  have hz : (t : Int) / 2147483648 = 0 := by omega
  rw [hp, hz] at e
  apply one_step
  rw [transition_at ops layout geometry t program (indexed t s)
    (.base (.shiftRightUnsigned32 2 1 31)) (by rfl) (by rfl), base_step]
  exact e

theorem adjustment_execute (ops : Ops α) (t : Nat) (s : State α) (ht : t < 32768) :
    Steps ops layout geometry t program (corrected t s) (adjusted t s) := by
  have hb : signed32 (t : Int) ∧ signed32 0 ∧ signed32 ((t : Int)+0) := by
    unfold signed32; omega
  have e := add32_step ops layout geometry t 3 1 (.reg 2) (corrected t s) (t : Int) 0
    (by rfl) (by rfl) hb
  simp only [Int.add_zero] at e
  apply one_step
  rw [transition_at ops layout geometry t program (corrected t s)
    (.base (.base (.addSigned32 3 1 (.reg 2)))) (by rfl) (by rfl)]
  exact e

theorem pair_execute (ops : Ops α) (t : Nat) (s : State α) (ht : t < 32768) :
    Steps ops layout geometry t program (adjusted t s) (paired t s) := by
  have hb : signed32 (t : Int) := by unfold signed32; omega
  have e := LarkPtxMatrix.signed_right_step ops layout geometry t 4 3 1
    (t : Int) (adjusted t s) (by rfl) hb
  have hp : (2 : Int)^min 1 32 = 2 := by decide
  have he : (t : Int)/2 = ((t/2 : Nat) : Int) := by omega
  rw [hp, he] at e
  apply one_step
  rw [transition_at ops layout geometry t program (adjusted t s)
    (.base (.shiftRightSigned32 4 3 1)) (by rfl) (by rfl), base_step]
  exact e

theorem mask_execute (ops : Ops α) (t : Nat) (s : State α) (ht : t < 32768) :
    Steps ops layout geometry t program (paired t s) (masked t s) := by
  have hb : unsigned32 (t : Int) ∧ signed32 (-2) := by unfold unsigned32 signed32; omega
  have e := LarkPtxMatrix.and_step ops layout geometry t 5 3 (.imm (-2))
    (t : Int) (-2) (paired t s) (by rfl) (by rfl) hb
  have htbits : LarkPtxMatrix.bits32 (t : Int) = t := by
    unfold LarkPtxMatrix.bits32
    have he : (t : Int) % 4294967296 = (t : Int) := by omega
    rw [he]; rfl
  rw [htbits, bits32_negative2, clear_low1 t (by omega)] at e
  apply one_step
  rw [transition_at ops layout geometry t program (paired t s)
    (.base (.andBits32 5 3 (.imm (-2)))) (by rfl) (by rfl), base_step]
  exact e

theorem globalX_execute (ops : Ops α) (t : Nat) (s : State α) :
    Steps ops layout geometry t program (masked t s) (globalX t s) :=
  .next (by rfl) (.refl _)

theorem wideX_execute (ops : Ops α) (t : Nat) (s : State α) (ht : t < 32768) :
    Steps ops layout geometry t program (globalX t s) (wideX t s) := by
  have htdiv : t/2 < 16384 := by omega
  have hb : signed32 ((t/2*2 : Nat) : Int) ∧ signed32 2 ∧
      signed64 (((t/2*2 : Nat) : Int)*2) := by
    unfold signed32 signed64; simp only [Int.natCast_mul]; omega
  have e := wide_step ops layout geometry t 10 5 2 ((t/2*2 : Nat) : Int)
    (globalX t s) (by rfl) hb
  have he : (((t/2*2 : Nat) : Int)*2) = ((t/2*4 : Nat) : Int) := by
    simp only [Int.natCast_mul]; omega
  rw [he] at e
  apply one_step
  rw [transition_at ops layout geometry t program (globalX t s)
    (.base (.base (.mulWideSigned32 10 5 2))) (by rfl) (by rfl)]
  exact e

theorem xPointer_execute (ops : Ops α) (t : Nat) (s : State α) (ht : t < 32768) :
    Steps ops layout geometry t program (wideX t s) (xPointer t s) := by
  have htdiv : t/2 < 16384 := by omega
  have hb : signed64 ((t/2*4 : Nat) : Int) ∧ signed64 (0+((t/2*4 : Nat) : Int)) := by
    unfold signed64; simp only [Int.natCast_mul]; omega
  have e := pointer_add_step ops layout geometry t 11 9 (.reg 10) ⟨0, 0, true⟩
    ((t/2*4 : Nat) : Int) (wideX t s) (by rfl) (by rfl) hb
  simp only [Int.zero_add] at e
  apply one_step
  rw [transition_at ops layout geometry t program (wideX t s)
    (.base (.base (.addSigned64 11 9 (.reg 10)))) (by rfl) (by rfl)]
  exact e

theorem coordinates_execute (ops : Ops α) (t : Nat) (s : State α) (ht : t < 32768) :
    Steps ops layout geometry t program (start s) (xPointer t s) := by
  apply steps_trans _ _ _ _ _ _ _ _ (parameters_execute ops t s)
  apply steps_trans _ _ _ _ _ _ _ _ (index_execute ops t s ht)
  apply steps_trans _ _ _ _ _ _ _ _ (correction_execute ops t s ht)
  apply steps_trans _ _ _ _ _ _ _ _ (adjustment_execute ops t s ht)
  apply steps_trans _ _ _ _ _ _ _ _ (pair_execute ops t s ht)
  apply steps_trans _ _ _ _ _ _ _ _ (mask_execute ops t s ht)
  apply steps_trans _ _ _ _ _ _ _ _ (globalX_execute ops t s)
  exact steps_trans _ _ _ _ _ _ _ _ (wideX_execute ops t s ht) (xPointer_execute ops t s ht)

theorem xPointer_pc (t : Nat) (s : State α) : (xPointer t s).pc = 13 := rfl
theorem xPointer_base (t : Nat) (s : State α) : (xPointer t s).registers.base = s := rfl

theorem instruction_step (ops : Ops α) (t pc : Nat) (s u : Machine α) (i : Instruction)
    (hpc : s.pc = pc) (hs : s.registers.stopped = false)
    (hf : program[pc]? = some i) (he : execute ops layout geometry t i s = some u) :
    Steps ops layout geometry t program s u := by
  apply one_step
  rw [transition_at ops layout geometry t program s i hs (by rw [hpc]; exact hf)]
  exact he

def Reads (input : Nat → Nat → α) (s : State α) : Prop :=
  (∀ i, i < 32768 → s.memory ⟨.global, 0, 0, i⟩ = some (input 0 i)) ∧
  (∀ i, i < 16384 → s.memory ⟨.global, 0, 1, i⟩ = some (input 1 i)) ∧
  (∀ i, i < 16384 → s.memory ⟨.global, 0, 2, i⟩ = some (input 2 i))

def xCell (t j : Nat) : Location := ⟨.global, 0, 0, t/2*2+j⟩
def cosineCell (t : Nat) : Location := ⟨.global, 0, 1, t/2⟩
def sineCell (t : Nat) : Location := ⟨.global, 0, 2, t/2⟩
def outputCell (t : Nat) : Location := ⟨.global, 0, 3, t⟩

theorem x_address (t j : Nat) (ht : t < 32768) (hj : j < 2) :
    address layout geometry t ⟨0, ((t/2*4 : Nat) : Int), true⟩ ((2*j : Nat) : Int) false =
      some (xCell t j) := by
  have hr : t/2 < 16384 := by omega
  have he : ((t/2*4 : Nat) : Int) + ((2*j : Nat) : Int) =
      ((t/2*2+j : Nat) : Int)*2 := by
    simp only [Int.natCast_add, Int.natCast_mul]; omega
  have hs : signed64 (((t/2*2+j : Nat) : Int)*2) := by
    unfold signed64; simp only [Int.natCast_add, Int.natCast_mul]; omega
  have hb : t/2*2+j < 256*128 := by omega
  rw [aligned_address layout geometry t 0 (t/2*2+j) _ _ false he hs]
  exact read_location layout geometry t 0 _ ⟨.input, 256*128⟩ (by rfl) hb

def loadX0 (input : Nat → Nat → α) (t : Nat) (s : State α) : Machine α :=
  loadedHalf (xPointer t s) t 1 (xCell t 0) (input 0 (t/2*2))
def castX0 (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) : Machine α :=
  setFloat (loadX0 input t s) 3 (ops.fromHalf (input 0 (t/2*2)))
def loadX1 (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) : Machine α :=
  loadedHalf (castX0 ops input t s) t 2 (xCell t 1) (input 0 (t/2*2+1))
def castX1 (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) : Machine α :=
  setFloat (loadX1 ops input t s) 4 (ops.fromHalf (input 0 (t/2*2+1)))

theorem input_loads_execute (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α)
    (ht : t < 32768) (hr : Reads input s) :
    Steps ops layout geometry t program (xPointer t s) (castX1 ops input t s) := by
  have hdiv : t/2 < 16384 := by omega
  have ha0 : (xPointer t s).registers.base.memory (xCell t 0) = some (input 0 (t/2*2)) := by
    simpa [xCell, xPointer_base] using hr.1 (t/2*2) (by omega)
  have h0 := instruction_step ops t 13 (xPointer t s) (loadX0 input t s)
    (.base (.base (.loadHalf 1 11 0))) (by rfl) (by rfl) (by rfl)
    (loadHalf_step ops layout geometry t 1 11 0 (xPointer t s)
      ⟨0, ((t/2*4 : Nat) : Int), true⟩ (xCell t 0) (input 0 (t/2*2))
      (by rfl) (by simpa using x_address t 0 ht (by decide)) ha0)
  have h1 := instruction_step ops t 14 (loadX0 input t s) (castX0 ops input t s)
    (.base (.base (.fromHalf 3 1))) (by rfl) (by rfl) (by rfl)
    (fromHalf_step ops layout geometry t 3 1 (loadX0 input t s) _ (by simp [loadX0]))
  have ha1 : (castX0 ops input t s).registers.base.memory (xCell t 1) =
      some (input 0 (t/2*2+1)) := by
    simpa [castX0, loadX0, xCell, xPointer_base] using hr.1 (t/2*2+1) (by omega)
  have h2 := instruction_step ops t 15 (castX0 ops input t s) (loadX1 ops input t s)
    (.base (.base (.loadHalf 2 11 2))) (by rfl) (by rfl) (by rfl)
    (loadHalf_step ops layout geometry t 2 11 2 (castX0 ops input t s)
      ⟨0, ((t/2*4 : Nat) : Int), true⟩ (xCell t 1) (input 0 (t/2*2+1))
      (by simp [castX0, loadX0, xPointer]) (by simpa using x_address t 1 ht (by decide)) ha1)
  have h3 := instruction_step ops t 16 (loadX1 ops input t s) (castX1 ops input t s)
    (.base (.base (.fromHalf 4 2))) (by rfl) (by rfl) (by rfl)
    (fromHalf_step ops layout geometry t 4 2 (loadX1 ops input t s) _ (by simp [loadX1]))
  exact steps_trans _ _ _ _ _ _ _ _ h0
    (steps_trans _ _ _ _ _ _ _ _ h1 (steps_trans _ _ _ _ _ _ _ _ h2 h3))

theorem inputs_execute (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α)
    (ht : t < 32768) (hr : Reads input s) :
    Steps ops layout geometry t program (start s) (castX1 ops input t s) :=
  steps_trans _ _ _ _ _ _ _ _ (coordinates_execute ops t s ht) (input_loads_execute ops input t s ht hr)

theorem inputs_memory (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) :
    (castX1 ops input t s).registers.base.memory = s.memory := rfl

def oddBit (t : Nat) : Bool := t%2 == 1
def evenBit (t : Nat) : Bool := t%2 == 0
def lowBit (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) : Machine α :=
  setIndex32 (castX1 ops input t s) 6 ((t%2 : Nat) : Int)
def compared (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) : Machine α :=
  setPredicate (lowBit ops input t s) 1 (oddBit t)
def literalFalse (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) : Machine α :=
  setPredicate (compared ops input t s) 2 false
def xored (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) : Machine α :=
  setPredicate (literalFalse ops input t s) 3 (oddBit t)
def inverted (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) : Machine α :=
  setPredicate (xored ops input t s) 4 (evenBit t)

theorem lowBit_execute (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α)
    (ht : t < 32768) :
    Steps ops layout geometry t program (castX1 ops input t s) (lowBit ops input t s) := by
  have hb : unsigned32 (t : Int) ∧ signed32 1 := by unfold unsigned32 signed32; omega
  have e := LarkPtxMatrix.and_step ops layout geometry t 6 1 (.imm 1)
    (t : Int) 1 (castX1 ops input t s) (by rfl) (by rfl) hb
  have htbits : LarkPtxMatrix.bits32 (t : Int) = t := by
    unfold LarkPtxMatrix.bits32
    have he : (t : Int) % 4294967296 = (t : Int) := by omega
    rw [he]; simp
  rw [htbits, show LarkPtxMatrix.bits32 1 = 1 by decide, Nat.and_one_is_mod] at e
  exact instruction_step ops t 17 _ _ (.base (.andBits32 6 1 (.imm 1)))
    (by rfl) (by rfl) (by rfl) e

theorem compare_execute (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) :
    Steps ops layout geometry t program (lowBit ops input t s) (compared ops input t s) := by
  have hm : t%2 < 2 := Nat.mod_lt _ (by decide)
  have hb : validBits32 ((t%2 : Nat) : Int) ∧ validBits32 1 := by unfold validBits32; omega
  have e := compare_step ops layout geometry t 1 6 (.imm 1)
    ((t%2 : Nat) : Int) 1 (lowBit ops input t s) (by rfl) (by rfl) hb
  have hbits : LarkPtxMatrix.bits32 ((t%2 : Nat) : Int) = t%2 := by
    unfold LarkPtxMatrix.bits32
    have he : ((t%2 : Nat) : Int) % 4294967296 = ((t%2 : Nat) : Int) := by omega
    rw [he]; rfl
  rw [hbits, show LarkPtxMatrix.bits32 1 = 1 by decide] at e
  exact instruction_step ops t 18 _ _ (.compareEqBits32 1 6 (.imm 1))
    (by rfl) (by rfl) (by rfl) e

theorem literalFalse_execute (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) :
    Steps ops layout geometry t program (compared ops input t s) (literalFalse ops input t s) :=
  .next (by rfl) (.refl _)

theorem xor_execute (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) :
    Steps ops layout geometry t program (literalFalse ops input t s) (xored ops input t s) := by
  have e := predicate_xor_step ops layout geometry t 3 1 2 (oddBit t) false
    (literalFalse ops input t s) (by rfl) (by rfl)
  have he : ((oddBit t) != false) = oddBit t := by cases h : oddBit t <;> rfl
  rw [he] at e
  exact instruction_step ops t 20 _ _ (.predicateXor 3 1 2) (by rfl) (by rfl) (by rfl) e

theorem not_odd_even (t : Nat) : (!(oddBit t)) = evenBit t := by
  rcases Nat.mod_two_eq_zero_or_one t with h | h <;> simp [oddBit, evenBit, h]

theorem invert_execute (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) :
    Steps ops layout geometry t program (xored ops input t s) (inverted ops input t s) := by
  have e := predicate_not_step ops layout geometry t 4 3 (oddBit t)
    (xored ops input t s) (by rfl)
  rw [not_odd_even] at e
  exact instruction_step ops t 21 _ _ (.predicateNot 4 3) (by rfl) (by rfl) (by rfl) e

theorem predicates_execute (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α)
    (ht : t < 32768) :
    Steps ops layout geometry t program (castX1 ops input t s) (inverted ops input t s) := by
  apply steps_trans _ _ _ _ _ _ _ _ (lowBit_execute ops input t s ht)
  apply steps_trans _ _ _ _ _ _ _ _ (compare_execute ops input t s)
  apply steps_trans _ _ _ _ _ _ _ _ (literalFalse_execute ops input t s)
  exact steps_trans _ _ _ _ _ _ _ _ (xor_execute ops input t s) (invert_execute ops input t s)

theorem inverted_memory (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) :
    (inverted ops input t s).registers.base.memory = s.memory := rfl

def globalSine (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) : Machine α :=
  setPointer (inverted ops input t s) 12 ⟨2, 0, true⟩
def coefficientWide (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) : Machine α :=
  LarkPtxMatrix.setIndex64 (globalSine ops input t s) 13 ((t/2*2 : Nat) : Int)
def sinePointer (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) : Machine α :=
  setPointer (coefficientWide ops input t s) 1 ⟨2, ((t/2*2 : Nat) : Int), true⟩
def globalCosine (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) : Machine α :=
  setPointer (sinePointer ops input t s) 14 ⟨1, 0, true⟩
def cosinePointer (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) : Machine α :=
  setPointer (globalCosine ops input t s) 2 ⟨1, ((t/2*2 : Nat) : Int), true⟩
def outputWide (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) : Machine α :=
  LarkPtxMatrix.setIndex64 (cosinePointer ops input t s) 15 ((t*2 : Nat) : Int)
def ready (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) : Machine α :=
  setPointer (outputWide ops input t s) 3 ⟨3, ((t*2 : Nat) : Int), true⟩

theorem globalSine_execute (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) :
    Steps ops layout geometry t program (inverted ops input t s) (globalSine ops input t s) :=
  .next (by rfl) (.refl _)

theorem coefficientWide_execute (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α)
    (ht : t < 32768) :
    Steps ops layout geometry t program (globalSine ops input t s) (coefficientWide ops input t s) := by
  have hr : t/2 < 16384 := by omega
  have hb : signed32 ((t/2 : Nat) : Int) ∧ signed32 2 ∧ signed64 (((t/2 : Nat) : Int)*2) := by
    unfold signed32 signed64; omega
  have e := wide_step ops layout geometry t 13 4 2 ((t/2 : Nat) : Int)
    (globalSine ops input t s) (by rfl) hb
  have he : (((t/2 : Nat) : Int)*2) = ((t/2*2 : Nat) : Int) := by simp
  rw [he] at e
  exact instruction_step ops t 23 _ _ (.base (.base (.mulWideSigned32 13 4 2)))
    (by rfl) (by rfl) (by rfl) e

theorem sinePointer_execute (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α)
    (ht : t < 32768) :
    Steps ops layout geometry t program (coefficientWide ops input t s) (sinePointer ops input t s) := by
  have hr : t/2 < 16384 := by omega
  have hb : signed64 ((t/2*2 : Nat) : Int) ∧ signed64 (0+((t/2*2 : Nat) : Int)) := by
    unfold signed64; simp only [Int.natCast_mul]; omega
  have e := pointer_add_step ops layout geometry t 1 12 (.reg 13) ⟨2, 0, true⟩
    ((t/2*2 : Nat) : Int) (coefficientWide ops input t s) (by rfl) (by rfl) hb
  simp only [Int.zero_add] at e
  exact instruction_step ops t 24 _ _ (.base (.base (.addSigned64 1 12 (.reg 13))))
    (by rfl) (by rfl) (by rfl) e

theorem globalCosine_execute (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) :
    Steps ops layout geometry t program (sinePointer ops input t s) (globalCosine ops input t s) :=
  .next (by rfl) (.refl _)

theorem cosinePointer_execute (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α)
    (ht : t < 32768) :
    Steps ops layout geometry t program (globalCosine ops input t s) (cosinePointer ops input t s) := by
  have hr : t/2 < 16384 := by omega
  have hb : signed64 ((t/2*2 : Nat) : Int) ∧ signed64 (0+((t/2*2 : Nat) : Int)) := by
    unfold signed64; simp only [Int.natCast_mul]; omega
  have e := pointer_add_step ops layout geometry t 2 14 (.reg 13) ⟨1, 0, true⟩
    ((t/2*2 : Nat) : Int) (globalCosine ops input t s) (by rfl) (by rfl) hb
  simp only [Int.zero_add] at e
  exact instruction_step ops t 26 _ _ (.base (.base (.addSigned64 2 14 (.reg 13))))
    (by rfl) (by rfl) (by rfl) e

theorem outputWide_execute (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α)
    (ht : t < 32768) :
    Steps ops layout geometry t program (cosinePointer ops input t s) (outputWide ops input t s) := by
  have hb : signed32 (t : Int) ∧ signed32 2 ∧ signed64 ((t : Int)*2) := by
    unfold signed32 signed64; omega
  have e := wide_step ops layout geometry t 15 1 2 (t : Int)
    (cosinePointer ops input t s) (by rfl) hb
  have he : (t : Int)*2 = ((t*2 : Nat) : Int) := by simp
  rw [he] at e
  exact instruction_step ops t 27 _ _ (.base (.base (.mulWideSigned32 15 1 2)))
    (by rfl) (by rfl) (by rfl) e

theorem outputPointer_execute (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α)
    (ht : t < 32768) :
    Steps ops layout geometry t program (outputWide ops input t s) (ready ops input t s) := by
  have hb : signed64 ((t*2 : Nat) : Int) ∧ signed64 (0+((t*2 : Nat) : Int)) := by
    unfold signed64; simp only [Int.natCast_mul]; omega
  have e := pointer_add_step ops layout geometry t 3 8 (.reg 15) ⟨3, 0, true⟩
    ((t*2 : Nat) : Int) (outputWide ops input t s) (by rfl) (by rfl) hb
  simp only [Int.zero_add] at e
  exact instruction_step ops t 28 _ _ (.base (.base (.addSigned64 3 8 (.reg 15))))
    (by rfl) (by rfl) (by rfl) e

theorem pointers_execute (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α)
    (ht : t < 32768) :
    Steps ops layout geometry t program (inverted ops input t s) (ready ops input t s) := by
  apply steps_trans _ _ _ _ _ _ _ _ (globalSine_execute ops input t s)
  apply steps_trans _ _ _ _ _ _ _ _ (coefficientWide_execute ops input t s ht)
  apply steps_trans _ _ _ _ _ _ _ _ (sinePointer_execute ops input t s ht)
  apply steps_trans _ _ _ _ _ _ _ _ (globalCosine_execute ops input t s)
  apply steps_trans _ _ _ _ _ _ _ _ (cosinePointer_execute ops input t s ht)
  exact steps_trans _ _ _ _ _ _ _ _ (outputWide_execute ops input t s ht) (outputPointer_execute ops input t s ht)

theorem ready_execute (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α)
    (ht : t < 32768) (hr : Reads input s) :
    Steps ops layout geometry t program (start s) (ready ops input t s) := by
  apply steps_trans _ _ _ _ _ _ _ _ (inputs_execute ops input t s ht hr)
  exact steps_trans _ _ _ _ _ _ _ _ (predicates_execute ops input t s ht) (pointers_execute ops input t s ht)

theorem ready_memory (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) :
    (ready ops input t s).registers.base.memory = s.memory := rfl
theorem ready_pc (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) :
    (ready ops input t s).pc = 29 := rfl
theorem ready_x0 (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) :
    (ready ops input t s).registers.scalar 3 = some (ops.fromHalf (input 0 (t/2*2))) := rfl
theorem ready_x1 (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) :
    (ready ops input t s).registers.scalar 4 = some (ops.fromHalf (input 0 (t/2*2+1))) := rfl
theorem ready_predicate (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) :
    (ready ops input t s).predicates 4 = some (evenBit t) := rfl

def branchStart (even : Bool) : Nat := if even then 31 else 41
def firstBuffer (even : Bool) : Nat := if even then 1 else 2
def secondBuffer (even : Bool) : Nat := if even then 2 else 1
def firstPointer (even : Bool) : Nat := if even then 2 else 1
def secondPointer (even : Bool) : Nat := if even then 1 else 2
def firstHalf (even : Bool) : Nat := if even then 6 else 3
def secondHalf (even : Bool) : Nat := if even then 7 else 4
def outputHalf (even : Bool) : Nat := if even then 8 else 5
def firstFloat (even : Bool) : Nat := if even then 10 else 5
def secondFloat (even : Bool) : Nat := if even then 11 else 6
def firstProduct (even : Bool) : Nat := if even then 13 else 8
def secondProduct (even : Bool) : Nat := if even then 14 else 9
def resultFloat (even : Bool) : Nat := if even then 12 else 7
def combineOperator (even : Bool) : Binary := if even then .sub else .add
def coefficientCell (t b : Nat) : Location := ⟨.global, 0, b, t/2⟩

def branchBody (even : Bool) : List Instruction :=
  [.base (.base (.loadHalf (firstHalf even) (firstPointer even) 0)),
   .base (.base (.fromHalf (firstFloat even) (firstHalf even))),
   .base (.base (.binaryFloat (firstProduct even) .mul 3 (firstFloat even))),
   .base (.base (.loadHalf (secondHalf even) (secondPointer even) 0)),
   .base (.base (.fromHalf (secondFloat even) (secondHalf even))),
   .base (.base (.binaryFloat (secondProduct even) .mul 4 (secondFloat even))),
   .base (.base (.binaryFloat (resultFloat even) (combineOperator even) (firstProduct even) (secondProduct even))),
   .base (.base (.toHalf (outputHalf even) (resultFloat even))),
   .base (.base (.storeHalf 3 0 (outputHalf even)))]

theorem program_branchBody : ∀ (even : Bool) (q : Fin 9),
    program[branchStart even+q.val]? = (branchBody even)[q.val]? := by decide

theorem branch_body_step (ops : Ops α) (t q : Nat) (even : Bool) (s u : Machine α)
    (i : Instruction) (hq : q < 9) (hpc : s.pc = branchStart even+q)
    (hs : s.registers.stopped = false) (hi : (branchBody even)[q]? = some i)
    (he : execute ops layout geometry t i s = some u) :
    Steps ops layout geometry t program s u := by
  have hf := program_branchBody even ⟨q, hq⟩
  rw [hi] at hf
  exact instruction_step ops t (branchStart even+q) s u i hpc hs hf he

theorem coefficient_address (t b : Nat) (ht : t < 32768) (hb : b = 1 ∨ b = 2) :
    address layout geometry t ⟨b, ((t/2*2 : Nat) : Int), true⟩ 0 false =
      some (coefficientCell t b) := by
  have hr : t/2 < 16384 := by omega
  have he : ((t/2*2 : Nat) : Int)+0 = ((t/2 : Nat) : Int)*2 := by simp
  have hs : signed64 (((t/2 : Nat) : Int)*2) := by unfold signed64; omega
  rw [aligned_address layout geometry t b (t/2) _ 0 false he hs]
  apply read_location layout geometry t b (t/2) ⟨.input, 16384⟩ _ hr
  rcases hb with rfl | rfl <;> rfl

theorem output_address (t : Nat) (ht : t < 32768) :
    address layout geometry t ⟨3, ((t*2 : Nat) : Int), true⟩ 0 true = some (outputCell t) := by
  have he : ((t*2 : Nat) : Int)+0 = (t : Int)*2 := by simp
  have hs : signed64 ((t : Int)*2) := by unfold signed64; omega
  rw [aligned_address layout geometry t 3 t _ 0 true he hs]
  have hr : (Role.output == Role.input) = false := by decide
  simp [location, layout, outputCell, ht, hr]

def entered (even : Bool) (s : Machine α) : Machine α := { s with pc := branchStart even }

theorem branch_execute (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) :
    Steps ops layout geometry t program (ready ops input t s)
      (entered (evenBit t) (ready ops input t s)) := by
  cases h : evenBit t with
  | false =>
      have h0 : Steps ops layout geometry t program (ready ops input t s)
          { ready ops input t s with pc := 30 } := by
        apply instruction_step ops t 29 _ _ (.base (.base (.branch 4 31))) (by rfl) (by rfl) (by rfl)
        change LarkPtxDot.execute ops layout geometry t (.branch 4 31) _ = _
        simp [LarkPtxDot.execute, ready_predicate, h, ready_pc]
      have h1 : Steps ops layout geometry t program { ready ops input t s with pc := 30 }
          (entered false (ready ops input t s)) :=
        instruction_step ops t 30 _ _ (.branchAlways 41) (by rfl) (by rfl) (by rfl) (by rfl)
      exact steps_trans _ _ _ _ _ _ _ _ h0 h1
  | true =>
      apply instruction_step ops t 29 _ _ (.base (.base (.branch 4 31))) (by rfl) (by rfl) (by rfl)
      change LarkPtxDot.execute ops layout geometry t (.branch 4 31) _ = _
      simp [LarkPtxDot.execute, ready_predicate, h, entered, branchStart]

def firstCoefficient (input : Nat → Nat → α) (t : Nat) (even : Bool) : α :=
  input (firstBuffer even) (t/2)
def secondCoefficient (input : Nat → Nat → α) (t : Nat) (even : Bool) : α :=
  input (secondBuffer even) (t/2)
def firstTerm (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (even : Bool) : α :=
  ops.mul (ops.fromHalf (input 0 (t/2*2))) (ops.fromHalf (firstCoefficient input t even))
def secondTerm (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (even : Bool) : α :=
  ops.mul (ops.fromHalf (input 0 (t/2*2+1))) (ops.fromHalf (secondCoefficient input t even))
def combinedValue (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (even : Bool) : α :=
  applyBinary ops (combineOperator even) (firstTerm ops input t even) (secondTerm ops input t even)
def branchValue (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (even : Bool) : α :=
  ops.toHalf (combinedValue ops input t even)

def bodyLoad0 (input : Nat → Nat → α) (t : Nat) (even : Bool) (s : Machine α) : Machine α :=
  loadedHalf s t (firstHalf even) (coefficientCell t (firstBuffer even)) (firstCoefficient input t even)
def bodyCast0 (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (even : Bool) (s : Machine α) : Machine α :=
  setFloat (bodyLoad0 input t even s) (firstFloat even) (ops.fromHalf (firstCoefficient input t even))
def bodyMul0 (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (even : Bool) (s : Machine α) : Machine α :=
  setFloat (bodyCast0 ops input t even s) (firstProduct even) (firstTerm ops input t even)
def bodyLoad1 (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (even : Bool) (s : Machine α) : Machine α :=
  loadedHalf (bodyMul0 ops input t even s) t (secondHalf even)
    (coefficientCell t (secondBuffer even)) (secondCoefficient input t even)
def bodyCast1 (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (even : Bool) (s : Machine α) : Machine α :=
  setFloat (bodyLoad1 ops input t even s) (secondFloat even) (ops.fromHalf (secondCoefficient input t even))
def bodyMul1 (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (even : Bool) (s : Machine α) : Machine α :=
  setFloat (bodyCast1 ops input t even s) (secondProduct even) (secondTerm ops input t even)
def bodyCombined (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (even : Bool) (s : Machine α) : Machine α :=
  setFloat (bodyMul1 ops input t even s) (resultFloat even) (combinedValue ops input t even)
def bodyHalf (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (even : Bool) (s : Machine α) : Machine α :=
  setHalf (bodyCombined ops input t even s) (outputHalf even) (branchValue ops input t even)
def bodyStored (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (even : Bool) (s : Machine α) : Machine α :=
  storedHalf (bodyHalf ops input t even s) t (outputCell t) (branchValue ops input t even)

theorem bodyStored_pc (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (even : Bool) (s : Machine α) :
    (bodyStored ops input t even s).pc = s.pc+9 := by
  simp [bodyStored, storedHalf, bodyHalf, setHalf, LarkPtxDot.advance, bodyCombined, bodyMul1,
    bodyCast1, bodyLoad1, bodyMul0, bodyCast0, bodyLoad0, Nat.add_assoc]

theorem bodyStored_memory (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (even : Bool) (s : Machine α) :
    (bodyStored ops input t even s).registers.base.memory =
      fun l => if l = outputCell t then some (branchValue ops input t even) else s.registers.base.memory l := rfl

theorem branch_body_execute (ops : Ops α) (input : Nat → Nat → α) (t : Nat)
    (even : Bool) (s : Machine α) (ht : t < 32768)
    (hpc : s.pc = branchStart even) (hs : s.registers.stopped = false)
    (hp0 : s.registers.pointer (firstPointer even) = some ⟨firstBuffer even, ((t/2*2 : Nat) : Int), true⟩)
    (hp1 : s.registers.pointer (secondPointer even) = some ⟨secondBuffer even, ((t/2*2 : Nat) : Int), true⟩)
    (hpo : s.registers.pointer 3 = some ⟨3, ((t*2 : Nat) : Int), true⟩)
    (hx0 : s.registers.scalar 3 = some (ops.fromHalf (input 0 (t/2*2))))
    (hx1 : s.registers.scalar 4 = some (ops.fromHalf (input 0 (t/2*2+1))))
    (hm0 : s.registers.base.memory (coefficientCell t (firstBuffer even)) = some (firstCoefficient input t even))
    (hm1 : s.registers.base.memory (coefficientCell t (secondBuffer even)) = some (secondCoefficient input t even)) :
    Steps ops layout geometry t program s (bodyStored ops input t even s) := by
  have h0 := branch_body_step ops t 0 even s (bodyLoad0 input t even s)
    (.base (.base (.loadHalf (firstHalf even) (firstPointer even) 0))) (by decide)
    (by simpa only [Nat.add_zero] using hpc) hs (by rfl)
    (loadHalf_step ops layout geometry t (firstHalf even) (firstPointer even) 0 s
      ⟨firstBuffer even, ((t/2*2 : Nat) : Int), true⟩ (coefficientCell t (firstBuffer even))
      (firstCoefficient input t even) hp0
      (coefficient_address t (firstBuffer even) ht (by cases even <;> simp [firstBuffer])) hm0)
  have h1 := branch_body_step ops t 1 even (bodyLoad0 input t even s) (bodyCast0 ops input t even s)
    (.base (.base (.fromHalf (firstFloat even) (firstHalf even)))) (by decide)
    (by simp [bodyLoad0, hpc]) (by simp [bodyLoad0, hs]) (by rfl)
    (fromHalf_step ops layout geometry t (firstFloat even) (firstHalf even)
      (bodyLoad0 input t even s) (firstCoefficient input t even) (by simp [bodyLoad0]))
  have h2 := branch_body_step ops t 2 even (bodyCast0 ops input t even s) (bodyMul0 ops input t even s)
    (.base (.base (.binaryFloat (firstProduct even) .mul 3 (firstFloat even)))) (by decide)
    (by simp [bodyCast0, bodyLoad0, hpc, Nat.add_assoc])
    (by simp [bodyCast0, bodyLoad0, hs]) (by rfl)
    (binaryFloat_step ops layout geometry t (firstProduct even) 3 (firstFloat even) .mul
      (bodyCast0 ops input t even s) _ _
      (by cases even <;> simp [bodyCast0, bodyLoad0, firstFloat, hx0])
      (by simp [bodyCast0]))
  have h3 := branch_body_step ops t 3 even (bodyMul0 ops input t even s) (bodyLoad1 ops input t even s)
    (.base (.base (.loadHalf (secondHalf even) (secondPointer even) 0))) (by decide)
    (by simp [bodyMul0, bodyCast0, bodyLoad0, hpc, Nat.add_assoc])
    (by simp [bodyMul0, bodyCast0, bodyLoad0, hs]) (by rfl)
    (loadHalf_step ops layout geometry t (secondHalf even) (secondPointer even) 0
      (bodyMul0 ops input t even s) ⟨secondBuffer even, ((t/2*2 : Nat) : Int), true⟩
      (coefficientCell t (secondBuffer even)) (secondCoefficient input t even)
      (by simp [bodyMul0, bodyCast0, bodyLoad0, hp1])
      (coefficient_address t (secondBuffer even) ht (by cases even <;> simp [secondBuffer]))
      (by simp [bodyMul0, bodyCast0, bodyLoad0, hm1]))
  have h4 := branch_body_step ops t 4 even (bodyLoad1 ops input t even s) (bodyCast1 ops input t even s)
    (.base (.base (.fromHalf (secondFloat even) (secondHalf even)))) (by decide)
    (by simp [bodyLoad1, bodyMul0, bodyCast0, bodyLoad0, hpc, Nat.add_assoc])
    (by simp [bodyLoad1, bodyMul0, bodyCast0, bodyLoad0, hs]) (by rfl)
    (fromHalf_step ops layout geometry t (secondFloat even) (secondHalf even)
      (bodyLoad1 ops input t even s) (secondCoefficient input t even) (by simp [bodyLoad1]))
  have h5 := branch_body_step ops t 5 even (bodyCast1 ops input t even s) (bodyMul1 ops input t even s)
    (.base (.base (.binaryFloat (secondProduct even) .mul 4 (secondFloat even)))) (by decide)
    (by simp [bodyCast1, bodyLoad1, bodyMul0, bodyCast0, bodyLoad0, hpc, Nat.add_assoc])
    (by simp [bodyCast1, bodyLoad1, bodyMul0, bodyCast0, bodyLoad0, hs]) (by rfl)
    (binaryFloat_step ops layout geometry t (secondProduct even) 4 (secondFloat even) .mul
      (bodyCast1 ops input t even s) _ _
      (by cases even <;> simp [bodyCast1, bodyLoad1, bodyMul0, bodyCast0, bodyLoad0,
          secondFloat, firstProduct, firstFloat, hx1])
      (by simp [bodyCast1]))
  have h6 := branch_body_step ops t 6 even (bodyMul1 ops input t even s) (bodyCombined ops input t even s)
    (.base (.base (.binaryFloat (resultFloat even) (combineOperator even) (firstProduct even) (secondProduct even))))
    (by decide)
    (by simp [bodyMul1, bodyCast1, bodyLoad1, bodyMul0, bodyCast0, bodyLoad0, hpc, Nat.add_assoc])
    (by simp [bodyMul1, bodyCast1, bodyLoad1, bodyMul0, bodyCast0, bodyLoad0, hs]) (by rfl)
    (binaryFloat_step ops layout geometry t (resultFloat even) (firstProduct even) (secondProduct even)
      (combineOperator even) (bodyMul1 ops input t even s) _ _
      (by cases even <;> simp [bodyMul1, bodyCast1, bodyLoad1, bodyMul0,
          firstProduct, secondProduct, secondFloat])
      (by simp [bodyMul1]))
  have h7 := branch_body_step ops t 7 even (bodyCombined ops input t even s) (bodyHalf ops input t even s)
    (.base (.base (.toHalf (outputHalf even) (resultFloat even)))) (by decide)
    (by simp [bodyCombined, bodyMul1, bodyCast1, bodyLoad1, bodyMul0, bodyCast0, bodyLoad0, hpc, Nat.add_assoc])
    (by simp [bodyCombined, bodyMul1, bodyCast1, bodyLoad1, bodyMul0, bodyCast0, bodyLoad0, hs]) (by rfl)
    (half_step ops layout geometry t (outputHalf even) (resultFloat even)
      (bodyCombined ops input t even s) (combinedValue ops input t even) (by simp [bodyCombined]))
  have h8 := branch_body_step ops t 8 even (bodyHalf ops input t even s) (bodyStored ops input t even s)
    (.base (.base (.storeHalf 3 0 (outputHalf even)))) (by decide)
    (by simp [bodyHalf, setHalf, LarkPtxDot.advance, bodyCombined, bodyMul1, bodyCast1, bodyLoad1,
      bodyMul0, bodyCast0, bodyLoad0, hpc, Nat.add_assoc])
    (by change s.registers.stopped = false; exact hs) (by rfl)
    (store_step ops layout geometry t 3 (outputHalf even) 0 (bodyHalf ops input t even s)
      ⟨3, ((t*2 : Nat) : Int), true⟩ (outputCell t) (branchValue ops input t even)
      (by change (bodyCombined ops input t even s).registers.pointer 3 = _
          simp [bodyCombined, bodyMul1, bodyCast1, bodyLoad1, bodyMul0, bodyCast0, bodyLoad0, hpo])
      (output_address t ht) (by cases even <;> rfl))
  exact steps_trans _ _ _ _ _ _ _ _ h0 (steps_trans _ _ _ _ _ _ _ _ h1
    (steps_trans _ _ _ _ _ _ _ _ h2 (steps_trans _ _ _ _ _ _ _ _ h3
      (steps_trans _ _ _ _ _ _ _ _ h4 (steps_trans _ _ _ _ _ _ _ _ h5
        (steps_trans _ _ _ _ _ _ _ _ h6 (steps_trans _ _ _ _ _ _ _ _ h7 h8)))))))

def branchReturned (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (even : Bool) (s : Machine α) : Machine α :=
  returned (if even then { bodyStored ops input t even s with pc := 50 } else bodyStored ops input t even s)

theorem branch_tail_execute (ops : Ops α) (input : Nat → Nat → α) (t : Nat)
    (even : Bool) (s : Machine α) (hpc : s.pc = branchStart even) (hs : s.registers.stopped = false) :
    Steps ops layout geometry t program (bodyStored ops input t even s) (branchReturned ops input t even s) := by
  have hstop : (bodyStored ops input t even s).registers.stopped = false := by
    change s.registers.stopped = false
    exact hs
  cases even with
  | false =>
      have hc : (bodyStored ops input t false s).pc = 50 := by rw [bodyStored_pc, hpc]; rfl
      exact instruction_step ops t 50 _ _ (.base (.base .ret)) hc hstop (by rfl)
        (return_step ops layout geometry t _)
  | true =>
      have hc : (bodyStored ops input t true s).pc = 40 := by rw [bodyStored_pc, hpc]; rfl
      have h0 : Steps ops layout geometry t program (bodyStored ops input t true s)
          { bodyStored ops input t true s with pc := 50 } :=
        instruction_step ops t 40 _ _ (.branchAlways 50) hc hstop (by rfl) (by rfl)
      have h1 : Steps ops layout geometry t program { bodyStored ops input t true s with pc := 50 }
          (branchReturned ops input t true s) :=
        instruction_step ops t 50 _ _ (.base (.base .ret)) (by rfl) hstop (by rfl)
          (return_step ops layout geometry t _)
      exact steps_trans _ _ _ _ _ _ _ _ h0 h1

theorem branchReturned_stopped (ops : Ops α) (input : Nat → Nat → α) (t : Nat)
    (even : Bool) (s : Machine α) : (branchReturned ops input t even s).registers.stopped = true := rfl

theorem branchReturned_memory (ops : Ops α) (input : Nat → Nat → α) (t : Nat)
    (even : Bool) (s : Machine α) :
    (branchReturned ops input t even s).registers.base.memory =
      fun l => if l = outputCell t then some (branchValue ops input t even) else s.registers.base.memory l := by
  cases even <;> rfl

theorem branchReturned_trace (ops : Ops α) (input : Nat → Nat → α) (t : Nat)
    (even : Bool) (s : Machine α) :
    (branchReturned ops input t even s).registers.base.trace =
      ⟨t, outputCell t, true, s.registers.base.epochs t⟩ ::
      ⟨t, coefficientCell t (secondBuffer even), false, s.registers.base.epochs t⟩ ::
      ⟨t, coefficientCell t (firstBuffer even), false, s.registers.base.epochs t⟩ :: s.registers.base.trace := by
  cases even <;> rfl

def laneResult (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) : Machine α :=
  branchReturned ops input t (evenBit t) (entered (evenBit t) (ready ops input t s))

theorem source_lane (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α)
    (ht : t < 32768) (hr : Reads input s) :
    Steps ops layout geometry t program (start s) (laneResult ops input t s) ∧
      (laneResult ops input t s).registers.stopped = true := by
  have hdiv : t/2 < 16384 := by omega
  have h0 := ready_execute ops input t s ht hr
  have h1 := branch_execute ops input t s
  have hbody := branch_body_execute ops input t (evenBit t) (entered (evenBit t) (ready ops input t s))
    ht (by rfl) (by rfl)
    (by cases h : evenBit t <;> rfl)
    (by cases h : evenBit t <;> rfl)
    (by rfl) (by rfl) (by rfl)
    (by
      cases h : evenBit t with
      | false =>
          change s.memory ⟨.global, 0, 2, t/2⟩ = some (input 2 (t/2))
          exact hr.2.2 (t/2) hdiv
      | true =>
          change s.memory ⟨.global, 0, 1, t/2⟩ = some (input 1 (t/2))
          exact hr.2.1 (t/2) hdiv)
    (by
      cases h : evenBit t with
      | false =>
          change s.memory ⟨.global, 0, 1, t/2⟩ = some (input 1 (t/2))
          exact hr.2.1 (t/2) hdiv
      | true =>
          change s.memory ⟨.global, 0, 2, t/2⟩ = some (input 2 (t/2))
          exact hr.2.2 (t/2) hdiv)
  have htail := branch_tail_execute ops input t (evenBit t)
    (entered (evenBit t) (ready ops input t s)) (by rfl) (by rfl)
  exact ⟨steps_trans _ _ _ _ _ _ _ _ h0 (steps_trans _ _ _ _ _ _ _ _ h1
    (steps_trans _ _ _ _ _ _ _ _ hbody htail)), branchReturned_stopped ops input t _ _⟩

theorem laneResult_memory (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) :
    (laneResult ops input t s).registers.base.memory =
      fun l => if l = outputCell t then some (branchValue ops input t (evenBit t)) else s.memory l := by
  unfold laneResult
  rw [branchReturned_memory]
  rfl

theorem laneResult_trace (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) :
    (laneResult ops input t s).registers.base.trace =
      ⟨t, outputCell t, true, s.epochs t⟩ ::
      ⟨t, coefficientCell t (secondBuffer (evenBit t)), false, s.epochs t⟩ ::
      ⟨t, coefficientCell t (firstBuffer (evenBit t)), false, s.epochs t⟩ ::
      ⟨t, xCell t 1, false, s.epochs t⟩ :: ⟨t, xCell t 0, false, s.epochs t⟩ :: s.trace := by
  unfold laneResult
  rw [branchReturned_trace]
  rfl

def reference (ops : Ops α) (input : Nat → Nat → α) (t : Nat) : α :=
  if t%2 = 0 then
    ops.toHalf (ops.sub
      (ops.mul (ops.fromHalf (input 0 (t/2*2))) (ops.fromHalf (input 1 (t/2))))
      (ops.mul (ops.fromHalf (input 0 (t/2*2+1))) (ops.fromHalf (input 2 (t/2)))))
  else
    ops.toHalf (ops.add
      (ops.mul (ops.fromHalf (input 0 (t/2*2))) (ops.fromHalf (input 2 (t/2))))
      (ops.mul (ops.fromHalf (input 0 (t/2*2+1))) (ops.fromHalf (input 1 (t/2)))))

theorem branchValue_reference (ops : Ops α) (input : Nat → Nat → α) (t : Nat) :
    branchValue ops input t (evenBit t) = reference ops input t := by
  by_cases h : t%2 = 0 <;>
    simp [reference, branchValue, combinedValue, evenBit, h, combineOperator, applyBinary,
      firstTerm, secondTerm, firstCoefficient, secondCoefficient, firstBuffer, secondBuffer]

theorem laneResult_reference (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) :
    (laneResult ops input t s).registers.base.memory =
      fun l => if l = outputCell t then some (reference ops input t) else s.memory l := by
  rw [laneResult_memory, branchValue_reference]

def afterLane (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) : State α :=
  (laneResult ops input t s).registers.base

theorem afterLane_memory (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) :
    (afterLane ops input t s).memory =
      fun l => if l = outputCell t then some (reference ops input t) else s.memory l :=
  laneResult_reference ops input t s

theorem afterLane_reads (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α)
    (h : Reads input s) : Reads input (afterLane ops input t s) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    rw [afterLane_memory]
    simpa [outputCell] using h.1 i hi
  · intro i hi
    rw [afterLane_memory]
    simpa [outputCell] using h.2.1 i hi
  · intro i hi
    rw [afterLane_memory]
    simpa [outputCell] using h.2.2 i hi

inductive LaneSequence (ops : Ops α) (p : List Instruction) : Nat → Nat → State α → State α → Prop where
  | nil (k : Nat) (s : State α) : LaneSequence ops p k 0 s s
  | next {k r : Nat} {s final : State α} {m : Machine α} :
      Steps ops layout geometry k p (start s) m →
      m.registers.stopped = true →
      LaneSequence ops p (k+1) r m.registers.base final →
      LaneSequence ops p k (r+1) s final

def runLanes (ops : Ops α) (input : Nat → Nat → α) : Nat → Nat → State α → State α
  | _, 0, s => s
  | k, r+1, s => runLanes ops input (k+1) r (afterLane ops input k s)

theorem runLanes_execute (ops : Ops α) (input : Nat → Nat → α) (k r : Nat) (s : State α)
    (hcount : k+r ≤ 32768) (hr : Reads input s) :
    LaneSequence ops program k r s (runLanes ops input k r s) := by
  induction r generalizing k s with
  | zero => exact .nil k s
  | succ r ih =>
      have lane := source_lane ops input k s (by omega) hr
      have rest := ih (k+1) (afterLane ops input k s) (by omega) (afterLane_reads ops input k s hr)
      exact .next lane.1 lane.2 rest

theorem runLanes_output_memory (ops : Ops α) (input : Nat → Nat → α) (k r i : Nat) (s : State α) :
    (runLanes ops input k r s).memory (outputCell i) =
      if k ≤ i ∧ i < k+r then some (reference ops input i) else s.memory (outputCell i) := by
  induction r generalizing k s with
  | zero =>
      have hn : ¬ (k ≤ i ∧ i < k) := by omega
      simp [runLanes, hn]
  | succ r ih =>
      rw [runLanes, ih]
      by_cases hi : i = k
      · subst i
        have hrest : ¬ (k+1 ≤ k ∧ k < k+1+r) := by omega
        have hwhole : k ≤ k ∧ k < k+(r+1) := by omega
        simp [afterLane_memory, hrest, hwhole]
      · have hloc : outputCell i ≠ outputCell k := by
          intro he
          exact hi (congrArg Location.offset he)
        have hrange : (k+1 ≤ i ∧ i < k+1+r) ↔ (k ≤ i ∧ i < k+(r+1)) := by omega
        rw [afterLane_memory]
        simp only [hloc, if_false, hrange]

theorem runLanes_other_memory (ops : Ops α) (input : Nat → Nat → α) (k r : Nat) (s : State α)
    (l : Location) (h : ∀ i, k ≤ i → i < k+r → l ≠ outputCell i) :
    (runLanes ops input k r s).memory l = s.memory l := by
  induction r generalizing k s with
  | zero => rfl
  | succ r ih =>
      have htail : ∀ i, k+1 ≤ i → i < k+1+r → l ≠ outputCell i := by
        intro i hi hj
        exact h i (by omega) (by omega)
      rw [runLanes, ih (k+1) (afterLane ops input k s) htail, afterLane_memory]
      simp only [if_neg (h k (by omega) (by omega))]

theorem runLanes_output_inside (ops : Ops α) (input : Nat → Nat → α) (k r i : Nat) (s : State α)
    (hi : k ≤ i ∧ i < k+r) :
    (runLanes ops input k r s).memory (outputCell i) = some (reference ops input i) := by
  rw [runLanes_output_memory]
  exact if_pos hi

theorem initial_reads (input : Nat → Nat → α) (outside : Location → Option α) :
    Reads input (initial layout input outside) := by
  refine ⟨?_, ?_, ?_⟩ <;> intro i hi <;> simp [initial, layout, hi]

def AccessSafe (a : Access) : Prop :=
  if a.write then a.location = outputCell a.thread
  else a.location.space = .global ∧ a.location.owner = 0 ∧ a.location.buffer < 3
def TraceSafe (trace : List Access) : Prop := ∀ a ∈ trace, AccessSafe a

theorem afterLane_trace_safe (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α)
    (h : TraceSafe s.trace) : TraceSafe (afterLane ops input t s).trace := by
  intro access ha
  change access ∈ (laneResult ops input t s).registers.base.trace at ha
  rw [laneResult_trace] at ha
  simp only [List.mem_cons] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | ha
  · rfl
  · cases evenBit t <;> simp [AccessSafe, coefficientCell, secondBuffer]
  · cases evenBit t <;> simp [AccessSafe, coefficientCell, firstBuffer]
  · simp [AccessSafe, xCell]
  · simp [AccessSafe, xCell]
  · exact h access ha

theorem runLanes_trace_safe (ops : Ops α) (input : Nat → Nat → α) (k r : Nat) (s : State α)
    (h : TraceSafe s.trace) : TraceSafe (runLanes ops input k r s).trace := by
  induction r generalizing k s with
  | zero => exact h
  | succ r ih => exact ih (k+1) (afterLane ops input k s) (afterLane_trace_safe ops input k s h)

theorem trace_safe_raceFree (g : Geometry) (trace : List Access) (h : TraceSafe trace) :
    raceFree g trace = true := by
  apply List.all_eq_true.mpr
  intro a ha
  apply List.all_eq_true.mpr
  intro b hb
  have hasafe := h a ha
  have hbsafe := h b hb
  by_cases he : a.thread = b.thread
  · simp [conflict, he]
  · cases haw : a.write <;> cases hbw : b.write <;>
      simp [AccessSafe, haw, hbw] at hasafe hbsafe
    · simp [conflict, haw, hbw]
    · have hn : a.location.buffer ≠ 3 := by have hi := hasafe.2.2; omega
      simp [conflict, sameLocation, hbsafe, haw, hbw, outputCell, hn]
    · have hn : (3 : Nat) ≠ b.location.buffer := by have hi := hbsafe.2.2; omega
      simp [conflict, sameLocation, hasafe, haw, hbw, outputCell, hn]
    · simp [conflict, sameLocation, hasafe, hbsafe, outputCell, haw, hbw, he]

def referenceSpec (ops : Ops α) (input : Nat → Nat → α) : List α :=
  (List.range 32768).map (reference ops input)

theorem extract_outputs (s : State α) (values : Nat → α)
    (h : ∀ i, i < 32768 → s.memory (outputCell i) = some (values i)) :
    extract layout s = some ((List.range 32768).map values) := by
  simp only [extract, layout, List.zipIdx_cons, List.zipIdx_nil, List.flatMap_cons,
    List.flatMap_nil, List.nil_append]
  simp only [List.map_cons, List.map_nil, show Role.input ≠ Role.output by decide,
    ↓reduceIte, List.nil_append, List.append_nil]
  change (((List.range 32768).map (fun i => (3, i))).mapM
    (fun bi => s.memory ⟨.global, 0, bi.1, bi.2⟩) : Option (List α)) = _
  rw [LarkPointwise.mapM_map]
  exact LarkPointwise.mapM_some (List.range 32768) _ _ (by
    intro i hi
    exact h i (List.mem_range.mp hi))

theorem runLanes_contract (ops : Ops α) (input : Nat → Nat → α) (k r : Nat) (s : State α)
    (hcount : k+r ≤ 32768) (hr : Reads input s) (htrace : TraceSafe s.trace) :
    ∃ final, LaneSequence ops program k r s final ∧
      (∀ i, k ≤ i → i < k+r → final.memory (outputCell i) = some (reference ops input i)) ∧
      (∀ l, (∀ i, k ≤ i → i < k+r → l ≠ outputCell i) → final.memory l = s.memory l) ∧
      TraceSafe final.trace := by
  refine ⟨runLanes ops input k r s, runLanes_execute ops input k r s hcount hr, ?_, ?_,
    runLanes_trace_safe ops input k r s htrace⟩
  · intro i hlow hhigh
    exact runLanes_output_inside ops input k r i s ⟨hlow, hhigh⟩
  · intro l h
    exact runLanes_other_memory ops input k r s l h

/-- The full concrete launch uses the symbolic existence theorem without expanding its state witness. -/
theorem complete_launch (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) :
    ∃ final, LaneSequence ops program 0 32768 (initial layout input outside) final ∧
      (∀ i, i < 32768 → final.memory (outputCell i) = some (reference ops input i)) ∧
      (∀ l, (∀ i, i < 32768 → l ≠ outputCell i) → final.memory l = (initial layout input outside).memory l) ∧
      TraceSafe final.trace := by
  obtain ⟨final, execution, outputs, preserved, safe⟩ :=
    runLanes_contract ops input 0 32768 (initial layout input outside) (by decide)
      (initial_reads input outside) (by simp [TraceSafe, initial])
  exact ⟨final, execution, (fun i hi => outputs i (Nat.zero_le _) hi),
    (fun l h => preserved l (fun i _ hi => h i hi)), safe⟩

def Correct (ops : Ops α) (p : List Instruction) (spec : (Nat → Nat → α) → List α) : Prop :=
  ∀ input outside, ∃ final,
    LaneSequence ops p 0 32768 (initial layout input outside) final ∧
    raceFree geometry final.trace = true ∧
    extract layout final = some (spec input) ∧
    (∀ l, (∀ i, i < 32768 → l ≠ outputCell i) → final.memory l = (initial layout input outside).memory l)

theorem kernel_correct (ops : Ops α) : Correct ops program (referenceSpec ops) := by
  intro input outside
  obtain ⟨final, execution, outputs, preserved, safe⟩ := complete_launch ops input outside
  exact ⟨final, execution, trace_safe_raceFree geometry final.trace safe,
    extract_outputs final (reference ops input) outputs, preserved⟩

theorem launch_execution (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) :
    ∃ final, LaneSequence ops program 0 32768 (initial layout input outside) final := by
  obtain ⟨final, execution, _, _, _⟩ := kernel_correct ops input outside
  exact ⟨final, execution⟩

theorem launch_outputs (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) :
    ∃ final, LaneSequence ops program 0 32768 (initial layout input outside) final ∧
      (∀ i, i < 32768 → final.memory (outputCell i) = some (reference ops input i)) := by
  obtain ⟨final, execution, outputs, _, _⟩ := complete_launch ops input outside
  exact ⟨final, execution, outputs⟩

theorem launch_other_memory (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) :
    ∃ final, LaneSequence ops program 0 32768 (initial layout input outside) final ∧
      (∀ l, (∀ i, i < 32768 → l ≠ outputCell i) → final.memory l = (initial layout input outside).memory l) := by
  obtain ⟨final, execution, _, _, preserved⟩ := kernel_correct ops input outside
  exact ⟨final, execution, preserved⟩

theorem launch_raceFree (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) :
    ∃ final, LaneSequence ops program 0 32768 (initial layout input outside) final ∧
      raceFree geometry final.trace = true := by
  obtain ⟨final, execution, race, _, _⟩ := kernel_correct ops input outside
  exact ⟨final, execution, race⟩

theorem final_extract (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) :
    ∃ final, LaneSequence ops program 0 32768 (initial layout input outside) final ∧
      extract layout final = some (referenceSpec ops input) := by
  obtain ⟨final, execution, _, values, _⟩ := kernel_correct ops input outside
  exact ⟨final, execution, values⟩

#print axioms runLanes_contract
#print axioms complete_launch
#print axioms branchValue_reference
#print axioms laneResult_reference
#print axioms afterLane_memory
#print axioms afterLane_reads
#print axioms runLanes_execute
#print axioms runLanes_output_memory
#print axioms runLanes_other_memory
#print axioms runLanes_output_inside
#print axioms initial_reads
#print axioms launch_execution
#print axioms launch_outputs
#print axioms launch_other_memory
#print axioms afterLane_trace_safe
#print axioms runLanes_trace_safe
#print axioms trace_safe_raceFree
#print axioms launch_raceFree
#print axioms extract_outputs
#print axioms final_extract
#print axioms kernel_correct
#print axioms branch_tail_execute
#print axioms branchReturned_stopped
#print axioms branchReturned_memory
#print axioms branchReturned_trace
#print axioms source_lane
#print axioms laneResult_memory
#print axioms laneResult_trace
#print axioms branch_body_execute
#print axioms bodyStored_pc
#print axioms bodyStored_memory
#print axioms program_branchBody
#print axioms branch_body_step
#print axioms coefficient_address
#print axioms output_address
#print axioms branch_execute
#print axioms globalSine_execute
#print axioms coefficientWide_execute
#print axioms sinePointer_execute
#print axioms globalCosine_execute
#print axioms cosinePointer_execute
#print axioms outputWide_execute
#print axioms outputPointer_execute
#print axioms pointers_execute
#print axioms ready_execute
#print axioms ready_memory
#print axioms ready_pc
#print axioms ready_x0
#print axioms ready_x1
#print axioms ready_predicate
#print axioms lowBit_execute
#print axioms compare_execute
#print axioms literalFalse_execute
#print axioms xor_execute
#print axioms not_odd_even
#print axioms invert_execute
#print axioms predicates_execute
#print axioms inverted_memory
#print axioms instruction_step
#print axioms x_address
#print axioms input_loads_execute
#print axioms inputs_execute
#print axioms inputs_memory
#print axioms bits32_negative2
#print axioms clear_low1
#print axioms parameters_execute
#print axioms index_execute
#print axioms correction_execute
#print axioms adjustment_execute
#print axioms pair_execute
#print axioms mask_execute
#print axioms globalX_execute
#print axioms wideX_execute
#print axioms xPointer_execute
#print axioms coordinates_execute
#print axioms xPointer_pc
#print axioms xPointer_base

end Kernel
end LarkPtxRotary
