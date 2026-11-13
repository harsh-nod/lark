import Lark.PtxLinearInit

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/- Actual unchanged Linear matrix loop. Development only: complete bias epilogue,
   whole-launch reference extraction and race proofs remain required. -/
namespace LarkPtxLinear.Linear.Body
open LarkNonlinear LarkPtxPointwise
open LarkPtxDot
open LarkPtxMatrix

def aCell (t c j : Nat) : Location := ⟨.global, 0, 0, t/512*256+16*c+j⟩
def bCell (t c j : Nat) : Location := ⟨.global, 0, 1, (16*c+j)*512+t%512⟩
def aBase (c : Nat) : Pointer := ⟨0, ((32*c : Nat) : Int), true⟩
def bBase (c : Nat) : Pointer := ⟨1, ((16384*c : Nat) : Int), true⟩
def aPointer (t c : Nat) : Pointer := ⟨0, ((t/512*512+32*c : Nat) : Int), true⟩
def bStride (t j : Nat) : Int := (( (t%512+j*512)*2 : Nat) : Int)
def bPointer (t c j : Nat) : Pointer :=
  ⟨1, ((16384*c+(t%512+j*512)*2 : Nat) : Int), true⟩

theorem a_address (t c j : Nat) (ht : t < 32768) (hc : c < 16) (hj : j < 16) :
    address LarkPtxLinear.Linear.layout LarkPtxLinear.Linear.geometry t (aPointer t c) ((2*j : Nat) : Int) false =
      some (aCell t c j) := by
  have hr : t/512 < 64 := by omega
  have he : ((t/512*512+32*c : Nat) : Int) + ((2*j : Nat) : Int) =
      ((t/512*256+16*c+j : Nat) : Int)*2 := by
    simp only [Int.natCast_add, Int.natCast_mul]; omega
  have hs : signed64 (((t/512*256+16*c+j : Nat) : Int)*2) := by
    unfold signed64; simp only [Int.natCast_add, Int.natCast_mul]; omega
  have hb : t/512*256+16*c+j < 64*256 := by omega
  unfold aPointer
  rw [aligned_address LarkPtxLinear.Linear.layout LarkPtxLinear.Linear.geometry t 0 (t/512*256+16*c+j) _ _ false he hs]
  exact read_location LarkPtxLinear.Linear.layout LarkPtxLinear.Linear.geometry t 0 _ ⟨.input, 64*256⟩ (by rfl) hb

theorem b_address (t c j : Nat) (hc : c < 16) (hj : j < 16) :
    address LarkPtxLinear.Linear.layout LarkPtxLinear.Linear.geometry t (bPointer t c j) 0 false = some (bCell t c j) := by
  have hcol : t%512 < 512 := Nat.mod_lt _ (by decide)
  have he : ((16384*c+(t%512+j*512)*2 : Nat) : Int)+0 =
      (((16*c+j)*512+t%512 : Nat) : Int)*2 := by
    simp only [Int.natCast_add, Int.natCast_mul]; omega
  have hs : signed64 ((((16*c+j)*512+t%512 : Nat) : Int)*2) := by
    unfold signed64; simp only [Int.natCast_add, Int.natCast_mul]; omega
  have hb : (16*c+j)*512+t%512 < 256*512 := by omega
  unfold bPointer
  rw [aligned_address LarkPtxLinear.Linear.layout LarkPtxLinear.Linear.geometry t 1 ((16*c+j)*512+t%512) _ 0 false he hs]
  exact read_location LarkPtxLinear.Linear.layout LarkPtxLinear.Linear.geometry t 1 _ ⟨.input, 256*512⟩ (by rfl) hb

def inputRegister (j : Nat) : Nat := if j = 0 then 69 else 35+2*j
def sumRegister (j : Nat) : Nat := if j = 15 then 69 else 37+2*j
def strideRegister (j : Nat) : Nat := if j = 0 then 19 else if j = 1 then 20 else 19-j

def term (j : Nat) : List LarkPtxLinear.Instruction :=
  [.base (.base (.loadHalf (2*j+1) 30 ((2*j : Nat) : Int))),
   .base (.base (.fromHalf (4+2*j) (2*j+1))),
   .base (.base (.addSigned64 (31+j) 53 (.reg (strideRegister j)))),
   .base (.base (.loadHalf (2*j+2) (31+j) 0)),
   .base (.base (.fromHalf (5+2*j) (2*j+2))),
   .base (.base (.binaryFloat (36+2*j) .mul (4+2*j) (5+2*j))),
   .base (.base (.binaryFloat (sumRegister j) .add (inputRegister j) (36+2*j)))]

theorem program_term : ∀ (j : Fin 16) (q : Fin 7),
    LarkPtxLinear.Linear.program[51+7*j.val+q.val]? = (term j.val)[q.val]? := by decide

theorem base_step_in_term (ops : Ops α) (t j q : Nat) (s u : Machine α)
    (instruction : LarkPtxDot.Instruction) (hj : j < 16) (hq : q < 7)
    (hpc : s.pc = 51+7*j+q) (hs : s.registers.stopped = false)
    (hi : (term j)[q]? = some (.base (.base instruction)))
    (he : LarkPtxDot.execute ops LarkPtxLinear.Linear.layout LarkPtxLinear.Linear.geometry t instruction s = some u) :
    LarkPtxLinear.Steps ops LarkPtxLinear.Linear.layout LarkPtxLinear.Linear.geometry t LarkPtxLinear.Linear.program s u := by
  have hf := program_term ⟨j, hj⟩ ⟨q, hq⟩
  rw [hi] at hf
  apply LarkPtxLinear.one_step
  rw [LarkPtxLinear.transition_at ops LarkPtxLinear.Linear.layout LarkPtxLinear.Linear.geometry t LarkPtxLinear.Linear.program s (.base (.base instruction)) hs
    (by rw [hpc]; exact hf), LarkPtxLinear.dot_step]
  exact he

def termLoadA (t c j : Nat) (a : α) (s : Machine α) : Machine α :=
  loadedHalf s t (2*j+1) (aCell t c j) a
def termCastA (ops : Ops α) (t c j : Nat) (a : α) (s : Machine α) : Machine α :=
  setFloat (termLoadA t c j a s) (4+2*j) (ops.fromHalf a)
def termAddressB (ops : Ops α) (t c j : Nat) (a : α) (s : Machine α) : Machine α :=
  setPointer (termCastA ops t c j a s) (31+j) (bPointer t c j)
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
    (hpc : s.pc = 51+7*j) (hs : s.registers.stopped = false)
    (hpA : s.registers.pointer 30 = some (aPointer t c))
    (hpB : s.registers.pointer 53 = some (bBase c))
    (hstride : s.registers.i64 (strideRegister j) = some (bStride t j))
    (ha : s.registers.base.memory (aCell t c j) = some a)
    (hb : s.registers.base.memory (bCell t c j) = some b)
    (hacc : s.registers.scalar (inputRegister j) = some acc) :
    LarkPtxLinear.Steps ops LarkPtxLinear.Linear.layout LarkPtxLinear.Linear.geometry t LarkPtxLinear.Linear.program s (termResult ops t c j a b acc s) := by
  have h1 := base_step_in_term ops t j 0 s (termLoadA t c j a s)
    (.loadHalf (2*j+1) 30 ((2*j : Nat) : Int)) hj (by decide)
    (by simpa only [Nat.add_zero] using hpc) hs (by rfl)
    (loadHalf_step ops LarkPtxLinear.Linear.layout LarkPtxLinear.Linear.geometry t (2*j+1) 30 _ s _ _ a hpA (a_address t c j ht hc hj) ha)
  have h2 := base_step_in_term ops t j 1 (termLoadA t c j a s) (termCastA ops t c j a s)
    (.fromHalf (4+2*j) (2*j+1)) hj (by decide)
    (by simp only [termLoadA, loadedHalf_pc]; omega)
    (by simpa only [termLoadA, loadedHalf_stopped] using hs) (by rfl)
    (fromHalf_step ops LarkPtxLinear.Linear.layout LarkPtxLinear.Linear.geometry t (4+2*j) (2*j+1) _ a (by simp [termLoadA]))
  have hptr : (termCastA ops t c j a s).registers.values (.int64 53) = some (.address (bBase c)) := by
    apply pointer_values
    simpa only [termCastA, termLoadA, setFloat_pointer, loadedHalf_pointer] using hpB
  have hval : operand64 (termCastA ops t c j a s).registers (.reg (strideRegister j)) =
      some (bStride t j) := by
    simpa only [operand64, termCastA, termLoadA, setFloat_i64, loadedHalf_i64] using hstride
  have hcol : t%512 < 512 := Nat.mod_lt _ (by decide)
  have hbound : signed64 (bStride t j) ∧ signed64 ((bBase c).offset+bStride t j) := by
    unfold bStride bBase signed64
    simp only [Int.natCast_add, Int.natCast_mul]; omega
  have e3 := pointer_add_step ops LarkPtxLinear.Linear.layout LarkPtxLinear.Linear.geometry t (31+j) 53 (.reg (strideRegister j))
    (bBase c) (bStride t j) (termCastA ops t c j a s) hptr hval hbound
  have heq : { bBase c with offset := (bBase c).offset+bStride t j } = bPointer t c j := by
    simp only [bBase, bStride, bPointer, Int.natCast_add]
  rw [heq] at e3
  have h3 := base_step_in_term ops t j 2 (termCastA ops t c j a s) (termAddressB ops t c j a s)
    (.addSigned64 (31+j) 53 (.reg (strideRegister j))) hj (by decide)
    (by simp only [termCastA, termLoadA, setFloat_pc, loadedHalf_pc]; omega)
    (by simpa only [termCastA, termLoadA, setFloat_stopped, loadedHalf_stopped] using hs)
    (by rfl) e3
  have h4 := base_step_in_term ops t j 3 (termAddressB ops t c j a s) (termLoadB ops t c j a b s)
    (.loadHalf (2*j+2) (31+j) 0) hj (by decide)
    (by simp only [termAddressB, termCastA, termLoadA, setPointer_pc, setFloat_pc, loadedHalf_pc]; omega)
    (by simpa only [termAddressB, termCastA, termLoadA, setPointer_stopped, setFloat_stopped,
      loadedHalf_stopped] using hs) (by rfl)
    (loadHalf_step ops LarkPtxLinear.Linear.layout LarkPtxLinear.Linear.geometry t (2*j+2) (31+j) 0 _ _ _ b
      (by simp [termAddressB]) (b_address t c j hc hj)
      (by simpa only [termAddressB, termCastA, termLoadA, setPointer_base, setFloat_memory,
        loadedHalf_memory] using hb))
  have h5 := base_step_in_term ops t j 4 (termLoadB ops t c j a b s) (termCastB ops t c j a b s)
    (.fromHalf (5+2*j) (2*j+2)) hj (by decide)
    (by simp only [termLoadB, termAddressB, termCastA, termLoadA, setPointer_pc, setFloat_pc,
      loadedHalf_pc]; omega)
    (by simpa only [termLoadB, termAddressB, termCastA, termLoadA, loadedHalf_stopped,
      setPointer_stopped, setFloat_stopped] using hs) (by rfl)
    (fromHalf_step ops LarkPtxLinear.Linear.layout LarkPtxLinear.Linear.geometry t (5+2*j) (2*j+2) _ b (by simp [termLoadB]))
  have hrAB : 4+2*j ≠ 5+2*j := by omega
  have h6 := base_step_in_term ops t j 5 (termCastB ops t c j a b s) (termProduct ops t c j a b s)
    (.binaryFloat (36+2*j) .mul (4+2*j) (5+2*j)) hj (by decide)
    (by simp only [termCastB, termLoadB, termAddressB, termCastA, termLoadA,
      setPointer_pc, setFloat_pc, loadedHalf_pc]; omega)
    (by simpa only [termCastB, termLoadB, termAddressB, termCastA, termLoadA,
      setPointer_stopped, setFloat_stopped, loadedHalf_stopped] using hs) (by rfl)
    (binaryFloat_step ops LarkPtxLinear.Linear.layout LarkPtxLinear.Linear.geometry t (36+2*j) (4+2*j) (5+2*j) .mul _ _ _
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
    (binaryFloat_step ops LarkPtxLinear.Linear.layout LarkPtxLinear.Linear.geometry t (sumRegister j) (inputRegister j) (36+2*j) .add _ _ _
      (by simp [termProduct, termCastB, termLoadB, termAddressB, termCastA, termLoadA,
        hrA, hrB, hrP, hacc]) (by simp [termProduct]))
  apply LarkPtxLinear.steps_trans _ _ _ _ _ _ _ _ h1
  apply LarkPtxLinear.steps_trans _ _ _ _ _ _ _ _ h2
  apply LarkPtxLinear.steps_trans _ _ _ _ _ _ _ _ h3
  apply LarkPtxLinear.steps_trans _ _ _ _ _ _ _ _ h4
  apply LarkPtxLinear.steps_trans _ _ _ _ _ _ _ _ h5
  exact LarkPtxLinear.steps_trans _ _ _ _ _ _ _ _ h6 h7

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
      if r = 31+j then some (bPointer t c j) else s.registers.pointer r := by
  simp only [termResult, termProduct, termCastB, termLoadB, termAddressB, termCastA, termLoadA,
    setFloat_pointer, loadedHalf_pointer, setPointer_pointer]

theorem termResult_i64 (ops : Ops α) (t c j r : Nat) (a b acc : α) (s : Machine α) :
    (termResult ops t c j a b acc s).registers.i64 r =
      if r = 31+j then none else s.registers.i64 r := by
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

def accumulatorRegister (j : Nat) : Nat := if j = 0 ∨ j = 16 then 69 else 35+2*j

theorem source_accumulator : ∀ j : Fin 16,
    inputRegister j.val = accumulatorRegister j.val ∧
    sumRegister j.val = accumulatorRegister (j.val+1) := by decide

theorem stride_register_bound (j : Nat) : strideRegister j < 21 := by
  unfold strideRegister
  split <;> try omega
  split <;> omega

def Reads (input : Nat → Nat → α) (s : Machine α) : Prop :=
  (∀ i, i < 64*256 → s.registers.base.memory ⟨.global, 0, 0, i⟩ = some (input 0 i)) ∧
  (∀ i, i < 256*512 → s.registers.base.memory ⟨.global, 0, 1, i⟩ = some (input 1 i))

structure BodyInvariant (input : Nat → Nat → α) (t c j : Nat) (acc : α) (s : Machine α) : Prop where
  pc : s.pc = 51+7*j
  stopped : s.registers.stopped = false
  a : s.registers.pointer 30 = some (aPointer t c)
  b : s.registers.pointer 53 = some (bBase c)
  strides : ∀ k, k < 16 → s.registers.i64 (strideRegister k) = some (bStride t k)
  accumulator : s.registers.scalar (accumulatorRegister j) = some acc
  reads : Reads input s
  thread : s.registers.i32 1 = some (t : Int)
  counter : s.registers.i32 27 = some ((16*c : Nat) : Int)
  output : s.registers.pointer 3 = some ⟨3, 0, true⟩
  abase : s.registers.pointer 52 = some (aBase c)
  rowOffset : s.registers.i64 21 = some ((t/512*512 : Nat) : Int)
  bias : s.registers.pointer 26 = some ⟨2, 0, false⟩
  biasColumn : s.registers.i64 18 = some ((t%512 : Nat) : Int)

def nextValue (ops : Ops α) (input : Nat → Nat → α) (t c j : Nat) (acc : α) : α :=
  ops.add acc (ops.mul (ops.fromHalf (input 0 (t/512*256+16*c+j)))
    (ops.fromHalf (input 1 ((16*c+j)*512+t%512))))

def chunkStep (ops : Ops α) (input : Nat → Nat → α) (t c j : Nat) (acc : α)
    (s : Machine α) : Machine α :=
  termResult ops t c j (input 0 (t/512*256+16*c+j)) (input 1 ((16*c+j)*512+t%512)) acc s

theorem chunk_step (ops : Ops α) (input : Nat → Nat → α) (t c j : Nat) (acc : α)
    (s : Machine α) (ht : t < 32768) (hc : c < 16) (hj : j < 16)
    (h : BodyInvariant input t c j acc s) :
    LarkPtxLinear.Steps ops LarkPtxLinear.Linear.layout LarkPtxLinear.Linear.geometry t LarkPtxLinear.Linear.program s (chunkStep ops input t c j acc s) ∧
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
  · simpa only [chunkStep, termResult_pointer, if_neg (by omega : 30 ≠ 31+j)] using h.a
  · simpa only [chunkStep, termResult_pointer, if_neg (by omega : 53 ≠ 31+j)] using h.b
  · intro k hk
    have hkb := stride_register_bound k
    simpa only [chunkStep, termResult_i64, if_neg (by omega : strideRegister k ≠ 31+j)]
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
  · simpa only [chunkStep, termResult_pointer, if_neg (by omega : 3 ≠ 31+j)] using h.output
  · simpa only [chunkStep, termResult_pointer, if_neg (by omega : 52 ≠ 31+j)] using h.abase
  · simpa only [chunkStep, termResult_i64, if_neg (by omega : 21 ≠ 31+j)] using h.rowOffset

  · simpa only [chunkStep, termResult_pointer, if_neg (by omega : 26 ≠ 31+j)] using h.bias
  · simpa only [chunkStep, termResult_i64, if_neg (by omega : 18 ≠ 31+j)] using h.biasColumn

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
    LarkPtxLinear.Steps ops LarkPtxLinear.Linear.layout LarkPtxLinear.Linear.geometry t LarkPtxLinear.Linear.program s (runTerms ops input t c j n acc s) ∧
    BodyInvariant input t c (j+n) (foldTerms ops input t c j n acc) (runTerms ops input t c j n acc s) := by
  induction n generalizing j acc s with
  | zero => exact ⟨.refl _, h⟩
  | succ n ih =>
      have head := chunk_step ops input t c j acc s ht hc (by omega) h
      have tail := ih (j+1) (nextValue ops input t c j acc) (chunkStep ops input t c j acc s)
        (by omega) head.2
      refine ⟨LarkPtxLinear.steps_trans _ _ _ _ _ _ _ _ head.1 tail.1, ?_⟩
      have he : j+(n+1) = (j+1)+n := by omega
      rw [he]
      exact tail.2

structure LoopInvariant (input : Nat → Nat → α) (t c : Nat) (acc : α) (s : Machine α) : Prop where
  pc : s.pc = if c < 16 then 50 else 168
  stopped : s.registers.stopped = false
  a : s.registers.pointer 52 = some (aBase c)
  b : s.registers.pointer 53 = some (bBase c)
  strides : ∀ k, k < 16 → s.registers.i64 (strideRegister k) = some (bStride t k)
  accumulator : s.registers.scalar 69 = some acc
  reads : Reads input s
  thread : s.registers.i32 1 = some (t : Int)
  counter : s.registers.i32 27 = some ((16*c : Nat) : Int)
  output : s.registers.pointer 3 = some ⟨3, 0, true⟩
  rowOffset : s.registers.i64 21 = some ((t/512*512 : Nat) : Int)
  bias : s.registers.pointer 26 = some ⟨2, 0, false⟩
  biasColumn : s.registers.i64 18 = some ((t%512 : Nat) : Int)

def bodyStart (t c : Nat) (s : Machine α) : Machine α := setPointer s 30 (aPointer t c)

theorem body_entry (ops : Ops α) (input : Nat → Nat → α) (t c : Nat) (acc : α) (s : Machine α)
    (ht : t < 32768) (hc : c < 16) (h : LoopInvariant input t c acc s) :
    LarkPtxLinear.Steps ops LarkPtxLinear.Linear.layout LarkPtxLinear.Linear.geometry t LarkPtxLinear.Linear.program s (bodyStart t c s) ∧
    BodyInvariant input t c 0 acc (bodyStart t c s) := by
  have hr : t/512 < 64 := by omega
  have hp : s.pc = 50 := by simpa only [if_pos hc] using h.pc
  have hbound : signed64 ((t/512*512 : Nat) : Int) ∧
      signed64 ((aBase c).offset+((t/512*512 : Nat) : Int)) := by
    unfold aBase signed64
    simp only [Int.natCast_mul]; omega
  have e := pointer_add_step ops LarkPtxLinear.Linear.layout LarkPtxLinear.Linear.geometry t 30 52 (.reg 21) (aBase c)
    ((t/512*512 : Nat) : Int) s (pointer_values _ _ _ h.a) h.rowOffset hbound
  have heq : { aBase c with offset := (aBase c).offset+((t/512*512 : Nat) : Int) } =
      aPointer t c := by
    have he : ((32*c : Nat) : Int)+((t/512*512 : Nat) : Int) =
        ((t/512*512+32*c : Nat) : Int) := by
      simp only [Int.natCast_add]; omega
    simp only [aBase, aPointer, he]
  rw [heq] at e
  have hexe : LarkPtxLinear.Steps ops LarkPtxLinear.Linear.layout LarkPtxLinear.Linear.geometry t LarkPtxLinear.Linear.program s (bodyStart t c s) := by
    apply LarkPtxLinear.one_step
    rw [LarkPtxLinear.transition_at ops LarkPtxLinear.Linear.layout LarkPtxLinear.Linear.geometry t LarkPtxLinear.Linear.program s (.base (.base (.addSigned64 30 52 (.reg 21))))
      h.stopped (by rw [hp]; rfl), LarkPtxLinear.dot_step]
    exact e
  refine ⟨hexe, ?_⟩
  constructor
  · simp only [bodyStart, setPointer_pc, hp]
  · simpa only [bodyStart, setPointer_stopped] using h.stopped
  · simp [bodyStart]
  · simpa only [bodyStart, setPointer_pointer, if_neg (by decide : 53 ≠ 30)] using h.b
  · intro k hk
    have hkb := stride_register_bound k
    simpa only [bodyStart, setPointer_i64, if_neg (by omega : strideRegister k ≠ 30)] using h.strides k hk
  · simpa only [bodyStart, setPointer_scalar, accumulatorRegister, if_pos (by decide : 0 = 0 ∨ 0 = 16)]
      using h.accumulator
  · exact h.reads
  · simpa only [bodyStart, setPointer_i32] using h.thread
  · simpa only [bodyStart, setPointer_i32] using h.counter
  · simpa only [bodyStart, setPointer_pointer, if_neg (by decide : 3 ≠ 30)] using h.output
  · simpa only [bodyStart, setPointer_pointer, if_neg (by decide : 52 ≠ 30)] using h.a
  · simpa only [bodyStart, setPointer_i64, if_neg (by decide : 21 ≠ 30)] using h.rowOffset

  · simpa only [bodyStart, setPointer_pointer, if_neg (by decide : 26 ≠ 30)] using h.bias
  · simpa only [bodyStart, setPointer_i64, if_neg (by decide : 18 ≠ 30)] using h.biasColumn

def chunkValue (ops : Ops α) (input : Nat → Nat → α) (t c : Nat) (acc : α) : α :=
  foldTerms ops input t c 0 16 acc

def bodyEnd (ops : Ops α) (input : Nat → Nat → α) (t c : Nat) (acc : α)
    (s : Machine α) : Machine α := runTerms ops input t c 0 16 acc (bodyStart t c s)

theorem body_execute (ops : Ops α) (input : Nat → Nat → α) (t c : Nat) (acc : α)
    (s : Machine α) (ht : t < 32768) (hc : c < 16) (h : LoopInvariant input t c acc s) :
    LarkPtxLinear.Steps ops LarkPtxLinear.Linear.layout LarkPtxLinear.Linear.geometry t LarkPtxLinear.Linear.program s (bodyEnd ops input t c acc s) ∧
    BodyInvariant input t c 16 (chunkValue ops input t c acc) (bodyEnd ops input t c acc s) := by
  have head := body_entry ops input t c acc s ht hc h
  have tail := runTerms_execute ops input t c 0 16 acc (bodyStart t c s) ht hc (by decide) head.2
  exact ⟨LarkPtxLinear.steps_trans _ _ _ _ _ _ _ _ head.1 tail.1, tail.2⟩

def bAdvanced (c : Nat) (s : Machine α) : Machine α := setPointer s 53 (bBase (c+1))
def aAdvanced (c : Nat) (s : Machine α) : Machine α := setPointer (bAdvanced c s) 52 (aBase (c+1))
def counted (c : Nat) (s : Machine α) : Machine α :=
  setIndex32 (aAdvanced c s) 27 ((16*(c+1) : Nat) : Int)
def compared (c : Nat) (s : Machine α) : Machine α :=
  setPredicate (counted c s) 1 (((16*(c+1) : Nat) : Int) != (256 : Int))
def controlResult (c : Nat) (s : Machine α) : Machine α :=
  let next := compared c s
  { next with pc := if (((16*(c+1) : Nat) : Int) != (256 : Int)) then 50 else next.pc+1 }

theorem control_execute (ops : Ops α) (input : Nat → Nat → α) (t c : Nat) (acc : α)
    (s : Machine α) (hc : c < 16) (h : BodyInvariant input t c 16 acc s) :
    LarkPtxLinear.Steps ops LarkPtxLinear.Linear.layout LarkPtxLinear.Linear.geometry t LarkPtxLinear.Linear.program s (controlResult c s) := by
  have hpc : s.pc = 163 := h.pc
  have hb : signed64 16384 ∧ signed64 ((bBase c).offset+16384) := by
    unfold signed64 bBase; simp only [Int.natCast_mul]; omega
  have e1 := pointer_add_step ops LarkPtxLinear.Linear.layout LarkPtxLinear.Linear.geometry t 53 53 (.imm 16384) (bBase c) 16384 s
    (pointer_values _ _ _ h.b) (by rfl) hb
  have heB : { bBase c with offset := (bBase c).offset+16384 } = bBase (c+1) := by
    have he : ((16384*c : Nat) : Int)+16384 = ((16384*(c+1) : Nat) : Int) := by
      simp only [Int.natCast_add, Int.natCast_mul]; omega
    simp only [bBase, he]
  rw [heB] at e1
  have h1 : LarkPtxLinear.Steps ops LarkPtxLinear.Linear.layout LarkPtxLinear.Linear.geometry t LarkPtxLinear.Linear.program s (bAdvanced c s) := by
    apply LarkPtxLinear.one_step
    rw [LarkPtxLinear.transition_at ops LarkPtxLinear.Linear.layout LarkPtxLinear.Linear.geometry t LarkPtxLinear.Linear.program s (.base (.base (.addSigned64 53 53 (.imm 16384))))
      h.stopped (by rw [hpc]; rfl), LarkPtxLinear.dot_step]
    exact e1
  have ha : signed64 32 ∧ signed64 ((aBase c).offset+32) := by
    unfold signed64 aBase; simp only [Int.natCast_mul]; omega
  have hpA : (bAdvanced c s).registers.values (.int64 52) = some (.address (aBase c)) := by
    apply pointer_values
    simpa [bAdvanced] using h.abase
  have e2 := pointer_add_step ops LarkPtxLinear.Linear.layout LarkPtxLinear.Linear.geometry t 52 52 (.imm 32) (aBase c) 32 (bAdvanced c s)
    hpA (by rfl) ha
  have heA : { aBase c with offset := (aBase c).offset+32 } = aBase (c+1) := by
    have he : ((32*c : Nat) : Int)+32 = ((32*(c+1) : Nat) : Int) := by
      simp only [Int.natCast_add, Int.natCast_mul]; omega
    simp only [aBase, he]
  rw [heA] at e2
  have h2 : LarkPtxLinear.Steps ops LarkPtxLinear.Linear.layout LarkPtxLinear.Linear.geometry t LarkPtxLinear.Linear.program (bAdvanced c s) (aAdvanced c s) := by
    apply LarkPtxLinear.one_step
    rw [LarkPtxLinear.transition_at ops LarkPtxLinear.Linear.layout LarkPtxLinear.Linear.geometry t LarkPtxLinear.Linear.program (bAdvanced c s) (.base (.base (.addSigned64 52 52 (.imm 32))))
      (by simpa only [bAdvanced, setPointer_stopped] using h.stopped)
      (by simp only [bAdvanced, setPointer_pc, hpc]; rfl), LarkPtxLinear.dot_step]
    exact e2
  have hg : signed32 ((16*c : Nat) : Int) ∧ signed32 16 ∧
      signed32 (((16*c : Nat) : Int)+16) := by
    unfold signed32; simp only [Int.natCast_mul]; omega
  have hx : (aAdvanced c s).registers.i32 27 = some ((16*c : Nat) : Int) := by
    simpa only [aAdvanced, bAdvanced, setPointer_i32] using h.counter
  have e3 := add32_step ops LarkPtxLinear.Linear.layout LarkPtxLinear.Linear.geometry t 27 27 (.imm 16) (aAdvanced c s)
    ((16*c : Nat) : Int) 16 hx (by rfl) hg
  have heC : ((16*c : Nat) : Int)+16 = ((16*(c+1) : Nat) : Int) := by
    simp only [Int.natCast_add, Int.natCast_mul]; omega
  rw [heC] at e3
  have h3 : LarkPtxLinear.Steps ops LarkPtxLinear.Linear.layout LarkPtxLinear.Linear.geometry t LarkPtxLinear.Linear.program (aAdvanced c s) (counted c s) := by
    apply LarkPtxLinear.one_step
    rw [LarkPtxLinear.transition_at ops LarkPtxLinear.Linear.layout LarkPtxLinear.Linear.geometry t LarkPtxLinear.Linear.program (aAdvanced c s) (.base (.base (.addSigned32 27 27 (.imm 16))))
      (by simpa only [aAdvanced, bAdvanced, setPointer_stopped] using h.stopped)
      (by simp only [aAdvanced, bAdvanced, setPointer_pc, hpc]; rfl), LarkPtxLinear.dot_step]
    exact e3
  have hp : signed32 ((16*(c+1) : Nat) : Int) ∧ signed32 256 := by
    unfold signed32; simp only [Int.natCast_add, Int.natCast_mul]; omega
  have e4 := compare_ne_step ops LarkPtxLinear.Linear.layout LarkPtxLinear.Linear.geometry t 1 27 (.imm 256) (counted c s)
    ((16*(c+1) : Nat) : Int) 256 (by simp [counted]) (by rfl) hp
  have h4 : LarkPtxLinear.Steps ops LarkPtxLinear.Linear.layout LarkPtxLinear.Linear.geometry t LarkPtxLinear.Linear.program (counted c s) (compared c s) := by
    apply LarkPtxLinear.one_step
    rw [LarkPtxLinear.transition_at ops LarkPtxLinear.Linear.layout LarkPtxLinear.Linear.geometry t LarkPtxLinear.Linear.program (counted c s) (.base (.base (.compareNeSigned32 1 27 (.imm 256))))
      (by change s.registers.stopped = false; exact h.stopped)
      (by simp only [counted, aAdvanced, bAdvanced, setIndex32_pc, setPointer_pc, hpc]; rfl), LarkPtxLinear.dot_step]
    exact e4
  have h5 : LarkPtxLinear.Steps ops LarkPtxLinear.Linear.layout LarkPtxLinear.Linear.geometry t LarkPtxLinear.Linear.program (compared c s) (controlResult c s) := by
    apply LarkPtxLinear.one_step
    rw [LarkPtxLinear.transition_at ops LarkPtxLinear.Linear.layout LarkPtxLinear.Linear.geometry t LarkPtxLinear.Linear.program (compared c s) (.base (.base (.branch 1 50)))
      (by change s.registers.stopped = false; exact h.stopped)
      (by simp only [compared, counted, aAdvanced, bAdvanced, setPredicate_pc,
        setIndex32_pc, setPointer_pc, hpc]; rfl), LarkPtxLinear.dot_step]
    simp only [LarkPtxDot.execute, compared, setPredicate, bind, pure, Option.bind]
    rfl
  apply LarkPtxLinear.steps_trans _ _ _ _ _ _ _ _ h1
  apply LarkPtxLinear.steps_trans _ _ _ _ _ _ _ _ h2
  apply LarkPtxLinear.steps_trans _ _ _ _ _ _ _ _ h3
  exact LarkPtxLinear.steps_trans _ _ _ _ _ _ _ _ h4 h5

theorem control_pc (c : Nat) (s : Machine α) (hc : c < 16) (hpc : s.pc = 163) :
    (controlResult c s).pc = if c+1 < 16 then 50 else 168 := by
  by_cases hn : c+1 < 16
  · have hne : (16 : Int)*((c : Int)+1) ≠ 256 := by omega
    simp [controlResult, hne, hn]
  · have he : c+1 = 16 := by omega
    simp [controlResult, compared, counted, aAdvanced, bAdvanced, he, hn, hpc]

theorem control_memory (c : Nat) (s : Machine α) :
    (controlResult c s).registers.base.memory = s.registers.base.memory := rfl

theorem control_i64 (c r : Nat) (s : Machine α) :
    (controlResult c s).registers.i64 r = if r = 52 then none else if r = 53 then none else s.registers.i64 r := by
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
  · change s.registers.scalar 69 = some acc
    simpa only [accumulatorRegister, if_pos (by decide : 16 = 0 ∨ 16 = 16)] using h.accumulator
  · change Reads input s
    exact h.reads
  · change s.registers.i32 1 = some (t : Int)
    exact h.thread
  · rfl
  · change s.registers.pointer 3 = some ⟨3, 0, true⟩
    exact h.output
  · rw [control_i64, if_neg (by decide : 21 ≠ 52), if_neg (by decide : 21 ≠ 53)]
    exact h.rowOffset

  · change s.registers.pointer 26 = some ⟨2, 0, false⟩
    exact h.bias
  · rw [control_i64, if_neg (by decide : 18 ≠ 52), if_neg (by decide : 18 ≠ 53)]
    exact h.biasColumn

def iteration (ops : Ops α) (input : Nat → Nat → α) (t c : Nat) (acc : α) (s : Machine α) : Machine α :=
  controlResult c (bodyEnd ops input t c acc s)

theorem iteration_execute (ops : Ops α) (input : Nat → Nat → α) (t c : Nat) (acc : α)
    (s : Machine α) (ht : t < 32768) (hc : c < 16) (h : LoopInvariant input t c acc s) :
    LarkPtxLinear.Steps ops LarkPtxLinear.Linear.layout LarkPtxLinear.Linear.geometry t LarkPtxLinear.Linear.program s (iteration ops input t c acc s) ∧
    LoopInvariant input t (c+1) (chunkValue ops input t c acc) (iteration ops input t c acc s) := by
  have hb := body_execute ops input t c acc s ht hc h
  have he := control_execute ops input t c _ _ hc hb.2
  exact ⟨LarkPtxLinear.steps_trans _ _ _ _ _ _ _ _ hb.1 he, control_invariant input t c _ _ hc hb.2⟩

def foldChunks (ops : Ops α) (input : Nat → Nat → α) (t : Nat) : Nat → Nat → α → α
  | _, 0, acc => acc
  | c, n+1, acc => foldChunks ops input t (c+1) n (chunkValue ops input t c acc)

def runChunks (ops : Ops α) (input : Nat → Nat → α) (t : Nat) : Nat → Nat → α → Machine α → Machine α
  | _, 0, _, s => s
  | c, n+1, acc, s => runChunks ops input t (c+1) n (chunkValue ops input t c acc)
      (iteration ops input t c acc s)

theorem runChunks_execute (ops : Ops α) (input : Nat → Nat → α) (t c n : Nat) (acc : α)
    (s : Machine α) (ht : t < 32768) (hcn : c+n ≤ 16) (h : LoopInvariant input t c acc s) :
    LarkPtxLinear.Steps ops LarkPtxLinear.Linear.layout LarkPtxLinear.Linear.geometry t LarkPtxLinear.Linear.program s (runChunks ops input t c n acc s) ∧
    LoopInvariant input t (c+n) (foldChunks ops input t c n acc) (runChunks ops input t c n acc s) := by
  induction n generalizing c acc s with
  | zero => exact ⟨.refl _, h⟩
  | succ n ih =>
      have head := iteration_execute ops input t c acc s ht (by omega) h
      have tail := ih (c+1) (chunkValue ops input t c acc) (iteration ops input t c acc s)
        (by omega) head.2
      refine ⟨LarkPtxLinear.steps_trans _ _ _ _ _ _ _ _ head.1 tail.1, ?_⟩
      have he : c+(n+1) = (c+1)+n := by omega
      rw [he]
      exact tail.2


theorem ready_loop (ops : Ops α) (input : Nat → Nat → α) (t : Nat)
    (base : State α) (s : Machine α) (h : LarkPtxLinear.Linear.Init.Ready ops t base s)
    (hr : Reads input (LarkPtxLinear.Linear.start base)) :
    LoopInvariant input t 0 (ops.literal 0 1) s := by
  constructor
  · exact h.pc
  · exact h.frame.active
  · simpa only [aBase, Nat.mul_zero, Int.natCast_zero] using h.frame.a
  · simpa only [bBase, Nat.mul_zero, Int.natCast_zero] using h.frame.b
  · intro j hj
    simpa only [strideRegister, bStride, LarkPtxLinear.Linear.Init.strideRegister,
      LarkPtxLinear.Linear.Init.bStride] using h.strides j hj
  · exact h.accumulator
  · constructor
    · intro i hi
      rw [h.frame.memory]
      exact hr.1 i hi
    · intro i hi
      rw [h.frame.memory]
      exact hr.2 i hi
  · exact h.frame.thread
  · exact h.counter
  · exact h.frame.out
  · have he : t/512*256*2 = t/512*512 := by omega
    simpa only [he] using h.rowWide
  · exact h.frame.bias
  · exact h.biasColumn

theorem initial_reads (input : Nat → Nat → α) (outside : Location → Option α) :
    Reads input (LarkPtxLinear.Linear.start (initial LarkPtxLinear.Linear.layout input outside)) := by
  constructor
  · intro i hi
    change (initial LarkPtxLinear.Linear.layout input outside).memory ⟨.global, 0, 0, i⟩ = _
    simp [initial, LarkPtxLinear.Linear.layout, hi]
  · intro i hi
    change (initial LarkPtxLinear.Linear.layout input outside).memory ⟨.global, 0, 1, i⟩ = _
    simp [initial, LarkPtxLinear.Linear.layout, hi]

def dotValue (ops : Ops α) (input : Nat → Nat → α) (t : Nat) : α :=
  foldChunks ops input t 0 16 (ops.literal 0 1)

theorem source_to_loop_exit (ops : Ops α) (input : Nat → Nat → α) (t : Nat)
    (base : State α) (ht : t < 32768) (hr : Reads input (LarkPtxLinear.Linear.start base)) :
    ∃ final, LarkPtxLinear.Steps ops LarkPtxLinear.Linear.layout LarkPtxLinear.Linear.geometry t
        LarkPtxLinear.Linear.program (LarkPtxLinear.Linear.start base) final ∧
      LoopInvariant input t 16 (dotValue ops input t) final := by
  obtain ⟨entry, first, ready⟩ := LarkPtxLinear.Linear.Init.prologue_ready ops t base ht
  have invariant := ready_loop ops input t base entry ready hr
  have loop := runChunks_execute ops input t 0 16 (ops.literal 0 1) entry ht (by decide) invariant
  exact ⟨runChunks ops input t 0 16 (ops.literal 0 1) entry,
    LarkPtxLinear.steps_trans _ _ _ _ _ _ _ _ first loop.1, loop.2⟩

end LarkPtxLinear.Linear.Body

#print axioms LarkPtxLinear.Linear.Body.a_address
#print axioms LarkPtxLinear.Linear.Body.b_address
#print axioms LarkPtxLinear.Linear.Body.program_term
#print axioms LarkPtxLinear.Linear.Body.base_step_in_term
#print axioms LarkPtxLinear.Linear.Body.term_execute
#print axioms LarkPtxLinear.Linear.Body.termResult_pc
#print axioms LarkPtxLinear.Linear.Body.termResult_stopped
#print axioms LarkPtxLinear.Linear.Body.termResult_i32
#print axioms LarkPtxLinear.Linear.Body.termResult_pointer
#print axioms LarkPtxLinear.Linear.Body.termResult_i64
#print axioms LarkPtxLinear.Linear.Body.termResult_memory
#print axioms LarkPtxLinear.Linear.Body.termResult_scalar
#print axioms LarkPtxLinear.Linear.Body.source_accumulator
#print axioms LarkPtxLinear.Linear.Body.stride_register_bound
#print axioms LarkPtxLinear.Linear.Body.chunk_step
#print axioms LarkPtxLinear.Linear.Body.runTerms_execute
#print axioms LarkPtxLinear.Linear.Body.body_entry
#print axioms LarkPtxLinear.Linear.Body.body_execute
#print axioms LarkPtxLinear.Linear.Body.control_execute
#print axioms LarkPtxLinear.Linear.Body.control_pc
#print axioms LarkPtxLinear.Linear.Body.control_memory
#print axioms LarkPtxLinear.Linear.Body.control_i64
#print axioms LarkPtxLinear.Linear.Body.control_invariant
#print axioms LarkPtxLinear.Linear.Body.iteration_execute
#print axioms LarkPtxLinear.Linear.Body.runChunks_execute
#print axioms LarkPtxLinear.Linear.Body.ready_loop
#print axioms LarkPtxLinear.Linear.Body.initial_reads
#print axioms LarkPtxLinear.Linear.Body.source_to_loop_exit
