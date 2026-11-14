import Lark.PtxFeedForwardDownInit

/- Full original down-stage sixteen-term loop, repeated64 times. This component
   connects actual initialization to loop exit; output proofs are separate. -/
namespace LarkPtxMatrix
open LarkNonlinear LarkPtxPointwise LarkPtxDot
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace FfnDown

def aCell (t c j : Nat) : Location := ⟨.global, 0, 0, t/256*1024+16*c+j⟩
def bCell (t c j : Nat) : Location := ⟨.global, 0, 1, (16*c+j)*256+t%256⟩
def aBase (c : Nat) : Pointer := ⟨0, ((32*c : Nat) : Int), true⟩
def bBase (c : Nat) : Pointer := ⟨1, ((8192*c : Nat) : Int), true⟩
def aPointer (t c : Nat) : Pointer := ⟨0, ((t/256*2048+32*c : Nat) : Int), true⟩
def bStride (t j : Nat) : Int := (( (t%256+j*256)*2 : Nat) : Int)
def bPointer (t c j : Nat) : Pointer :=
  ⟨1, ((8192*c+(t%256+j*256)*2 : Nat) : Int), true⟩

theorem a_address (t c j : Nat) (ht : t < 16384) (hc : c < 64) (hj : j < 16) :
    address layout geometry t (aPointer t c) ((2*j : Nat) : Int) false =
      some (aCell t c j) := by
  have hr : t/256 < 64 := by omega
  have he : ((t/256*2048+32*c : Nat) : Int) + ((2*j : Nat) : Int) =
      ((t/256*1024+16*c+j : Nat) : Int)*2 := by
    simp only [Int.natCast_add, Int.natCast_mul]; omega
  have hs : signed64 (((t/256*1024+16*c+j : Nat) : Int)*2) := by
    unfold signed64; simp only [Int.natCast_add, Int.natCast_mul]; omega
  have hb : t/256*1024+16*c+j < 64*1024 := by omega
  unfold aPointer
  rw [aligned_address layout geometry t 0 (t/256*1024+16*c+j) _ _ false he hs]
  exact read_location layout geometry t 0 _ ⟨.input, 64*1024⟩ (by rfl) hb

theorem b_address (t c j : Nat) (hc : c < 64) (hj : j < 16) :
    address layout geometry t (bPointer t c j) 0 false = some (bCell t c j) := by
  have hcol : t%256 < 256 := Nat.mod_lt _ (by decide)
  have he : ((8192*c+(t%256+j*256)*2 : Nat) : Int)+0 =
      (((16*c+j)*256+t%256 : Nat) : Int)*2 := by
    simp only [Int.natCast_add, Int.natCast_mul]; omega
  have hs : signed64 ((((16*c+j)*256+t%256 : Nat) : Int)*2) := by
    unfold signed64; simp only [Int.natCast_add, Int.natCast_mul]; omega
  have hb : (16*c+j)*256+t%256 < 1024*256 := by omega
  unfold bPointer
  rw [aligned_address layout geometry t 1 ((16*c+j)*256+t%256) _ 0 false he hs]
  exact read_location layout geometry t 1 _ ⟨.input, 1024*256⟩ (by rfl) hb

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
    (ht : t < 16384) (hc : c < 64) (hj : j < 16)
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
  have hcol : t%256 < 256 := Nat.mod_lt _ (by decide)
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
  (∀ i, i < 64*1024 → s.registers.base.memory ⟨.global, 0, 0, i⟩ = some (input 0 i)) ∧
  (∀ i, i < 1024*256 → s.registers.base.memory ⟨.global, 0, 1, i⟩ = some (input 1 i))

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
  rowOffset : s.registers.i64 19 = some ((t/256*2048 : Nat) : Int)

def nextValue (ops : Ops α) (input : Nat → Nat → α) (t c j : Nat) (acc : α) : α :=
  ops.add acc (ops.mul (ops.fromHalf (input 0 (t/256*1024+16*c+j)))
    (ops.fromHalf (input 1 ((16*c+j)*256+t%256))))

def chunkStep (ops : Ops α) (input : Nat → Nat → α) (t c j : Nat) (acc : α)
    (s : Machine α) : Machine α :=
  termResult ops t c j (input 0 (t/256*1024+16*c+j)) (input 1 ((16*c+j)*256+t%256)) acc s

theorem chunk_step (ops : Ops α) (input : Nat → Nat → α) (t c j : Nat) (acc : α)
    (s : Machine α) (ht : t < 16384) (hc : c < 64) (hj : j < 16)
    (h : BodyInvariant input t c j acc s) :
    Steps ops layout geometry t program s (chunkStep ops input t c j acc s) ∧
    BodyInvariant input t c (j+1) (nextValue ops input t c j acc) (chunkStep ops input t c j acc s) := by
  have hr : t/256 < 64 := by omega
  have hcol : t%256 < 256 := Nat.mod_lt _ (by decide)
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
    (s : Machine α) (ht : t < 16384) (hc : c < 64) (hjn : j+n ≤ 16)
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
  pc : s.pc = if c < 64 then 47 else 165
  stopped : s.registers.stopped = false
  a : s.registers.pointer 47 = some (aBase c)
  b : s.registers.pointer 48 = some (bBase c)
  strides : ∀ k, k < 16 → s.registers.i64 (strideRegister k) = some (bStride t k)
  accumulator : s.registers.scalar 68 = some acc
  reads : Reads input s
  thread : s.registers.i32 1 = some (t : Int)
  counter : s.registers.i32 27 = some ((16*c : Nat) : Int)
  output : s.registers.pointer 24 = some ⟨2, 0, false⟩
  rowOffset : s.registers.i64 19 = some ((t/256*2048 : Nat) : Int)

def bodyStart (t c : Nat) (s : Machine α) : Machine α := setPointer s 27 (aPointer t c)

theorem body_entry (ops : Ops α) (input : Nat → Nat → α) (t c : Nat) (acc : α) (s : Machine α)
    (ht : t < 16384) (hc : c < 64) (h : LoopInvariant input t c acc s) :
    Steps ops layout geometry t program s (bodyStart t c s) ∧
    BodyInvariant input t c 0 acc (bodyStart t c s) := by
  have hr : t/256 < 64 := by omega
  have hp : s.pc = 47 := by simpa only [if_pos hc] using h.pc
  have hbound : signed64 ((t/256*2048 : Nat) : Int) ∧
      signed64 ((aBase c).offset+((t/256*2048 : Nat) : Int)) := by
    unfold aBase signed64
    simp only [Int.natCast_mul]; omega
  have e := pointer_add_step ops layout geometry t 27 47 (.reg 19) (aBase c)
    ((t/256*2048 : Nat) : Int) s (pointer_values _ _ _ h.a) h.rowOffset hbound
  have heq : { aBase c with offset := (aBase c).offset+((t/256*2048 : Nat) : Int) } =
      aPointer t c := by
    have he : ((32*c : Nat) : Int)+((t/256*2048 : Nat) : Int) =
        ((t/256*2048+32*c : Nat) : Int) := by
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
    (s : Machine α) (ht : t < 16384) (hc : c < 64) (h : LoopInvariant input t c acc s) :
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
  setPredicate (counted c s) 1 (((16*(c+1) : Nat) : Int) != (1024 : Int))
def controlResult (c : Nat) (s : Machine α) : Machine α :=
  let next := compared c s
  { next with pc := if (((16*(c+1) : Nat) : Int) != (1024 : Int)) then 47 else next.pc+1 }

theorem control_execute (ops : Ops α) (input : Nat → Nat → α) (t c : Nat) (acc : α)
    (s : Machine α) (hc : c < 64) (h : BodyInvariant input t c 16 acc s) :
    Steps ops layout geometry t program s (controlResult c s) := by
  have hpc : s.pc = 160 := h.pc
  have hb : signed64 8192 ∧ signed64 ((bBase c).offset+8192) := by
    unfold signed64 bBase; simp only [Int.natCast_mul]; omega
  have e1 := pointer_add_step ops layout geometry t 48 48 (.imm 8192) (bBase c) 8192 s
    (pointer_values _ _ _ h.b) (by rfl) hb
  have heB : { bBase c with offset := (bBase c).offset+8192 } = bBase (c+1) := by
    have he : ((8192*c : Nat) : Int)+8192 = ((8192*(c+1) : Nat) : Int) := by
      simp only [Int.natCast_add, Int.natCast_mul]; omega
    simp only [bBase, he]
  rw [heB] at e1
  have h1 : Steps ops layout geometry t program s (bAdvanced c s) := by
    apply one_step
    rw [transition_at ops layout geometry t program s (.base (.addSigned64 48 48 (.imm 8192)))
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
  have hp : signed32 ((16*(c+1) : Nat) : Int) ∧ signed32 1024 := by
    unfold signed32; simp only [Int.natCast_add, Int.natCast_mul]; omega
  have e4 := compare_ne_step ops layout geometry t 1 27 (.imm 1024) (counted c s)
    ((16*(c+1) : Nat) : Int) 1024 (by simp [counted]) (by rfl) hp
  have h4 : Steps ops layout geometry t program (counted c s) (compared c s) := by
    apply one_step
    rw [transition_at ops layout geometry t program (counted c s) (.base (.compareNeSigned32 1 27 (.imm 1024)))
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

theorem control_pc (c : Nat) (s : Machine α) (hc : c < 64) (hpc : s.pc = 160) :
    (controlResult c s).pc = if c+1 < 64 then 47 else 165 := by
  by_cases hn : c+1 < 64
  · have hne : (16 : Int)*((c : Int)+1) ≠ 1024 := by omega
    simp [controlResult, hne, hn]
  · have he : c+1 = 64 := by omega
    simp [controlResult, compared, counted, aAdvanced, bAdvanced, he, hn, hpc]

theorem control_memory (c : Nat) (s : Machine α) :
    (controlResult c s).registers.base.memory = s.registers.base.memory := rfl

theorem control_i64 (c r : Nat) (s : Machine α) :
    (controlResult c s).registers.i64 r = if r = 47 then none else if r = 48 then none else s.registers.i64 r := by
  simp only [controlResult, compared, counted, aAdvanced, bAdvanced,
    setPredicate_registers, setIndex32_i64, setPointer_i64]

theorem control_invariant (input : Nat → Nat → α) (t c : Nat) (acc : α) (s : Machine α)
    (hc : c < 64) (h : BodyInvariant input t c 16 acc s) :
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
    (s : Machine α) (ht : t < 16384) (hc : c < 64) (h : LoopInvariant input t c acc s) :
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
    (s : Machine α) (ht : t < 16384) (hcn : c+n ≤ 64) (h : LoopInvariant input t c acc s) :
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

theorem initialized_strides (ops : Ops α) (t k : Nat) (s : State α) (hk : k < 16) :
    (initialized ops t s).registers.i64 (strideRegister k) = some (bStride t k) := by
  have cases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rfl

theorem initialized_loop (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α)
    (hreads : Reads input (start s)) :
    LoopInvariant input t 0 (ops.literal 0 1) (initialized ops t s) := by
  constructor
  · exact initialized_pc ops t s
  · rfl
  · rfl
  · rfl
  · exact fun k hk => initialized_strides ops t k s hk
  · rfl
  · constructor
    · intro i hi
      rw [initialized_base]
      exact hreads.1 i hi
    · intro i hi
      rw [initialized_base]
      exact hreads.2 i hi
  · rfl
  · rfl
  · rfl
  · change some (((t/256*1024 : Nat) : Int)*2) = some ((t/256*2048 : Nat) : Int)
    congr 1
    simp only [Int.natCast_mul]
    omega

def dotValue (ops : Ops α) (input : Nat → Nat → α) (t : Nat) : α :=
  foldChunks ops input t 0 64 (ops.literal 0 1)

def loopExit (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) : Machine α :=
  runChunks ops input t 0 64 (ops.literal 0 1) (initialized ops t s)

theorem source_to_loop_exit (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α)
    (ht : t < 16384) (hreads : Reads input (start s)) :
    Steps ops layout geometry t program (start s) (loopExit ops input t s) ∧
    LoopInvariant input t 64 (dotValue ops input t) (loopExit ops input t s) := by
  have he := runChunks_execute ops input t 0 64 (ops.literal 0 1) (initialized ops t s) ht
    (by decide) (initialized_loop ops input t s hreads)
  exact ⟨steps_trans _ _ _ _ _ _ _ _ (prologue_execute ops t s ht) he.1, he.2⟩

end FfnDown
#print axioms FfnDown.a_address
#print axioms FfnDown.b_address
#print axioms FfnDown.body_execute
#print axioms FfnDown.control_execute
#print axioms FfnDown.initialized_loop
#print axioms FfnDown.source_to_loop_exit
end LarkPtxMatrix
