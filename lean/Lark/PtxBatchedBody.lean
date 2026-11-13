import Lark.PtxBatchedInit

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/- Original 32-batch BMM source body development. No kernel certificate yet. -/
namespace LarkPtxBatched.Bmm.Body
open LarkNonlinear LarkPtxPointwise
open LarkPtxDot (Machine setPointer setIndex32 setFloat loadedHalf address
  aligned_address read_location loadHalf_step fromHalf_step binaryFloat_step
  loadedHalf_pc loadedHalf_stopped loadedHalf_pointer loadedHalf_memory
  setFloat_pc setFloat_pointer setFloat_memory)
open LarkPtxMatrix (Steps steps_trans one_step transition_at base_step)

def aCell (t c j : Nat) : Location := ⟨.global, 0, 0, aIndex t (16*c+j)⟩
def bCell (t c j : Nat) : Location := ⟨.global, 0, 1, bIndex t (16*c+j)⟩
def aPointer (t c : Nat) : Pointer := ⟨0, (((aIndex t 0+16*c)*2 : Nat) : Int), true⟩
def bPointer (t c : Nat) : Pointer := ⟨1, (((bIndex t 0+16*c*512)*2 : Nat) : Int), true⟩

theorem a_address (t c j : Nat) (ht : t < 1048576) (hc : c < 16) (hj : j < 16) :
    address layout geometry t (aPointer t c) ((2*j : Nat) : Int) false =
      some (aCell t c j) := by
  have bounds := input_indices_valid t (16*c+j) ht (by omega)
  have he : (((aIndex t 0+16*c)*2 : Nat) : Int)+((2*j : Nat) : Int) =
      ((aIndex t (16*c+j) : Nat) : Int)*2 := by
    simp only [aIndex, Int.natCast_add, Int.natCast_mul, Int.natCast_zero]; omega
  have hs : signed64 (((aIndex t (16*c+j) : Nat) : Int)*2) := by
    unfold signed64; omega
  unfold aPointer
  rw [aligned_address layout geometry t 0 (aIndex t (16*c+j)) _ _ false he hs]
  exact read_location layout geometry t 0 _ ⟨.input, 32*64*256⟩ (by rfl) bounds.1

theorem b_address (t c j : Nat) (ht : t < 1048576) (hc : c < 16) (hj : j < 16) :
    address layout geometry t (bPointer t c) ((1024*j : Nat) : Int) false =
      some (bCell t c j) := by
  have bounds := input_indices_valid t (16*c+j) ht (by omega)
  have he : (((bIndex t 0+16*c*512)*2 : Nat) : Int)+((1024*j : Nat) : Int) =
      ((bIndex t (16*c+j) : Nat) : Int)*2 := by
    simp only [bIndex, Int.natCast_add, Int.natCast_mul, Int.natCast_zero]; omega
  have hs : signed64 (((bIndex t (16*c+j) : Nat) : Int)*2) := by
    unfold signed64; omega
  unfold bPointer
  rw [aligned_address layout geometry t 1 (bIndex t (16*c+j)) _ _ false he hs]
  exact read_location layout geometry t 1 _ ⟨.input, 32*256*512⟩ (by rfl) bounds.2

def inputRegister (j : Nat) : Nat := if j = 0 then 68 else 2*j+35
def sumRegister (j : Nat) : Nat := if j = 15 then 68 else 2*j+37

def term (j : Nat) : List LarkPtxMatrix.Instruction :=
  [.base (.loadHalf (2*j+1) 12 ((2*j : Nat) : Int)),
   .base (.fromHalf (2*j+4) (2*j+1)),
   .base (.loadHalf (2*j+2) 13 ((1024*j : Nat) : Int)),
   .base (.fromHalf (2*j+5) (2*j+2)),
   .base (.binaryFloat (2*j+36) .mul (2*j+4) (2*j+5)),
   .base (.binaryFloat (sumRegister j) .add (inputRegister j) (2*j+36))]

theorem program_term : ∀ (j : Fin 15) (q : Fin 6),
    program[37+6*j.val+q.val]? = (term (j.val+1))[q.val]? := by decide

theorem step_in_term (ops : Ops α) (t j q : Nat) (hj : j < 16) (hq : q < 6) (hj0 : 0 < j)
    (s u : Machine α) (ins : LarkPtxDot.Instruction)
    (hpc : s.pc = 31+6*j+q) (hs : s.registers.stopped = false)
    (hi : (term j)[q]? = some (.base ins))
    (he : LarkPtxDot.execute ops layout geometry t ins s = some u) :
    Steps ops layout geometry t program s u := by
  have hf := program_term ⟨j-1, by omega⟩ ⟨q, hq⟩
  change program[37+6*(j-1)+q]? = (term ((j-1)+1))[q]? at hf
  have hj1 : j-1+1 = j := by omega
  have hpos : 37+6*(j-1)+q = 31+6*j+q := by omega
  rw [hj1, hpos, hi] at hf
  apply one_step
  rw [transition_at ops layout geometry t program s (.base ins) hs
    (by rw [hpc]; exact hf), base_step]
  exact he

def termLoadA (t c j : Nat) (a : α) (s : Machine α) : Machine α :=
  loadedHalf s t (2*j+1) (aCell t c j) a

def termCastA (ops : Ops α) (t c j : Nat) (a : α) (s : Machine α) : Machine α :=
  setFloat (termLoadA t c j a s) (2*j+4) (ops.fromHalf a)

def termLoadB (ops : Ops α) (t c j : Nat) (a b : α) (s : Machine α) : Machine α :=
  loadedHalf (termCastA ops t c j a s) t (2*j+2) (bCell t c j) b

def termCastB (ops : Ops α) (t c j : Nat) (a b : α) (s : Machine α) : Machine α :=
  setFloat (termLoadB ops t c j a b s) (2*j+5) (ops.fromHalf b)

def termProduct (ops : Ops α) (t c j : Nat) (a b : α) (s : Machine α) : Machine α :=
  setFloat (termCastB ops t c j a b s) (2*j+36) (ops.mul (ops.fromHalf a) (ops.fromHalf b))

def termResult (ops : Ops α) (t c j : Nat) (a b acc : α) (s : Machine α) : Machine α :=
  setFloat (termProduct ops t c j a b s) (sumRegister j)
    (ops.add acc (ops.mul (ops.fromHalf a) (ops.fromHalf b)))

theorem term_execute (ops : Ops α) (t c j : Nat) (a b acc : α) (s : Machine α)
    (ht : t < 1048576) (hc : c < 16) (hj : j < 16) (hj0 : 0 < j)
    (hpc : s.pc = 31 + 6*j) (hs : s.registers.stopped = false)
    (hpA : s.registers.pointer 12 = some (aPointer t c))
    (hpB : s.registers.pointer 13 = some (bPointer t c))
    (ha : s.registers.base.memory (aCell t c j) = some a)
    (hb : s.registers.base.memory (bCell t c j) = some b)
    (hacc : s.registers.scalar (inputRegister j) = some acc) :
    Steps ops layout geometry t program s (termResult ops t c j a b acc s) := by
  have h1 := step_in_term ops t j 0 hj (by decide) hj0 s (termLoadA t c j a s)
    (.loadHalf (2*j+1) 12 ((2*j : Nat) : Int))
    (by simpa only [Nat.add_zero] using hpc) hs (by rfl)
    (loadHalf_step ops layout geometry t (2*j+1) 12 _ s _ _ a hpA
      (a_address t c j ht hc hj) ha)
  have h2 := step_in_term ops t j 1 hj (by decide) hj0
    (termLoadA t c j a s) (termCastA ops t c j a s) (.fromHalf (2*j+4) (2*j+1))
    (by simp only [termLoadA, loadedHalf_pc]; omega)
    (by change s.registers.stopped = false; exact hs) (by rfl)
    (fromHalf_step ops layout geometry t (2*j+4) (2*j+1) _ a
      (by simp [termLoadA]))
  have h3 := step_in_term ops t j 2 hj (by decide) hj0
    (termCastA ops t c j a s) (termLoadB ops t c j a b s)
    (.loadHalf (2*j+2) 13 ((1024*j : Nat) : Int))
    (by simp only [termCastA, termLoadA, setFloat_pc, loadedHalf_pc]; omega)
    (by change s.registers.stopped = false; exact hs) (by rfl)
    (loadHalf_step ops layout geometry t (2*j+2) 13 _ _ _ _ b
      (by simpa only [termCastA, termLoadA, setFloat_pointer, loadedHalf_pointer] using hpB)
      (b_address t c j ht hc hj)
      (by simpa only [termCastA, termLoadA, setFloat_memory, loadedHalf_memory] using hb))
  have h4 := step_in_term ops t j 3 hj (by decide) hj0
    (termLoadB ops t c j a b s) (termCastB ops t c j a b s) (.fromHalf (2*j+5) (2*j+2))
    (by simp only [termLoadB, termCastA, termLoadA, setFloat_pc, loadedHalf_pc]; omega)
    (by change s.registers.stopped = false; exact hs) (by rfl)
    (fromHalf_step ops layout geometry t (2*j+5) (2*j+2) _ b
      (by simp [termLoadB]))
  have hrAB : 2*j+4 ≠ 2*j+5 := by omega
  have h5 := step_in_term ops t j 4 hj (by decide) hj0
    (termCastB ops t c j a b s) (termProduct ops t c j a b s)
    (.binaryFloat (2*j+36) .mul (2*j+4) (2*j+5))
    (by simp only [termCastB, termLoadB, termCastA, termLoadA, setFloat_pc, loadedHalf_pc]; omega)
    (by change s.registers.stopped = false; exact hs) (by rfl)
    (binaryFloat_step ops layout geometry t (2*j+36) (2*j+4) (2*j+5) .mul _ _ _
      (by simp [termCastB, termLoadB, termCastA, hrAB])
      (by simp [termCastB]))
  have hrA : inputRegister j ≠ 2*j+4 := by unfold inputRegister; split <;> omega
  have hrB : inputRegister j ≠ 2*j+5 := by unfold inputRegister; split <;> omega
  have hrP : inputRegister j ≠ 2*j+36 := by unfold inputRegister; split <;> omega
  have h6 := step_in_term ops t j 5 hj (by decide) hj0
    (termProduct ops t c j a b s) (termResult ops t c j a b acc s)
    (.binaryFloat (sumRegister j) .add (inputRegister j) (2*j+36))
    (by simp only [termProduct, termCastB, termLoadB, termCastA, termLoadA, setFloat_pc, loadedHalf_pc]; omega)
    (by change s.registers.stopped = false; exact hs) (by rfl)
    (binaryFloat_step ops layout geometry t (sumRegister j) (inputRegister j) (2*j+36) .add _ _ _
      (by simp [termProduct, termCastB, termLoadB, termCastA, termLoadA, hrA, hrB, hrP, hacc])
      (by simp [termProduct]))
  apply steps_trans _ _ _ _ _ _ _ _ h1
  apply steps_trans _ _ _ _ _ _ _ _ h2
  apply steps_trans _ _ _ _ _ _ _ _ h3
  apply steps_trans _ _ _ _ _ _ _ _ h4
  exact steps_trans _ _ _ _ _ _ _ _ h5 h6

theorem termResult_pc (ops : Ops α) (t c j : Nat) (a b acc : α) (s : Machine α) :
    (termResult ops t c j a b acc s).pc = s.pc + 6 := by
  simp only [termResult, termProduct, termCastB, termLoadB, termCastA, termLoadA,
    setFloat_pc, loadedHalf_pc]

theorem termResult_pointer (ops : Ops α) (t c j r : Nat) (a b acc : α) (s : Machine α) :
    (termResult ops t c j a b acc s).registers.pointer r = s.registers.pointer r := rfl

theorem termResult_memory (ops : Ops α) (t c j : Nat) (a b acc : α) (s : Machine α) :
    (termResult ops t c j a b acc s).registers.base.memory = s.registers.base.memory := rfl

theorem termResult_scalar (ops : Ops α) (t c j : Nat) (a b acc : α) (s : Machine α) :
    (termResult ops t c j a b acc s).registers.scalar (sumRegister j) =
      some (ops.add acc (ops.mul (ops.fromHalf a) (ops.fromHalf b))) := by
  simp [termResult]


theorem termResult_stopped (ops : Ops α) (t c j : Nat) (a b acc : α) (s : Machine α) :
    (termResult ops t c j a b acc s).registers.stopped = s.registers.stopped := rfl

theorem termResult_i32 (ops : Ops α) (t c j r : Nat) (a b acc : α) (s : Machine α) :
    (termResult ops t c j a b acc s).registers.i32 r = s.registers.i32 r := rfl

theorem termResult_i64 (ops : Ops α) (t c j r : Nat) (a b acc : α) (s : Machine α) :
    (termResult ops t c j a b acc s).registers.i64 r = s.registers.i64 r := rfl

def accumulatorRegister (j : Nat) : Nat := if j = 0 ∨ j = 16 then 68 else 2*j+35

theorem source_accumulator : ∀ j : Fin 16,
    inputRegister j.val = accumulatorRegister j.val ∧
    sumRegister j.val = accumulatorRegister (j.val+1) := by decide

def Reads (input : Nat → Nat → α) (s : Machine α) : Prop :=
  (∀ i, i < 32*64*256 → s.registers.base.memory ⟨.global, 0, 0, i⟩ = some (input 0 i)) ∧
  (∀ i, i < 32*256*512 → s.registers.base.memory ⟨.global, 0, 1, i⟩ = some (input 1 i))

def aBase (c : Nat) : Pointer := ⟨0, ((32*c : Nat) : Int), true⟩
def bBase (c : Nat) : Pointer := ⟨1, ((16384*c : Nat) : Int), true⟩

structure BodyInvariant (input : Nat → Nat → α) (t c j : Nat) (acc : α) (s : Machine α) : Prop where
  pc : s.pc = 31+6*j
  stopped : s.registers.stopped = false
  a : s.registers.pointer 12 = some (aPointer t c)
  b : s.registers.pointer 13 = some (bPointer t c)
  accumulator : s.registers.scalar (accumulatorRegister j) = some acc
  reads : Reads input s
  thread : s.registers.i32 1 = some (t : Int)
  counter : s.registers.i32 24 = some ((16*c : Nat) : Int)
  output : s.registers.pointer 9 = some ⟨2, 0, false⟩
  abase : s.registers.pointer 17 = some (aBase c)
  bbase : s.registers.pointer 18 = some (bBase c)
  aoffset : s.registers.i64 4 = some (((aIndex t 0 : Nat) : Int)*2)
  boffset : s.registers.i64 3 = some (((bIndex t 0 : Nat) : Int)*2)

def nextValue (ops : Ops α) (input : Nat → Nat → α) (t c j : Nat) (acc : α) : α :=
  ops.add acc (ops.mul (ops.fromHalf (input 0 (aIndex t (16*c+j))))
    (ops.fromHalf (input 1 (bIndex t (16*c+j)))))

def chunkStep (ops : Ops α) (input : Nat → Nat → α) (t c j : Nat) (acc : α)
    (s : Machine α) : Machine α :=
  termResult ops t c j (input 0 (aIndex t (16*c+j))) (input 1 (bIndex t (16*c+j))) acc s

theorem chunk_step (ops : Ops α) (input : Nat → Nat → α) (t c j : Nat) (acc : α)
    (s : Machine α) (ht : t < 1048576) (hc : c < 16) (hj : j < 16) (hj0 : 0 < j)
    (h : BodyInvariant input t c j acc s) :
    Steps ops layout geometry t program s (chunkStep ops input t c j acc s) ∧
    BodyInvariant input t c (j+1) (nextValue ops input t c j acc) (chunkStep ops input t c j acc s) := by
  have bounds := input_indices_valid t (16*c+j) ht (by omega)
  have hreg := source_accumulator ⟨j, hj⟩
  have ex := term_execute ops t c j _ _ acc s ht hc hj hj0 h.pc h.stopped h.a h.b
    (h.reads.1 _ bounds.1) (h.reads.2 _ bounds.2) (by rw [hreg.1]; exact h.accumulator)
  refine ⟨ex, ?_⟩
  constructor
  · rw [chunkStep, termResult_pc, h.pc]; omega
  · simpa only [chunkStep, termResult_stopped] using h.stopped
  · simpa only [chunkStep, termResult_pointer] using h.a
  · simpa only [chunkStep, termResult_pointer] using h.b
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
  · simpa only [chunkStep, termResult_pointer] using h.output
  · simpa only [chunkStep, termResult_pointer] using h.abase
  · simpa only [chunkStep, termResult_pointer] using h.bbase
  · simpa only [chunkStep, termResult_i64] using h.aoffset
  · simpa only [chunkStep, termResult_i64] using h.boffset

def foldTerms (ops : Ops α) (input : Nat → Nat → α) (t c j : Nat) : Nat → α → α
  | 0, acc => acc
  | n+1, acc => foldTerms ops input t c (j+1) n (nextValue ops input t c j acc)

def runTerms (ops : Ops α) (input : Nat → Nat → α) (t c j : Nat) : Nat → α → Machine α → Machine α
  | 0, _, s => s
  | n+1, acc, s => runTerms ops input t c (j+1) n (nextValue ops input t c j acc)
      (chunkStep ops input t c j acc s)

theorem runTerms_execute (ops : Ops α) (input : Nat → Nat → α) (t c j n : Nat) (acc : α)
    (s : Machine α) (ht : t < 1048576) (hc : c < 16) (hj0 : 0 < j) (hjn : j+n ≤ 16)
    (h : BodyInvariant input t c j acc s) :
    Steps ops layout geometry t program s (runTerms ops input t c j n acc s) ∧
    BodyInvariant input t c (j+n) (foldTerms ops input t c j n acc) (runTerms ops input t c j n acc s) := by
  induction n generalizing j acc s with
  | zero => exact ⟨.refl _, h⟩
  | succ n ih =>
      have head := chunk_step ops input t c j acc s ht hc (by omega) hj0 h
      have tail := ih (j+1) (nextValue ops input t c j acc) (chunkStep ops input t c j acc s)
        (by omega) (by omega) head.2
      refine ⟨steps_trans _ _ _ _ _ _ _ _ head.1 tail.1, ?_⟩
      have he : j+(n+1) = (j+1)+n := by omega
      rw [he]
      exact tail.2

structure LoopInvariant (input : Nat → Nat → α) (t c : Nat) (acc : α) (s : Machine α) : Prop where
  pc : s.pc = if c < 16 then 29 else 132
  stopped : s.registers.stopped = false
  a : s.registers.pointer 17 = some (aBase c)
  b : s.registers.pointer 18 = some (bBase c)
  accumulator : s.registers.scalar 68 = some acc
  reads : Reads input s
  thread : s.registers.i32 1 = some (t : Int)
  counter : s.registers.i32 24 = some ((16*c : Nat) : Int)
  output : s.registers.pointer 9 = some ⟨2, 0, false⟩
  aoffset : s.registers.i64 4 = some (((aIndex t 0 : Nat) : Int)*2)
  boffset : s.registers.i64 3 = some (((bIndex t 0 : Nat) : Int)*2)

def firstAddressA (t c : Nat) (s : Machine α) : Machine α := setPointer s 12 (aPointer t c)
def firstLoadA (t c : Nat) (a : α) (s : Machine α) : Machine α :=
  loadedHalf (firstAddressA t c s) t 1 (aCell t c 0) a
def firstCastA (ops : Ops α) (t c : Nat) (a : α) (s : Machine α) : Machine α :=
  setFloat (firstLoadA t c a s) 4 (ops.fromHalf a)
def firstAddressB (ops : Ops α) (t c : Nat) (a : α) (s : Machine α) : Machine α :=
  setPointer (firstCastA ops t c a s) 13 (bPointer t c)
def firstLoadB (ops : Ops α) (t c : Nat) (a b : α) (s : Machine α) : Machine α :=
  loadedHalf (firstAddressB ops t c a s) t 2 (bCell t c 0) b
def firstCastB (ops : Ops α) (t c : Nat) (a b : α) (s : Machine α) : Machine α :=
  setFloat (firstLoadB ops t c a b s) 5 (ops.fromHalf b)
def firstProduct (ops : Ops α) (t c : Nat) (a b : α) (s : Machine α) : Machine α :=
  setFloat (firstCastB ops t c a b s) 36 (ops.mul (ops.fromHalf a) (ops.fromHalf b))
def firstResult (ops : Ops α) (t c : Nat) (a b acc : α) (s : Machine α) : Machine α :=
  setFloat (firstProduct ops t c a b s) 37
    (ops.add acc (ops.mul (ops.fromHalf a) (ops.fromHalf b)))

theorem firstResult_pc (ops : Ops α) (t c : Nat) (a b acc : α) (s : Machine α) :
    (firstResult ops t c a b acc s).pc = s.pc+8 := by
  simp only [firstResult, firstProduct, firstCastB, firstLoadB, firstAddressB, firstCastA,
    firstLoadA, firstAddressA, setFloat_pc, loadedHalf_pc, LarkPtxDot.setPointer_pc]

theorem firstResult_stopped (ops : Ops α) (t c : Nat) (a b acc : α) (s : Machine α) :
    (firstResult ops t c a b acc s).registers.stopped = s.registers.stopped := rfl

theorem firstResult_i32 (ops : Ops α) (t c r : Nat) (a b acc : α) (s : Machine α) :
    (firstResult ops t c a b acc s).registers.i32 r = s.registers.i32 r := rfl

theorem firstResult_pointer (ops : Ops α) (t c r : Nat) (a b acc : α) (s : Machine α) :
    (firstResult ops t c a b acc s).registers.pointer r =
      if r = 13 then some (bPointer t c) else if r = 12 then some (aPointer t c)
      else s.registers.pointer r := by
  simp only [firstResult, firstProduct, firstCastB, firstLoadB, firstAddressB, firstCastA,
    firstLoadA, firstAddressA, setFloat_pointer, loadedHalf_pointer, LarkPtxDot.setPointer_pointer]

theorem firstResult_i64 (ops : Ops α) (t c r : Nat) (a b acc : α) (s : Machine α) :
    (firstResult ops t c a b acc s).registers.i64 r =
      if r = 13 then none else if r = 12 then none else s.registers.i64 r := by
  simp only [firstResult, firstProduct, firstCastB, firstLoadB, firstAddressB, firstCastA,
    firstLoadA, firstAddressA, LarkPtxMatrix.setFloat_i64, LarkPtxMatrix.loadedHalf_i64,
    LarkPtxMatrix.setPointer_i64]

theorem firstResult_memory (ops : Ops α) (t c : Nat) (a b acc : α) (s : Machine α) :
    (firstResult ops t c a b acc s).registers.base.memory = s.registers.base.memory := rfl

theorem firstResult_scalar (ops : Ops α) (t c : Nat) (a b acc : α) (s : Machine α) :
    (firstResult ops t c a b acc s).registers.scalar 37 =
      some (ops.add acc (ops.mul (ops.fromHalf a) (ops.fromHalf b))) := by simp [firstResult]

theorem first_execute (ops : Ops α) (input : Nat → Nat → α) (t c : Nat) (acc : α)
    (s : Machine α) (ht : t < 1048576) (hc : c < 16) (h : LoopInvariant input t c acc s) :
    Steps ops layout geometry t program s
      (firstResult ops t c (input 0 (aIndex t (16*c))) (input 1 (bIndex t (16*c))) acc s) := by
  let a := input 0 (aIndex t (16*c))
  let b := input 1 (bIndex t (16*c))
  have hpc : s.pc = 29 := by simpa only [if_pos hc] using h.pc
  have bounds := input_indices_valid t (16*c) ht (by omega)
  have basebounds := input_indices_valid t 0 ht (by decide)
  have ha : signed64 (((aIndex t 0 : Nat) : Int)*2) ∧
      signed64 ((aBase c).offset+((aIndex t 0 : Nat) : Int)*2) := by
    unfold signed64 aBase; simp only [Int.natCast_mul]; omega
  have ea := LarkPtxDot.pointer_add_step ops layout geometry t 12 17 (.reg 4) (aBase c)
    (((aIndex t 0 : Nat) : Int)*2) s (LarkPtxDot.pointer_values _ _ _ h.a) h.aoffset ha
  have epa : { aBase c with offset := (aBase c).offset+((aIndex t 0 : Nat) : Int)*2 } =
      aPointer t c := by
    have he : ((32*c : Nat) : Int)+((aIndex t 0 : Nat) : Int)*2 =
        (((aIndex t 0+16*c)*2 : Nat) : Int) := by
      simp only [Int.natCast_add, Int.natCast_mul]; omega
    simp only [aBase, aPointer, he]
  rw [epa] at ea
  have h1 := Init.instruction_step ops t 29 s (firstAddressA t c s)
    (.base (.addSigned64 12 17 (.reg 4))) hpc h.stopped (by rfl) ea
  have h2 := Init.instruction_step ops t 30 (firstAddressA t c s) (firstLoadA t c a s)
    (.base (.loadHalf 1 12 0))
    (by change s.pc+1 = 30; omega) (by exact h.stopped) (by rfl)
    (loadHalf_step ops layout geometry t 1 12 0 _ _ _ a
      (by simp [firstAddressA]) (a_address t c 0 ht hc (by decide))
      (by simpa only [firstAddressA, LarkPtxMatrix.setPointer_base, aCell, Nat.add_zero]
        using h.reads.1 _ bounds.1))
  have h3 := Init.instruction_step ops t 31 (firstLoadA t c a s) (firstCastA ops t c a s)
    (.base (.fromHalf 4 1))
    (by change s.pc+1+1 = 31; omega) (by exact h.stopped) (by rfl)
    (fromHalf_step ops layout geometry t 4 1 _ a (by simp [firstLoadA]))
  have hpB : (firstCastA ops t c a s).registers.values (.int64 18) = some (.address (bBase c)) := by
    apply LarkPtxDot.pointer_values
    simpa [firstCastA, firstLoadA, firstAddressA] using h.b
  have hoB : LarkPtxDot.operand64 (firstCastA ops t c a s).registers (.reg 3) =
      some (((bIndex t 0 : Nat) : Int)*2) := by
    simpa [LarkPtxDot.operand64, firstCastA, firstLoadA, firstAddressA] using h.boffset
  have hb : signed64 (((bIndex t 0 : Nat) : Int)*2) ∧
      signed64 ((bBase c).offset+((bIndex t 0 : Nat) : Int)*2) := by
    unfold signed64 bBase; simp only [Int.natCast_mul]; omega
  have eb := LarkPtxDot.pointer_add_step ops layout geometry t 13 18 (.reg 3) (bBase c)
    (((bIndex t 0 : Nat) : Int)*2) (firstCastA ops t c a s) hpB hoB hb
  have epb : { bBase c with offset := (bBase c).offset+((bIndex t 0 : Nat) : Int)*2 } =
      bPointer t c := by
    have he : ((16384*c : Nat) : Int)+((bIndex t 0 : Nat) : Int)*2 =
        (((bIndex t 0+16*c*512)*2 : Nat) : Int) := by
      simp only [Int.natCast_add, Int.natCast_mul]; omega
    simp only [bBase, bPointer, he]
  rw [epb] at eb
  have h4 := Init.instruction_step ops t 32 (firstCastA ops t c a s) (firstAddressB ops t c a s)
    (.base (.addSigned64 13 18 (.reg 3)))
    (by change s.pc+1+1+1 = 32; omega) (by exact h.stopped) (by rfl) eb
  have h5 := Init.instruction_step ops t 33 (firstAddressB ops t c a s) (firstLoadB ops t c a b s)
    (.base (.loadHalf 2 13 0))
    (by change s.pc+1+1+1+1 = 33; omega) (by exact h.stopped) (by rfl)
    (loadHalf_step ops layout geometry t 2 13 0 _ _ _ b
      (by simp [firstAddressB]) (b_address t c 0 ht hc (by decide))
      (by simpa only [firstAddressB, firstCastA, firstLoadA, firstAddressA, bCell, Nat.add_zero,
        LarkPtxMatrix.setPointer_base, setFloat_memory, loadedHalf_memory] using h.reads.2 _ bounds.2))
  have h6 := Init.instruction_step ops t 34 (firstLoadB ops t c a b s) (firstCastB ops t c a b s)
    (.base (.fromHalf 5 2))
    (by change s.pc+1+1+1+1+1 = 34; omega) (by exact h.stopped) (by rfl)
    (fromHalf_step ops layout geometry t 5 2 _ b (by simp [firstLoadB]))
  have h7 := Init.instruction_step ops t 35 (firstCastB ops t c a b s) (firstProduct ops t c a b s)
    (.base (.binaryFloat 36 .mul 4 5))
    (by change s.pc+1+1+1+1+1+1 = 35; omega) (by exact h.stopped) (by rfl)
    (binaryFloat_step ops layout geometry t 36 4 5 .mul _ _ _
      (by simp [firstCastB, firstLoadB, firstAddressB, firstCastA])
      (by simp [firstCastB]))
  have h8 := Init.instruction_step ops t 36 (firstProduct ops t c a b s) (firstResult ops t c a b acc s)
    (.base (.binaryFloat 37 .add 68 36))
    (by change s.pc+1+1+1+1+1+1+1 = 36; omega) (by exact h.stopped) (by rfl)
    (binaryFloat_step ops layout geometry t 37 68 36 .add _ _ _
      (by simpa [firstProduct, firstCastB, firstLoadB, firstAddressB, firstCastA, firstLoadA,
        firstAddressA] using h.accumulator) (by simp [firstProduct]))
  exact steps_trans _ _ _ _ _ _ _ _ h1
    (steps_trans _ _ _ _ _ _ _ _ h2
      (steps_trans _ _ _ _ _ _ _ _ h3
        (steps_trans _ _ _ _ _ _ _ _ h4
          (steps_trans _ _ _ _ _ _ _ _ h5
            (steps_trans _ _ _ _ _ _ _ _ h6 (steps_trans _ _ _ _ _ _ _ _ h7 h8))))))

def firstChunk (ops : Ops α) (input : Nat → Nat → α) (t c : Nat) (acc : α)
    (s : Machine α) : Machine α :=
  firstResult ops t c (input 0 (aIndex t (16*c))) (input 1 (bIndex t (16*c))) acc s

theorem first_invariant (ops : Ops α) (input : Nat → Nat → α) (t c : Nat) (acc : α)
    (s : Machine α) (hc : c < 16) (h : LoopInvariant input t c acc s) :
    BodyInvariant input t c 1 (nextValue ops input t c 0 acc) (firstChunk ops input t c acc s) := by
  have hpc : s.pc = 29 := by simpa only [if_pos hc] using h.pc
  constructor
  · rw [firstChunk, firstResult_pc, hpc]
  · simpa only [firstChunk, firstResult_stopped] using h.stopped
  · simp [firstChunk, firstResult_pointer]
  · simp [firstChunk, firstResult_pointer]
  · simpa [firstChunk, accumulatorRegister, nextValue] using
      firstResult_scalar ops t c (input 0 (aIndex t (16*c))) (input 1 (bIndex t (16*c))) acc s
  · constructor
    · intro i hi
      rw [firstChunk, firstResult_memory]
      exact h.reads.1 i hi
    · intro i hi
      rw [firstChunk, firstResult_memory]
      exact h.reads.2 i hi
  · simpa only [firstChunk, firstResult_i32] using h.thread
  · simpa only [firstChunk, firstResult_i32] using h.counter
  · simpa only [firstChunk, firstResult_pointer, if_neg (by decide : 9 ≠ 13),
      if_neg (by decide : 9 ≠ 12)] using h.output
  · simpa only [firstChunk, firstResult_pointer, if_neg (by decide : 17 ≠ 13),
      if_neg (by decide : 17 ≠ 12)] using h.a
  · simpa only [firstChunk, firstResult_pointer, if_neg (by decide : 18 ≠ 13),
      if_neg (by decide : 18 ≠ 12)] using h.b
  · simpa only [firstChunk, firstResult_i64, if_neg (by decide : 4 ≠ 13),
      if_neg (by decide : 4 ≠ 12)] using h.aoffset
  · simpa only [firstChunk, firstResult_i64, if_neg (by decide : 3 ≠ 13),
      if_neg (by decide : 3 ≠ 12)] using h.boffset

def chunkValue (ops : Ops α) (input : Nat → Nat → α) (t c : Nat) (acc : α) : α :=
  foldTerms ops input t c 1 15 (nextValue ops input t c 0 acc)

def bodyEnd (ops : Ops α) (input : Nat → Nat → α) (t c : Nat) (acc : α)
    (s : Machine α) : Machine α :=
  runTerms ops input t c 1 15 (nextValue ops input t c 0 acc) (firstChunk ops input t c acc s)

theorem body_execute (ops : Ops α) (input : Nat → Nat → α) (t c : Nat) (acc : α)
    (s : Machine α) (ht : t < 1048576) (hc : c < 16) (h : LoopInvariant input t c acc s) :
    Steps ops layout geometry t program s (bodyEnd ops input t c acc s) ∧
    BodyInvariant input t c 16 (chunkValue ops input t c acc) (bodyEnd ops input t c acc s) := by
  have head := first_execute ops input t c acc s ht hc h
  have invariant := first_invariant ops input t c acc s hc h
  have tail := runTerms_execute ops input t c 1 15 (nextValue ops input t c 0 acc)
    (firstChunk ops input t c acc s) ht hc (by decide) (by decide) invariant
  exact ⟨steps_trans _ _ _ _ _ _ _ _ head tail.1, tail.2⟩

theorem initial_loop (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (base : State α)
    (s : Machine α) (h : Init.Ready ops t base s) (hreads : Reads input (start base)) :
    LoopInvariant input t 0 (ops.literal 0 1) s := by
  constructor
  · simpa using h.pc
  · exact h.frame.active
  · exact h.frame.a
  · exact h.frame.b
  · exact h.accumulator
  · constructor
    · intro i hi
      change s.registers.base.memory _ = _
      rw [h.frame.memory]
      exact hreads.1 i hi
    · intro i hi
      change s.registers.base.memory _ = _
      rw [h.frame.memory]
      exact hreads.2 i hi
  · exact h.frame.index
  · exact h.counter
  · exact h.frame.out
  · exact h.aOffset
  · exact h.bOffset

end LarkPtxBatched.Bmm.Body

#print axioms LarkPtxBatched.Bmm.Body.a_address
#print axioms LarkPtxBatched.Bmm.Body.b_address
#print axioms LarkPtxBatched.Bmm.Body.program_term
#print axioms LarkPtxBatched.Bmm.Body.term_execute
#print axioms LarkPtxBatched.Bmm.Body.termResult_pc
#print axioms LarkPtxBatched.Bmm.Body.termResult_pointer
#print axioms LarkPtxBatched.Bmm.Body.termResult_memory
#print axioms LarkPtxBatched.Bmm.Body.termResult_scalar
#print axioms LarkPtxBatched.Bmm.Body.termResult_stopped
#print axioms LarkPtxBatched.Bmm.Body.termResult_i32
#print axioms LarkPtxBatched.Bmm.Body.termResult_i64
#print axioms LarkPtxBatched.Bmm.Body.source_accumulator
#print axioms LarkPtxBatched.Bmm.Body.chunk_step
#print axioms LarkPtxBatched.Bmm.Body.runTerms_execute
#print axioms LarkPtxBatched.Bmm.Body.firstResult_pc
#print axioms LarkPtxBatched.Bmm.Body.firstResult_stopped
#print axioms LarkPtxBatched.Bmm.Body.firstResult_i32
#print axioms LarkPtxBatched.Bmm.Body.firstResult_pointer
#print axioms LarkPtxBatched.Bmm.Body.firstResult_i64
#print axioms LarkPtxBatched.Bmm.Body.firstResult_memory
#print axioms LarkPtxBatched.Bmm.Body.firstResult_scalar
#print axioms LarkPtxBatched.Bmm.Body.first_execute
#print axioms LarkPtxBatched.Bmm.Body.first_invariant
#print axioms LarkPtxBatched.Bmm.Body.body_execute
#print axioms LarkPtxBatched.Bmm.Body.initial_loop
