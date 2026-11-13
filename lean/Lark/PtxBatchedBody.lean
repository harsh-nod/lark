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

open LarkPtxDot (pointer_add_step pointer_values add32_step compare_ne_step setPredicate
  setPointer_pc setIndex32_pc setPredicate_pc)
open LarkPtxMatrix (setPointer_stopped setPointer_i32 setPredicate_registers setIndex32_i64 setPointer_i64)

def bAdvanced (c : Nat) (s : Machine α) : Machine α := setPointer s 18 (bBase (c+1))
def aAdvanced (c : Nat) (s : Machine α) : Machine α := setPointer (bAdvanced c s) 17 (aBase (c+1))
def counted (c : Nat) (s : Machine α) : Machine α :=
  setIndex32 (aAdvanced c s) 24 ((16*(c+1) : Nat) : Int)
def compared (c : Nat) (s : Machine α) : Machine α :=
  setPredicate (counted c s) 1 (((16*(c+1) : Nat) : Int) != (256 : Int))
def controlResult (c : Nat) (s : Machine α) : Machine α :=
  let next := compared c s
  { next with pc := if (((16*(c+1) : Nat) : Int) != (256 : Int)) then 29 else next.pc+1 }

theorem control_execute (ops : Ops α) (input : Nat → Nat → α) (t c : Nat) (acc : α)
    (s : Machine α) (hc : c < 16) (h : BodyInvariant input t c 16 acc s) :
    Steps ops layout geometry t program s (controlResult c s) := by
  have hpc : s.pc = 127 := h.pc
  have hb : signed64 16384 ∧ signed64 ((bBase c).offset+16384) := by
    unfold signed64 bBase; simp only [Int.natCast_mul]; omega
  have e1 := pointer_add_step ops layout geometry t 18 18 (.imm 16384) (bBase c) 16384 s
    (pointer_values _ _ _ h.bbase) (by rfl) hb
  have heB : { bBase c with offset := (bBase c).offset+16384 } = bBase (c+1) := by
    have he : ((16384*c : Nat) : Int)+16384 = ((16384*(c+1) : Nat) : Int) := by
      simp only [Int.natCast_add, Int.natCast_mul]; omega
    simp only [bBase, he]
  rw [heB] at e1
  have h1 : Steps ops layout geometry t program s (bAdvanced c s) := by
    apply one_step
    rw [transition_at ops layout geometry t program s (.base (.addSigned64 18 18 (.imm 16384)))
      h.stopped (by rw [hpc]; rfl), base_step]
    exact e1
  have ha : signed64 32 ∧ signed64 ((aBase c).offset+32) := by
    unfold signed64 aBase; simp only [Int.natCast_mul]; omega
  have hpA : (bAdvanced c s).registers.values (.int64 17) = some (.address (aBase c)) := by
    apply pointer_values
    simpa [bAdvanced] using h.abase
  have e2 := pointer_add_step ops layout geometry t 17 17 (.imm 32) (aBase c) 32 (bAdvanced c s)
    hpA (by rfl) ha
  have heA : { aBase c with offset := (aBase c).offset+32 } = aBase (c+1) := by
    have he : ((32*c : Nat) : Int)+32 = ((32*(c+1) : Nat) : Int) := by
      simp only [Int.natCast_add, Int.natCast_mul]; omega
    simp only [aBase, he]
  rw [heA] at e2
  have h2 : Steps ops layout geometry t program (bAdvanced c s) (aAdvanced c s) := by
    apply one_step
    rw [transition_at ops layout geometry t program (bAdvanced c s) (.base (.addSigned64 17 17 (.imm 32)))
      (by simpa only [bAdvanced, setPointer_stopped] using h.stopped)
      (by simp only [bAdvanced, setPointer_pc, hpc]; rfl), base_step]
    exact e2
  have hg : signed32 ((16*c : Nat) : Int) ∧ signed32 16 ∧
      signed32 (((16*c : Nat) : Int)+16) := by
    unfold signed32; simp only [Int.natCast_mul]; omega
  have hx : (aAdvanced c s).registers.i32 24 = some ((16*c : Nat) : Int) := by
    simpa only [aAdvanced, bAdvanced, setPointer_i32] using h.counter
  have e3 := add32_step ops layout geometry t 24 24 (.imm 16) (aAdvanced c s)
    ((16*c : Nat) : Int) 16 hx (by rfl) hg
  have heC : ((16*c : Nat) : Int)+16 = ((16*(c+1) : Nat) : Int) := by
    simp only [Int.natCast_add, Int.natCast_mul]; omega
  rw [heC] at e3
  have h3 : Steps ops layout geometry t program (aAdvanced c s) (counted c s) := by
    apply one_step
    rw [transition_at ops layout geometry t program (aAdvanced c s) (.base (.addSigned32 24 24 (.imm 16)))
      (by simpa only [aAdvanced, bAdvanced, setPointer_stopped] using h.stopped)
      (by simp only [aAdvanced, bAdvanced, setPointer_pc, hpc]; rfl), base_step]
    exact e3
  have hp : signed32 ((16*(c+1) : Nat) : Int) ∧ signed32 256 := by
    unfold signed32; simp only [Int.natCast_add, Int.natCast_mul]; omega
  have e4 := compare_ne_step ops layout geometry t 1 24 (.imm 256) (counted c s)
    ((16*(c+1) : Nat) : Int) 256 (by simp [counted]) (by rfl) hp
  have h4 : Steps ops layout geometry t program (counted c s) (compared c s) := by
    apply one_step
    rw [transition_at ops layout geometry t program (counted c s) (.base (.compareNeSigned32 1 24 (.imm 256)))
      (by change s.registers.stopped = false; exact h.stopped)
      (by simp only [counted, aAdvanced, bAdvanced, setIndex32_pc, setPointer_pc, hpc]; rfl), base_step]
    exact e4
  have h5 : Steps ops layout geometry t program (compared c s) (controlResult c s) := by
    apply one_step
    rw [transition_at ops layout geometry t program (compared c s) (.base (.branch 1 29))
      (by change s.registers.stopped = false; exact h.stopped)
      (by simp only [compared, counted, aAdvanced, bAdvanced, setPredicate_pc,
        setIndex32_pc, setPointer_pc, hpc]; rfl), base_step]
    simp only [LarkPtxDot.execute, compared, setPredicate, bind, pure, Option.bind]
    rfl
  apply steps_trans _ _ _ _ _ _ _ _ h1
  apply steps_trans _ _ _ _ _ _ _ _ h2
  apply steps_trans _ _ _ _ _ _ _ _ h3
  exact steps_trans _ _ _ _ _ _ _ _ h4 h5

theorem control_pc (c : Nat) (s : Machine α) (hc : c < 16) (hpc : s.pc = 127) :
    (controlResult c s).pc = if c+1 < 16 then 29 else 132 := by
  by_cases hn : c+1 < 16
  · have hne : (16 : Int)*((c : Int)+1) ≠ 256 := by omega
    simp [controlResult, hne, hn]
  · have he : c+1 = 16 := by omega
    simp [controlResult, compared, counted, aAdvanced, bAdvanced, he, hn, hpc]

theorem control_memory (c : Nat) (s : Machine α) :
    (controlResult c s).registers.base.memory = s.registers.base.memory := rfl

theorem control_i64 (c r : Nat) (s : Machine α) :
    (controlResult c s).registers.i64 r = if r = 17 then none else if r = 18 then none else s.registers.i64 r := by
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
  · change s.registers.scalar 68 = some acc
    simpa only [accumulatorRegister, if_pos (by decide : 16 = 0 ∨ 16 = 16)] using h.accumulator
  · change Reads input s
    exact h.reads
  · change s.registers.i32 1 = some (t : Int)
    exact h.thread
  · rfl
  · change s.registers.pointer 9 = some ⟨2, 0, false⟩
    exact h.output
  · rw [control_i64, if_neg (by decide : 4 ≠ 17), if_neg (by decide : 4 ≠ 18)]
    exact h.aoffset
  · rw [control_i64, if_neg (by decide : 3 ≠ 17), if_neg (by decide : 3 ≠ 18)]
    exact h.boffset

def iteration (ops : Ops α) (input : Nat → Nat → α) (t c : Nat) (acc : α) (s : Machine α) : Machine α :=
  controlResult c (bodyEnd ops input t c acc s)

theorem iteration_execute (ops : Ops α) (input : Nat → Nat → α) (t c : Nat) (acc : α)
    (s : Machine α) (ht : t < 1048576) (hc : c < 16) (h : LoopInvariant input t c acc s) :
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
    (s : Machine α) (ht : t < 1048576) (hcn : c+n ≤ 16) (h : LoopInvariant input t c acc s) :
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

open LarkPtxDot (setHalf storedHalf returned global_step half_step wide_step store_step return_step operand64)
open LarkPtxMatrix (setIndex64 setIndex64_i64 setPointer_scalar)

def outputCell (t : Nat) : Location := ⟨.global, 0, 2, t⟩
def exitGlobal (s : Machine α) : Machine α := setPointer s 14 ⟨2, 0, true⟩
def exitHalf (ops : Ops α) (acc : α) (s : Machine α) : Machine α :=
  setHalf (exitGlobal s) 33 (ops.toHalf acc)
def exitWide (ops : Ops α) (t : Nat) (acc : α) (s : Machine α) : Machine α :=
  setIndex64 (exitHalf ops acc s) 15 ((t*2 : Nat) : Int)
def exitAddress (ops : Ops α) (t : Nat) (acc : α) (s : Machine α) : Machine α :=
  setPointer (exitWide ops t acc s) 16 ⟨2, ((t*2 : Nat) : Int), true⟩
def exitStored (ops : Ops α) (t : Nat) (acc : α) (s : Machine α) : Machine α :=
  storedHalf (exitAddress ops t acc s) t (outputCell t) (ops.toHalf acc)
def exitReturned (ops : Ops α) (t : Nat) (acc : α) (s : Machine α) : Machine α :=
  returned (exitStored ops t acc s)

theorem output_address (t : Nat) (ht : t < 1048576) :
    address layout geometry t ⟨2, ((t*2 : Nat) : Int), true⟩ 0 true = some (outputCell t) := by
  have hs : signed64 ((t : Int)*2) := by unfold signed64; omega
  have hr : (Role.output == Role.input) = false := rfl
  rw [aligned_address layout geometry t 2 t _ 0 true (by simp) hs]
  simp [location, layout, ht, outputCell, hr]

theorem epilogue_execute (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (acc : α)
    (s : Machine α) (ht : t < 1048576) (h : LoopInvariant input t 16 acc s) :
    Steps ops layout geometry t program s (exitReturned ops t acc s) := by
  have hpc : s.pc = 132 := h.pc
  have e1 := global_step ops layout geometry t 14 9 s ⟨2, 0, false⟩ h.output
  have h1 : Steps ops layout geometry t program s (exitGlobal s) := by
    apply one_step
    rw [transition_at ops layout geometry t program s (.base (.toGlobal 14 9))
      h.stopped (by rw [hpc]; rfl), base_step]
    exact e1
  have e2 := half_step ops layout geometry t 33 68 (exitGlobal s) acc
    (by simpa only [exitGlobal, setPointer_scalar] using h.accumulator)
  have h2 : Steps ops layout geometry t program (exitGlobal s) (exitHalf ops acc s) := by
    apply one_step
    rw [transition_at ops layout geometry t program (exitGlobal s) (.base (.toHalf 33 68))
      (by simpa only [exitGlobal, setPointer_stopped] using h.stopped)
      (by simp only [exitGlobal, setPointer_pc, hpc]; rfl), base_step]
    exact e2
  have hb : signed32 (t : Int) ∧ signed32 2 ∧ signed64 ((t : Int)*2) := by
    unfold signed32 signed64; omega
  have hx : (exitHalf ops acc s).registers.i32 1 = some (t : Int) := by
    change s.registers.i32 1 = some (t : Int)
    exact h.thread
  have e3 := wide_step ops layout geometry t 15 1 2 (t : Int) (exitHalf ops acc s) hx hb
  have he : (t : Int)*2 = ((t*2 : Nat) : Int) := by simp
  rw [he] at e3
  have h3 : Steps ops layout geometry t program (exitHalf ops acc s) (exitWide ops t acc s) := by
    apply one_step
    rw [transition_at ops layout geometry t program (exitHalf ops acc s) (.base (.mulWideSigned32 15 1 2))
      (by change s.registers.stopped = false; exact h.stopped)
      (by change program[(s.pc+1)+1]? = _; rw [hpc]; rfl), base_step]
    exact e3
  have hp : signed64 ((t*2 : Nat) : Int) ∧ signed64 (0+((t*2 : Nat) : Int)) := by
    unfold signed64; simp only [Int.natCast_mul]; omega
  have e4 := pointer_add_step ops layout geometry t 16 14 (.reg 15) ⟨2, 0, true⟩
    ((t*2 : Nat) : Int) (exitWide ops t acc s) (by rfl) (by simp [operand64, exitWide, setIndex64_i64]) hp
  simp only [Int.zero_add] at e4
  have h4 : Steps ops layout geometry t program (exitWide ops t acc s) (exitAddress ops t acc s) := by
    apply one_step
    rw [transition_at ops layout geometry t program (exitWide ops t acc s) (.base (.addSigned64 16 14 (.reg 15)))
      (by change s.registers.stopped = false; exact h.stopped)
      (by change program[((s.pc+1)+1)+1]? = _; rw [hpc]; rfl), base_step]
    exact e4
  have e5 := store_step ops layout geometry t 16 33 0 (exitAddress ops t acc s)
    ⟨2, ((t*2 : Nat) : Int), true⟩ (outputCell t) (ops.toHalf acc) (by rfl)
    (output_address t ht) (by rfl)
  have h5 : Steps ops layout geometry t program (exitAddress ops t acc s) (exitStored ops t acc s) := by
    apply one_step
    rw [transition_at ops layout geometry t program (exitAddress ops t acc s) (.base (.storeHalf 16 0 33))
      (by change s.registers.stopped = false; exact h.stopped)
      (by change program[(((s.pc+1)+1)+1)+1]? = _; rw [hpc]; rfl), base_step]
    exact e5
  have h6 : Steps ops layout geometry t program (exitStored ops t acc s) (exitReturned ops t acc s) := by
    apply one_step
    rw [transition_at ops layout geometry t program (exitStored ops t acc s) (.base .ret)
      (by change s.registers.stopped = false; exact h.stopped)
      (by change program[((((s.pc+1)+1)+1)+1)+1]? = _; rw [hpc]; rfl), base_step]
    exact return_step ops layout geometry t _
  apply steps_trans _ _ _ _ _ _ _ _ h1
  apply steps_trans _ _ _ _ _ _ _ _ h2
  apply steps_trans _ _ _ _ _ _ _ _ h3
  apply steps_trans _ _ _ _ _ _ _ _ h4
  exact steps_trans _ _ _ _ _ _ _ _ h5 h6

theorem runTerms_memory (ops : Ops α) (input : Nat → Nat → α) (t c j n : Nat) (acc : α)
    (s : Machine α) :
    (runTerms ops input t c j n acc s).registers.base.memory = s.registers.base.memory := by
  induction n generalizing j acc s with
  | zero => rfl
  | succ n ih => simp only [runTerms, ih, chunkStep, termResult_memory]

theorem bodyEnd_memory (ops : Ops α) (input : Nat → Nat → α) (t c : Nat) (acc : α)
    (s : Machine α) :
    (bodyEnd ops input t c acc s).registers.base.memory = s.registers.base.memory := by
  simp only [bodyEnd, runTerms_memory, firstChunk, firstResult_memory]

theorem iteration_memory (ops : Ops α) (input : Nat → Nat → α) (t c : Nat) (acc : α)
    (s : Machine α) :
    (iteration ops input t c acc s).registers.base.memory = s.registers.base.memory := by
  simp only [iteration, control_memory, bodyEnd_memory]

theorem runChunks_memory (ops : Ops α) (input : Nat → Nat → α) (t c n : Nat) (acc : α)
    (s : Machine α) :
    (runChunks ops input t c n acc s).registers.base.memory = s.registers.base.memory := by
  induction n generalizing c acc s with
  | zero => rfl
  | succ n ih => simp only [runChunks, ih, iteration_memory]

def dotValue (ops : Ops α) (input : Nat → Nat → α) (t : Nat) : α :=
  foldChunks ops input t 0 16 (ops.literal 0 1)

theorem source_to_loop_exit (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (base : State α)
    (ht : t < 1048576) (hreads : Reads input (start base)) :
    ∃ final, Steps ops layout geometry t program (start base) final ∧
      LoopInvariant input t 16 (dotValue ops input t) final ∧ final.registers.base.memory = base.memory := by
  obtain ⟨initial, initialSteps, ready⟩ := Init.prefix29_execute ops t base ht
  have entry := initial_loop ops input t base initial ready hreads
  have loop := runChunks_execute ops input t 0 16 (ops.literal 0 1) initial ht (by decide) entry
  refine ⟨runChunks ops input t 0 16 (ops.literal 0 1) initial,
    steps_trans _ _ _ _ _ _ _ _ initialSteps loop.1, loop.2, ?_⟩
  rw [runChunks_memory, ready.frame.memory]

theorem exitReturned_memory (ops : Ops α) (t : Nat) (acc : α) (s : Machine α) :
    (exitReturned ops t acc s).registers.base.memory =
      fun l => if l = outputCell t then some (ops.toHalf acc) else s.registers.base.memory l := rfl

theorem exitReturned_stopped (ops : Ops α) (t : Nat) (acc : α) (s : Machine α) :
    (exitReturned ops t acc s).registers.stopped = true := rfl

theorem exitReturned_pc (ops : Ops α) (t : Nat) (acc : α) (s : Machine α) :
    (exitReturned ops t acc s).pc = s.pc+6 := rfl

theorem source_lane (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (base : State α)
    (ht : t < 1048576) (hreads : Reads input (start base)) :
    ∃ final, Steps ops layout geometry t program (start base) final ∧
      final.registers.stopped = true ∧ final.pc = 138 ∧
      final.registers.base.memory =
        fun l => if l = outputCell t then some (ops.toHalf (dotValue ops input t)) else base.memory l := by
  obtain ⟨exited, initialSteps, invariant, memory⟩ := source_to_loop_exit ops input t base ht hreads
  have tail := epilogue_execute ops input t (dotValue ops input t) exited ht invariant
  refine ⟨exitReturned ops t (dotValue ops input t) exited,
    steps_trans _ _ _ _ _ _ _ _ initialSteps tail, exitReturned_stopped _ _ _ _, ?_, ?_⟩
  · rw [exitReturned_pc, invariant.pc]
    rfl
  · rw [exitReturned_memory, memory]

def referenceTerm (ops : Ops α) (input : Nat → Nat → α) (t k : Nat) (acc : α) : α :=
  ops.add acc (ops.mul (ops.fromHalf (input 0 (aIndex t k))) (ops.fromHalf (input 1 (bIndex t k))))

def referenceFold (ops : Ops α) (input : Nat → Nat → α) (t : Nat) : Nat → Nat → α → α
  | _, 0, acc => acc
  | k, r+1, acc => referenceFold ops input t (k+1) r (referenceTerm ops input t k acc)

theorem foldTerms_reference (ops : Ops α) (input : Nat → Nat → α) (t c j r : Nat) (acc : α) :
    foldTerms ops input t c j r acc = referenceFold ops input t (16*c+j) r acc := by
  induction r generalizing j acc with
  | zero => rfl
  | succ r ih =>
      simp only [foldTerms, ih, referenceFold, nextValue, referenceTerm, Nat.add_assoc]

theorem chunkValue_reference (ops : Ops α) (input : Nat → Nat → α) (t c : Nat) (acc : α) :
    chunkValue ops input t c acc = referenceFold ops input t (16*c) 16 acc := by
  rw [chunkValue, foldTerms_reference]
  rfl

theorem referenceFold_append (ops : Ops α) (input : Nat → Nat → α) (t k m n : Nat) (acc : α) :
    referenceFold ops input t k (m+n) acc =
      referenceFold ops input t (k+m) n (referenceFold ops input t k m acc) := by
  induction m generalizing k acc with
  | zero => simp [referenceFold]
  | succ m ih =>
      have he : m+1+n = (m+n)+1 := by omega
      simp only [he, referenceFold, ih]
      have hk : k+1+m = k+(m+1) := by omega
      rw [hk]

theorem foldChunks_reference (ops : Ops α) (input : Nat → Nat → α) (t c r : Nat) (acc : α) :
    foldChunks ops input t c r acc = referenceFold ops input t (16*c) (16*r) acc := by
  induction r generalizing c acc with
  | zero => rfl
  | succ r ih =>
      rw [foldChunks, ih, chunkValue_reference]
      have he : 16*(r+1) = 16+16*r := by omega
      rw [he, referenceFold_append]
      have hc : 16*(c+1) = 16*c+16 := by omega
      simp only [hc]

def reference (ops : Ops α) (input : Nat → Nat → α) (t : Nat) : α :=
  ops.toHalf (referenceFold ops input t 0 256 (ops.literal 0 1))

theorem dotValue_reference (ops : Ops α) (input : Nat → Nat → α) (t : Nat) :
    ops.toHalf (dotValue ops input t) = reference ops input t := by
  unfold dotValue reference
  rw [foldChunks_reference]

theorem source_lane_reference (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (base : State α)
    (ht : t < 1048576) (hreads : Reads input (start base)) :
    ∃ final, Steps ops layout geometry t program (start base) final ∧
      final.registers.stopped = true ∧ final.pc = 138 ∧
      final.registers.base.memory =
        fun l => if l = outputCell t then some (reference ops input t) else base.memory l := by
  obtain ⟨final, execution, stopped, pc, memory⟩ := source_lane ops input t base ht hreads
  refine ⟨final, execution, stopped, pc, ?_⟩
  simpa only [dotValue_reference] using memory

inductive LaneSequence (ops : Ops α) (p : List LarkPtxMatrix.Instruction) :
    Nat → Nat → State α → State α → Prop where
  | nil (k : Nat) (s : State α) : LaneSequence ops p k 0 s s
  | next {k r : Nat} {s final : State α} {m : Machine α} :
      Steps ops layout geometry k p (start s) m →
      m.registers.stopped = true →
      LaneSequence ops p (k+1) r m.registers.base final →
      LaneSequence ops p k (r+1) s final

theorem lane_reads (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (base : State α)
    (s : Machine α) (hreads : Reads input (start base))
    (memory : s.registers.base.memory =
      fun l => if l = outputCell t then some (reference ops input t) else base.memory l) :
    Reads input (start s.registers.base) := by
  constructor
  · intro i hi
    change s.registers.base.memory ⟨.global, 0, 0, i⟩ = _
    rw [memory]
    simpa [outputCell] using hreads.1 i hi
  · intro i hi
    change s.registers.base.memory ⟨.global, 0, 1, i⟩ = _
    rw [memory]
    simpa [outputCell] using hreads.2 i hi

theorem launch_exists (ops : Ops α) (input : Nat → Nat → α) (k r : Nat) (base : State α)
    (hcount : k+r ≤ 1048576) (hreads : Reads input (start base)) :
    ∃ final, LaneSequence ops program k r base final ∧ Reads input (start final) ∧
      (∀ i, final.memory (outputCell i) =
        if k ≤ i ∧ i < k+r then some (reference ops input i) else base.memory (outputCell i)) ∧
      (∀ l, (∀ i, k ≤ i → i < k+r → l ≠ outputCell i) → final.memory l = base.memory l) := by
  induction r generalizing k base with
  | zero =>
      refine ⟨base, .nil k base, hreads, ?_, ?_⟩
      · intro i
        have hn : ¬ (k ≤ i ∧ i < k+0) := by omega
        simp only [if_neg hn]
      · intro l _
        rfl
  | succ r ih =>
      obtain ⟨lane, execution, stopped, pc, memory⟩ := source_lane_reference ops input k base (by omega) hreads
      have nextReads := lane_reads ops input k base lane hreads memory
      obtain ⟨final, tail, finalReads, outputs, outside⟩ := ih (k+1) lane.registers.base (by omega) nextReads
      refine ⟨final, .next execution stopped tail, finalReads, ?_, ?_⟩
      · intro i
        rw [outputs]
        by_cases hi : i = k
        · subst i
          have hrest : ¬ (k+1 ≤ k ∧ k < k+1+r) := by omega
          have hwhole : k ≤ k ∧ k < k+(r+1) := by omega
          rw [if_neg hrest, memory]
          simp [hwhole]
        · have hloc : outputCell i ≠ outputCell k := by
            intro he
            exact hi (congrArg Location.offset he)
          have hrange : (k+1 ≤ i ∧ i < k+1+r) ↔ (k ≤ i ∧ i < k+(r+1)) := by omega
          rw [memory]
          simp only [hloc, if_false, hrange]
      · intro l h
        have htail : ∀ i, k+1 ≤ i → i < k+1+r → l ≠ outputCell i := by
          intro i hi hj
          exact h i (by omega) (by omega)
        rw [outside l htail, memory]
        simp only [if_neg (h k (by omega) (by omega))]

theorem initial_reads (input : Nat → Nat → α) (outside : Location → Option α) :
    Reads input (start (initial layout input outside)) := by
  constructor
  · intro i hi
    change (initial layout input outside).memory ⟨.global, 0, 0, i⟩ = _
    simp [initial, layout, hi]
  · intro i hi
    change (initial layout input outside).memory ⟨.global, 0, 1, i⟩ = _
    simp [initial, layout, hi]

theorem source_launch_outputs (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) :
    ∃ final, LaneSequence ops program 0 1048576 (initial layout input outside) final ∧
      (∀ i, i < 1048576 → final.memory (outputCell i) = some (reference ops input i)) ∧
      (∀ l, (∀ i, i < 1048576 → l ≠ outputCell i) →
        final.memory l = (initial layout input outside).memory l) := by
  obtain ⟨final, execution, reads, outputs, preserved⟩ :=
    launch_exists ops input 0 1048576 (initial layout input outside) (by decide) (initial_reads input outside)
  refine ⟨final, execution, ?_, ?_⟩
  · intro i hi
    simpa only [Nat.zero_le, true_and, Nat.zero_add, if_pos hi] using outputs i
  · intro l h
    apply preserved l
    intro i _ hi
    exact h i (by simpa using hi)

abbrev TraceSafe := LarkPtxMatrix.Gemm.TraceSafe

theorem control_trace (c : Nat) (s : Machine α) :
    (controlResult c s).registers.base.trace = s.registers.base.trace := rfl

theorem termResult_trace_safe (ops : Ops α) (t c j : Nat) (a b acc : α) (s : Machine α)
    (h : TraceSafe s.registers.base.trace) :
    TraceSafe (termResult ops t c j a b acc s).registers.base.trace := by
  intro access ha
  change access ∈ (⟨t, bCell t c j, false, s.registers.base.epochs t⟩ ::
    ⟨t, aCell t c j, false, s.registers.base.epochs t⟩ :: s.registers.base.trace) at ha
  simp only [List.mem_cons] at ha
  rcases ha with rfl | rfl | ha
  · simp [LarkPtxMatrix.Gemm.AccessSafe, bCell]
  · simp [LarkPtxMatrix.Gemm.AccessSafe, aCell]
  · exact h access ha

theorem firstResult_trace_safe (ops : Ops α) (t c : Nat) (a b acc : α) (s : Machine α)
    (h : TraceSafe s.registers.base.trace) :
    TraceSafe (firstResult ops t c a b acc s).registers.base.trace := by
  intro access ha
  change access ∈ (⟨t, bCell t c 0, false, s.registers.base.epochs t⟩ ::
    ⟨t, aCell t c 0, false, s.registers.base.epochs t⟩ :: s.registers.base.trace) at ha
  simp only [List.mem_cons] at ha
  rcases ha with rfl | rfl | ha
  · simp [LarkPtxMatrix.Gemm.AccessSafe, bCell]
  · simp [LarkPtxMatrix.Gemm.AccessSafe, aCell]
  · exact h access ha

theorem runTerms_trace_safe (ops : Ops α) (input : Nat → Nat → α) (t c j r : Nat)
    (acc : α) (s : Machine α) (h : TraceSafe s.registers.base.trace) :
    TraceSafe (runTerms ops input t c j r acc s).registers.base.trace := by
  induction r generalizing j acc s with
  | zero => exact h
  | succ r ih =>
      exact ih (j+1) (nextValue ops input t c j acc) (chunkStep ops input t c j acc s)
        (termResult_trace_safe ops t c j _ _ acc s h)

theorem iteration_trace_safe (ops : Ops α) (input : Nat → Nat → α) (t c : Nat)
    (acc : α) (s : Machine α) (h : TraceSafe s.registers.base.trace) :
    TraceSafe (iteration ops input t c acc s).registers.base.trace := by
  rw [iteration, control_trace]
  unfold bodyEnd
  exact runTerms_trace_safe ops input t c 1 15 (nextValue ops input t c 0 acc)
    (firstChunk ops input t c acc s) (firstResult_trace_safe ops t c _ _ acc s h)

theorem runChunks_trace_safe (ops : Ops α) (input : Nat → Nat → α) (t c r : Nat)
    (acc : α) (s : Machine α) (h : TraceSafe s.registers.base.trace) :
    TraceSafe (runChunks ops input t c r acc s).registers.base.trace := by
  induction r generalizing c acc s with
  | zero => exact h
  | succ r ih =>
      exact ih (c+1) (chunkValue ops input t c acc) (iteration ops input t c acc s)
        (iteration_trace_safe ops input t c acc s h)

theorem exitReturned_trace_safe (ops : Ops α) (t : Nat) (acc : α) (s : Machine α)
    (h : TraceSafe s.registers.base.trace) :
    TraceSafe (exitReturned ops t acc s).registers.base.trace := by
  intro access ha
  change access ∈ (⟨t, outputCell t, true, s.registers.base.epochs t⟩ :: s.registers.base.trace) at ha
  rcases List.mem_cons.mp ha with rfl | ha
  · rfl
  · exact h access ha

theorem source_lane_safe (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (base : State α)
    (ht : t < 1048576) (hreads : Reads input (start base)) (hsafe : TraceSafe base.trace) :
    ∃ final, Steps ops layout geometry t program (start base) final ∧
      final.registers.stopped = true ∧ final.pc = 138 ∧
      final.registers.base.memory =
        (fun l => if l = outputCell t then some (reference ops input t) else base.memory l) ∧
      TraceSafe final.registers.base.trace := by
  obtain ⟨initial, initialSteps, ready⟩ := Init.prefix29_execute ops t base ht
  have entry := initial_loop ops input t base initial ready hreads
  have loop := runChunks_execute ops input t 0 16 (ops.literal 0 1) initial ht (by decide) entry
  let exited := runChunks ops input t 0 16 (ops.literal 0 1) initial
  have invariant : LoopInvariant input t 16 (dotValue ops input t) exited := loop.2
  have tail := epilogue_execute ops input t (dotValue ops input t) exited ht invariant
  have memory : exited.registers.base.memory = base.memory := by
    rw [runChunks_memory, ready.frame.memory]
  have initialSafe : TraceSafe initial.registers.base.trace := by
    rw [ready.frame.memory]
    exact hsafe
  have exitedSafe : TraceSafe exited.registers.base.trace :=
    runChunks_trace_safe ops input t 0 16 (ops.literal 0 1) initial initialSafe
  refine ⟨exitReturned ops t (dotValue ops input t) exited,
    steps_trans _ _ _ _ _ _ _ _ initialSteps (steps_trans _ _ _ _ _ _ _ _ loop.1 tail),
    exitReturned_stopped _ _ _ _, ?_, ?_, exitReturned_trace_safe _ _ _ _ exitedSafe⟩
  · rw [exitReturned_pc, invariant.pc]
    rfl
  · rw [exitReturned_memory, memory, dotValue_reference]

theorem launch_exists_safe (ops : Ops α) (input : Nat → Nat → α) (k r : Nat) (base : State α)
    (hcount : k+r ≤ 1048576) (hreads : Reads input (start base)) (hsafe : TraceSafe base.trace) :
    ∃ final, LaneSequence ops program k r base final ∧ Reads input (start final) ∧ TraceSafe final.trace ∧
      (∀ i, final.memory (outputCell i) =
        if k ≤ i ∧ i < k+r then some (reference ops input i) else base.memory (outputCell i)) ∧
      (∀ l, (∀ i, k ≤ i → i < k+r → l ≠ outputCell i) → final.memory l = base.memory l) := by
  induction r generalizing k base with
  | zero =>
      refine ⟨base, .nil k base, hreads, hsafe, ?_, ?_⟩
      · intro i
        have hn : ¬ (k ≤ i ∧ i < k+0) := by omega
        simp only [if_neg hn]
      · intro l _
        rfl
  | succ r ih =>
      obtain ⟨lane, execution, stopped, pc, memory, laneSafe⟩ := source_lane_safe ops input k base (by omega) hreads hsafe
      have nextReads := lane_reads ops input k base lane hreads memory
      obtain ⟨final, tail, finalReads, finalSafe, outputs, outside⟩ := ih (k+1) lane.registers.base (by omega) nextReads laneSafe
      refine ⟨final, .next execution stopped tail, finalReads, finalSafe, ?_, ?_⟩
      · intro i
        rw [outputs]
        by_cases hi : i = k
        · subst i
          have hrest : ¬ (k+1 ≤ k ∧ k < k+1+r) := by omega
          have hwhole : k ≤ k ∧ k < k+(r+1) := by omega
          rw [if_neg hrest, memory]
          simp [hwhole]
        · have hloc : outputCell i ≠ outputCell k := by
            intro he
            exact hi (congrArg Location.offset he)
          have hrange : (k+1 ≤ i ∧ i < k+1+r) ↔ (k ≤ i ∧ i < k+(r+1)) := by omega
          rw [memory]
          simp only [hloc, if_false, hrange]
      · intro l h
        have htail : ∀ i, k+1 ≤ i → i < k+1+r → l ≠ outputCell i := by
          intro i hi hj
          exact h i (by omega) (by omega)
        rw [outside l htail, memory]
        simp only [if_neg (h k (by omega) (by omega))]

def referenceSpec (ops : Ops α) (input : Nat → Nat → α) : List α :=
  (List.range 1048576).map (reference ops input)

inductive TensorReference where
  | input : Nat → TensorReference
  | fromHalf : TensorReference → TensorReference
  | matmul : TensorReference → TensorReference → TensorReference
  | toHalf : TensorReference → TensorReference
  deriving DecidableEq, Repr

def referenceBody : TensorReference :=
  .toHalf (.matmul (.fromHalf (.input 0)) (.fromHalf (.input 1)))

/-- Closed [32,64,256] @ [32,256,512] FP16 batched reference; other ASTs refuse.
The scalar operations and reference formalization retain their declared trust
boundary. This does not establish IEEE or backend conformance. -/
def evaluateReference (ops : Ops α) (input : Nat → Nat → α) : TensorReference → Option (List α)
  | .toHalf (.matmul (.fromHalf (.input 0)) (.fromHalf (.input 1))) => some (referenceSpec ops input)
  | _ => none

theorem evaluate_reference_body (ops : Ops α) (input : Nat → Nat → α) :
    evaluateReference ops input referenceBody = some (referenceSpec ops input) := rfl

theorem extract_outputs (s : State α) (values : Nat → α)
    (h : ∀ i, i < 1048576 → s.memory (outputCell i) = some (values i)) :
    extract layout s = some ((List.range 1048576).map values) := by
  simp only [extract, layout, List.zipIdx_cons, List.zipIdx_nil, List.flatMap_cons,
    List.flatMap_nil, List.nil_append]
  simp only [List.map_cons, List.map_nil, show Role.input ≠ Role.output by decide,
    ↓reduceIte, List.nil_append, List.append_nil]
  change (((List.range 1048576).map (fun i => (2, i))).mapM
    (fun bi => s.memory ⟨.global, 0, bi.1, bi.2⟩) : Option (List α)) = _
  rw [LarkPointwise.mapM_map]
  exact LarkPointwise.mapM_some (List.range 1048576) _ _ (by
    intro i hi
    exact h i (List.mem_range.mp hi))

def Correct (ops : Ops α) (p : List LarkPtxMatrix.Instruction)
    (spec : (Nat → Nat → α) → List α) : Prop :=
  ∀ input outside, ∃ final,
    LaneSequence ops p 0 1048576 (initial layout input outside) final ∧
    raceFree geometry final.trace = true ∧ extract layout final = some (spec input) ∧
    (∀ l, (∀ i, i < 1048576 → l ≠ outputCell i) →
      final.memory l = (initial layout input outside).memory l)

theorem kernel_correct (ops : Ops α) : Correct ops program (referenceSpec ops) := by
  intro input outside
  have initialSafe : TraceSafe (initial layout input outside).trace := by
    simp [LarkPtxMatrix.Gemm.TraceSafe, initial]
  obtain ⟨final, execution, reads, safe, outputs, preserved⟩ :=
    launch_exists_safe ops input 0 1048576 (initial layout input outside)
      (by decide) (initial_reads input outside) initialSafe
  have everyOutput : ∀ i, i < 1048576 → final.memory (outputCell i) = some (reference ops input i) := by
    intro i hi
    simpa only [Nat.zero_le, true_and, Nat.zero_add, if_pos hi] using outputs i
  refine ⟨final, execution, LarkPtxMatrix.Gemm.trace_safe_raceFree geometry final.trace safe,
    extract_outputs final (reference ops input) everyOutput, ?_⟩
  intro l h
  apply preserved l
  intro i _ hi
  exact h i (by simpa using hi)

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
#print axioms LarkPtxBatched.Bmm.Body.control_execute
#print axioms LarkPtxBatched.Bmm.Body.control_pc
#print axioms LarkPtxBatched.Bmm.Body.control_memory
#print axioms LarkPtxBatched.Bmm.Body.control_i64
#print axioms LarkPtxBatched.Bmm.Body.control_invariant
#print axioms LarkPtxBatched.Bmm.Body.iteration_execute
#print axioms LarkPtxBatched.Bmm.Body.runChunks_execute
#print axioms LarkPtxBatched.Bmm.Body.output_address
#print axioms LarkPtxBatched.Bmm.Body.epilogue_execute
#print axioms LarkPtxBatched.Bmm.Body.runTerms_memory
#print axioms LarkPtxBatched.Bmm.Body.bodyEnd_memory
#print axioms LarkPtxBatched.Bmm.Body.iteration_memory
#print axioms LarkPtxBatched.Bmm.Body.runChunks_memory
#print axioms LarkPtxBatched.Bmm.Body.source_to_loop_exit
#print axioms LarkPtxBatched.Bmm.Body.exitReturned_memory
#print axioms LarkPtxBatched.Bmm.Body.exitReturned_stopped
#print axioms LarkPtxBatched.Bmm.Body.exitReturned_pc
#print axioms LarkPtxBatched.Bmm.Body.source_lane
#print axioms LarkPtxBatched.Bmm.Body.foldTerms_reference
#print axioms LarkPtxBatched.Bmm.Body.chunkValue_reference
#print axioms LarkPtxBatched.Bmm.Body.referenceFold_append
#print axioms LarkPtxBatched.Bmm.Body.foldChunks_reference
#print axioms LarkPtxBatched.Bmm.Body.dotValue_reference
#print axioms LarkPtxBatched.Bmm.Body.source_lane_reference
#print axioms LarkPtxBatched.Bmm.Body.lane_reads
#print axioms LarkPtxBatched.Bmm.Body.launch_exists
#print axioms LarkPtxBatched.Bmm.Body.initial_reads
#print axioms LarkPtxBatched.Bmm.Body.source_launch_outputs
#print axioms LarkPtxBatched.Bmm.Body.control_trace
#print axioms LarkPtxBatched.Bmm.Body.termResult_trace_safe
#print axioms LarkPtxBatched.Bmm.Body.firstResult_trace_safe
#print axioms LarkPtxBatched.Bmm.Body.runTerms_trace_safe
#print axioms LarkPtxBatched.Bmm.Body.iteration_trace_safe
#print axioms LarkPtxBatched.Bmm.Body.runChunks_trace_safe
#print axioms LarkPtxBatched.Bmm.Body.exitReturned_trace_safe
#print axioms LarkPtxBatched.Bmm.Body.source_lane_safe
#print axioms LarkPtxBatched.Bmm.Body.launch_exists_safe
#print axioms LarkPtxBatched.Bmm.Body.evaluate_reference_body
#print axioms LarkPtxBatched.Bmm.Body.extract_outputs
#print axioms LarkPtxBatched.Bmm.Body.kernel_correct
