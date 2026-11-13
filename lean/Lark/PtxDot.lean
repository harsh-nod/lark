import Lark.PtxPointwise

/-!
Small-step PTX model for the actual compiled scalar dot-product kernels.
Every instruction changes the physical typed register file, predicate state,
program counter or memory explicitly. Finite execution is an inductive sequence
of successful instruction transitions ending at ret; there is no new execution
fuel and no change to any existing CUDA task/fuel/shape/launch.

This is a guarded abstract model, not an IEEE or NVIDIA conformance result.
Its initial target is the original independent 512-by-1024 FP16 GEMV compiler
output, including the sixteen-term unrolled loop and actual backward branch.
No source-bound kernel theorem is established by these definitions alone.
-/
namespace LarkPtxDot
open LarkNonlinear
open LarkPtxPointwise
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

inductive Operand where
  | reg : Nat → Operand
  | imm : Int → Operand
  deriving DecidableEq, Repr

inductive Instruction where
  | parameter : Nat → Nat → Instruction
  | toGlobal : Nat → Nat → Instruction
  | blockId : Nat → Instruction
  | literal32 : Nat → Int → Instruction
  | shiftLeft32 : Nat → Nat → Nat → Instruction
  | addSigned32 : Nat → Nat → Operand → Instruction
  | mulWideSigned32 : Nat → Nat → Int → Instruction
  | addSigned64 : Nat → Nat → Operand → Instruction
  | loadHalf : Nat → Nat → Int → Instruction
  | fromHalf : Nat → Nat → Instruction
  | literalFloat : Nat → Int → Nat → Instruction
  | binaryFloat : Nat → Binary → Nat → Nat → Instruction
  | toHalf : Nat → Nat → Instruction
  | storeHalf : Nat → Int → Nat → Instruction
  | compareNeSigned32 : Nat → Nat → Operand → Instruction
  | branch : Nat → Nat → Instruction
  | ret : Instruction
  deriving DecidableEq, Repr

structure Machine (α : Type) where
  registers : Registers α
  predicates : Nat → Option Bool := fun _ => none
  pc : Nat := 0

def operand32 (s : Registers α) : Operand → Option Int
  | .reg r => s.i32 r
  | .imm n => some n

def operand64 (s : Registers α) : Operand → Option Int
  | .reg r => s.i64 r
  | .imm n => some n

def unsigned32 (v : Int) : Prop := 0 ≤ v ∧ v < 4294967296
instance (v : Int) : Decidable (unsigned32 v) :=
  inferInstanceAs (Decidable (0 ≤ v ∧ v < 4294967296))

def address (layout : Layout) (g : Geometry) (t : Nat)
    (p : Pointer) (offset : Int) (write : Bool) : Option Location :=
  let byte := p.offset + offset
  if p.isGlobal ∧ signed64 byte ∧ byte % 2 = 0 then
    location layout g t .global p.buffer (byte / 2) write
  else none

def advance (s : Machine α) (registers : Registers α) : Machine α :=
  { s with registers, pc := s.pc + 1 }

def execute (ops : Ops α) (layout : Layout) (g : Geometry) (t : Nat)
    (instruction : Instruction) (s : Machine α) : Option (Machine α) := do
  let r := s.registers
  match instruction with
  | .parameter d b =>
      if b < layout.global.length then
        some (advance s (putPointer r d ⟨b, 0, false⟩))
      else none
  | .toGlobal d a =>
      let p ← r.pointer a
      some (advance s (putPointer r d { p with isGlobal := true }))
  | .blockId d =>
      let block := t / g.block
      if 0 < g.block ∧ block < 4294967296 then
        some (advance s (putI32 r d block))
      else none
  | .literal32 d n =>
      if unsigned32 n then some (advance s (putI32 r d n)) else none
  | .shiftLeft32 d a count =>
      let v ← r.i32 a
      if unsigned32 v then
        some (advance s (putI32 r d ((v * (2 : Int) ^ min count 32) % 4294967296)))
      else none
  | .addSigned32 d a b =>
      let x ← r.i32 a
      let y ← operand32 r b
      if signed32 x ∧ signed32 y ∧ signed32 (x + y) then
        some (advance s (putI32 r d (x + y)))
      else none
  | .mulWideSigned32 d a c =>
      let v ← r.i32 a
      if signed32 v ∧ signed32 c ∧ signed64 (v * c) then
        some (advance s (putI64 r d (v * c)))
      else none
  | .addSigned64 d a b =>
      let y ← operand64 r b
      if signed64 y then
        match r.values (.int64 a) with
        | some (.address p) =>
            if signed64 (p.offset + y) then
              some (advance s (putPointer r d { p with offset := p.offset + y }))
            else none
        | some (.integer x) =>
            if signed64 x ∧ signed64 (x + y) then
              some (advance s (putI64 r d (x + y)))
            else none
        | _ => none
      else none
  | .loadHalf d a offset =>
      let p ← r.pointer a
      let l ← address layout g t p offset false
      let value ← r.base.memory l
      some (advance s { putHalf r d value with base := record r.base t l false })
  | .fromHalf d a =>
      let value ← r.half a
      some (advance s (putScalar r d (ops.fromHalf value)))
  | .literalFloat d n denominator =>
      if denominator ≠ 0 then
        some (advance s (putScalar r d (ops.literal n denominator)))
      else none
  | .binaryFloat d op a b =>
      let x ← r.scalar a
      let y ← r.scalar b
      some (advance s (putScalar r d (applyBinary ops op x y)))
  | .toHalf d a =>
      let value ← r.scalar a
      some (advance s (putHalf r d (ops.toHalf value)))
  | .storeHalf a offset b =>
      let p ← r.pointer a
      let l ← address layout g t p offset true
      let value ← r.half b
      let base := { record r.base t l true with
                    memory := fun k => if k = l then some value else r.base.memory k }
      some (advance s { r with base })
  | .compareNeSigned32 d a b =>
      let x ← r.i32 a
      let y ← operand32 r b
      if signed32 x ∧ signed32 y then
        some { s with predicates := fun p => if p = d then some (x != y) else s.predicates p,
                      pc := s.pc + 1 }
      else none
  | .branch predicate target =>
      let taken ← s.predicates predicate
      some { s with pc := if taken then target else s.pc + 1 }
  | .ret => some (advance s { r with stopped := true })

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

theorem transition_halted (ops : Ops α) (layout : Layout) (g : Geometry) (t : Nat)
    (program : List Instruction) (s : Machine α) (h : s.registers.stopped = true) :
    transition ops layout g t program s = none := by
  simp [transition, h]

theorem branch_uninitialized (ops : Ops α) (layout : Layout) (g : Geometry) (t p target : Nat)
    (s : Machine α) (h : s.predicates p = none) :
    execute ops layout g t (.branch p target) s = none := by
  simp [execute, h]

theorem transition_at (ops : Ops α) (layout : Layout) (g : Geometry) (t : Nat)
    (program : List Instruction) (s : Machine α) (instruction : Instruction)
    (hstop : s.registers.stopped = false) (hfetch : program[s.pc]? = some instruction) :
    transition ops layout g t program s = execute ops layout g t instruction s := by
  simp [transition, hstop, hfetch]

theorem blockId_step (ops : Ops α) (layout : Layout) (g : Geometry) (t d : Nat)
    (s : Machine α) (h : 0 < g.block ∧ t / g.block < 4294967296) :
    execute ops layout g t (.blockId d) s =
      some (advance s (putI32 s.registers d ((t / g.block : Nat) : Int))) := by
  simp [execute, h]

theorem shiftLeft_step (ops : Ops α) (layout : Layout) (g : Geometry) (t d a count : Nat)
    (s : Machine α) (v : Int) (hv : s.registers.i32 a = some v) (hb : unsigned32 v) :
    execute ops layout g t (.shiftLeft32 d a count) s =
      some (advance s (putI32 s.registers d ((v * (2 : Int) ^ min count 32) % 4294967296))) := by
  simp [execute, hv, hb]

theorem wide_step (ops : Ops α) (layout : Layout) (g : Geometry) (t d a : Nat) (c v : Int)
    (s : Machine α) (hv : s.registers.i32 a = some v)
    (hb : signed32 v ∧ signed32 c ∧ signed64 (v * c)) :
    execute ops layout g t (.mulWideSigned32 d a c) s =
      some (advance s (putI64 s.registers d (v * c))) := by
  simp [execute, hv, hb]

theorem pointer_add_step (ops : Ops α) (layout : Layout) (g : Geometry) (t d a : Nat)
    (b : Operand) (p : Pointer) (v : Int) (s : Machine α)
    (hp : s.registers.values (.int64 a) = some (.address p))
    (hv : operand64 s.registers b = some v) (hb : signed64 v ∧ signed64 (p.offset + v)) :
    execute ops layout g t (.addSigned64 d a b) s =
      some (advance s (putPointer s.registers d { p with offset := p.offset + v })) := by
  simp [execute, hp, hv, hb.1, hb.2]

def setFloat (s : Machine α) (d : Nat) (v : α) : Machine α :=
  advance s (putScalar s.registers d v)

def loadedHalf (s : Machine α) (t d : Nat) (l : Location) (v : α) : Machine α :=
  advance s { putHalf s.registers d v with base := record s.registers.base t l false }

@[simp] theorem setFloat_scalar (s : Machine α) (d r : Nat) (v : α) :
    (setFloat s d v).registers.scalar r = if r = d then some v else s.registers.scalar r := by
  by_cases h : r = d <;> simp [setFloat, advance, putScalar, putValue, Registers.scalar, h]

@[simp] theorem loadedHalf_half (s : Machine α) (t d r : Nat) (l : Location) (v : α) :
    (loadedHalf s t d l v).registers.half r = if r = d then some v else s.registers.half r := by
  by_cases h : r = d <;> simp [loadedHalf, advance, putHalf, putValue, Registers.half, h]

@[simp] theorem setFloat_half (s : Machine α) (d r : Nat) (v : α) :
    (setFloat s d v).registers.half r = s.registers.half r := rfl

@[simp] theorem loadedHalf_scalar (s : Machine α) (t d r : Nat) (l : Location) (v : α) :
    (loadedHalf s t d l v).registers.scalar r = s.registers.scalar r := rfl

@[simp] theorem setFloat_pointer (s : Machine α) (d r : Nat) (v : α) :
    (setFloat s d v).registers.pointer r = s.registers.pointer r := rfl

@[simp] theorem loadedHalf_pointer (s : Machine α) (t d r : Nat) (l : Location) (v : α) :
    (loadedHalf s t d l v).registers.pointer r = s.registers.pointer r := rfl

@[simp] theorem setFloat_memory (s : Machine α) (d : Nat) (v : α) :
    (setFloat s d v).registers.base.memory = s.registers.base.memory := rfl

@[simp] theorem loadedHalf_memory (s : Machine α) (t d : Nat) (l : Location) (v : α) :
    (loadedHalf s t d l v).registers.base.memory = s.registers.base.memory := rfl

@[simp] theorem setFloat_pc (s : Machine α) (d : Nat) (v : α) :
    (setFloat s d v).pc = s.pc + 1 := rfl

@[simp] theorem loadedHalf_pc (s : Machine α) (t d : Nat) (l : Location) (v : α) :
    (loadedHalf s t d l v).pc = s.pc + 1 := rfl

@[simp] theorem setFloat_stopped (s : Machine α) (d : Nat) (v : α) :
    (setFloat s d v).registers.stopped = s.registers.stopped := rfl

@[simp] theorem loadedHalf_stopped (s : Machine α) (t d : Nat) (l : Location) (v : α) :
    (loadedHalf s t d l v).registers.stopped = s.registers.stopped := rfl

theorem loadHalf_step (ops : Ops α) (layout : Layout) (g : Geometry) (t d a : Nat)
    (offset : Int) (s : Machine α) (p : Pointer) (l : Location) (v : α)
    (hp : s.registers.pointer a = some p) (hl : address layout g t p offset false = some l)
    (hv : s.registers.base.memory l = some v) :
    execute ops layout g t (.loadHalf d a offset) s = some (loadedHalf s t d l v) := by
  simp [execute, hp, hl, hv, loadedHalf]

theorem fromHalf_step (ops : Ops α) (layout : Layout) (g : Geometry) (t d a : Nat)
    (s : Machine α) (v : α) (hv : s.registers.half a = some v) :
    execute ops layout g t (.fromHalf d a) s = some (setFloat s d (ops.fromHalf v)) := by
  simp [execute, hv, setFloat]

theorem binaryFloat_step (ops : Ops α) (layout : Layout) (g : Geometry) (t d a b : Nat)
    (op : Binary) (s : Machine α) (x y : α)
    (hx : s.registers.scalar a = some x) (hy : s.registers.scalar b = some y) :
    execute ops layout g t (.binaryFloat d op a b) s =
      some (setFloat s d (applyBinary ops op x y)) := by
  simp [execute, hx, hy, setFloat]

theorem aligned_address (layout : Layout) (g : Geometry) (t b i : Nat)
    (offset delta : Int) (write : Bool)
    (he : offset + delta = (i : Int) * 2) (hs : signed64 ((i : Int) * 2)) :
    address layout g t ⟨b, offset, true⟩ delta write =
      location layout g t .global b (i : Int) write := by
  simp only [address]
  rw [he]
  simp [hs]

theorem read_location (layout : Layout) (g : Geometry) (t b i : Nat) (buffer : Buffer)
    (hb : layout.global[b]? = some buffer) (hi : i < buffer.size) :
    location layout g t .global b (i : Int) false = some ⟨.global, 0, b, i⟩ := by
  simp [location, hb, hi]

def setPointer (s : Machine α) (d : Nat) (p : Pointer) : Machine α :=
  advance s (putPointer s.registers d p)

def setIndex32 (s : Machine α) (d : Nat) (v : Int) : Machine α :=
  advance s (putI32 s.registers d v)

def setPredicate (s : Machine α) (d : Nat) (v : Bool) : Machine α :=
  { s with predicates := fun r => if r = d then some v else s.predicates r, pc := s.pc+1 }

@[simp] theorem setPointer_pointer (s : Machine α) (d r : Nat) (p : Pointer) :
    (setPointer s d p).registers.pointer r = if r = d then some p else s.registers.pointer r := by
  by_cases h : r = d <;> simp [setPointer, advance, putPointer, putValue, Registers.pointer, h]

@[simp] theorem setIndex32_i32 (s : Machine α) (d r : Nat) (v : Int) :
    (setIndex32 s d v).registers.i32 r = if r = d then some v else s.registers.i32 r := by
  by_cases h : r = d <;> simp [setIndex32, advance, putI32, putValue, Registers.i32, h]

@[simp] theorem setPointer_pc (s : Machine α) (d : Nat) (p : Pointer) :
    (setPointer s d p).pc = s.pc+1 := rfl
@[simp] theorem setIndex32_pc (s : Machine α) (d : Nat) (v : Int) :
    (setIndex32 s d v).pc = s.pc+1 := rfl
@[simp] theorem setPredicate_pc (s : Machine α) (d : Nat) (v : Bool) :
    (setPredicate s d v).pc = s.pc+1 := rfl

theorem pointer_values (s : Registers α) (a : Nat) (p : Pointer) (h : s.pointer a = some p) :
    s.values (.int64 a) = some (.address p) := by
  cases hv : s.values (.int64 a) with
  | none => simp [Registers.pointer, hv] at h
  | some v =>
      cases v with
      | integer n => simp [Registers.pointer, hv] at h
      | number x => simp [Registers.pointer, hv] at h
      | address q =>
          have he : q = p := by simpa [Registers.pointer, hv] using h
          simp [he]

theorem add32_step (ops : Ops α) (layout : Layout) (g : Geometry) (t d a : Nat) (b : Operand)
    (s : Machine α) (x y : Int) (hx : s.registers.i32 a = some x)
    (hy : operand32 s.registers b = some y) (hb : signed32 x ∧ signed32 y ∧ signed32 (x+y)) :
    execute ops layout g t (.addSigned32 d a b) s = some (setIndex32 s d (x+y)) := by
  simp [execute, hx, hy, hb, setIndex32]

theorem compare_ne_step (ops : Ops α) (layout : Layout) (g : Geometry) (t d a : Nat) (b : Operand)
    (s : Machine α) (x y : Int) (hx : s.registers.i32 a = some x)
    (hy : operand32 s.registers b = some y) (hb : signed32 x ∧ signed32 y) :
    execute ops layout g t (.compareNeSigned32 d a b) s = some (setPredicate s d (x != y)) := by
  simp [execute, hx, hy, hb, setPredicate]

def setHalf (s : Machine α) (d : Nat) (v : α) : Machine α :=
  advance s (putHalf s.registers d v)

def storedHalf (s : Machine α) (t : Nat) (l : Location) (v : α) : Machine α :=
  advance s { s.registers with base := { record s.registers.base t l true with
    memory := fun k => if k = l then some v else s.registers.base.memory k } }

def returned (s : Machine α) : Machine α :=
  advance s { s.registers with stopped := true }

theorem global_step (ops : Ops α) (layout : Layout) (g : Geometry) (t d a : Nat)
    (s : Machine α) (p : Pointer) (hp : s.registers.pointer a = some p) :
    execute ops layout g t (.toGlobal d a) s = some (setPointer s d { p with isGlobal := true }) := by
  simp [execute, hp, setPointer]

theorem half_step (ops : Ops α) (layout : Layout) (g : Geometry) (t d a : Nat)
    (s : Machine α) (v : α) (hv : s.registers.scalar a = some v) :
    execute ops layout g t (.toHalf d a) s = some (setHalf s d (ops.toHalf v)) := by
  simp [execute, hv, setHalf]

theorem store_step (ops : Ops α) (layout : Layout) (g : Geometry) (t a b : Nat) (offset : Int)
    (s : Machine α) (p : Pointer) (l : Location) (v : α)
    (hp : s.registers.pointer a = some p) (ha : address layout g t p offset true = some l)
    (hv : s.registers.half b = some v) :
    execute ops layout g t (.storeHalf a offset b) s = some (storedHalf s t l v) := by
  simp [execute, hp, ha, hv, storedHalf]

theorem return_step (ops : Ops α) (layout : Layout) (g : Geometry) (t : Nat) (s : Machine α) :
    execute ops layout g t .ret s = some (returned s) := rfl

namespace Gemv

def layout (rows : Nat) : Layout :=
  ⟨[⟨.input, rows * 1024⟩, ⟨.input, 1024⟩, ⟨.output, rows⟩], [], []⟩

def geometry (rows : Nat) : Geometry := ⟨rows, 1, 32⟩

def prologue : List Instruction :=
  [.parameter 8 0, .parameter 9 1, .parameter 7 2,
   .toGlobal 16 9, .blockId 1, .shiftLeft32 5 1 10,
   .toGlobal 10 8, .mulWideSigned32 11 5 2,
   .addSigned64 12 10 (.reg 11), .addSigned64 17 12 (.imm 16),
   .literalFloat 68 0 1, .literal32 6 0]

def term (j : Nat) : List Instruction :=
  [.loadHalf (2*j+1) 17 (((2*j : Nat) : Int) - 16),
   .fromHalf (2*j+4) (2*j+1),
   .loadHalf (2*j+2) 16 (2*j : Nat),
   .fromHalf (2*j+5) (2*j+2),
   .binaryFloat (2*j+36) .mul (2*j+4) (2*j+5),
   .binaryFloat (if j = 15 then 68 else 2*j+37) .add
     (if j = 0 then 68 else 2*j+35) (2*j+36)]

def loopControl : List Instruction :=
  [.addSigned64 17 17 (.imm 32), .addSigned64 16 16 (.imm 32),
   .addSigned32 6 6 (.imm 16), .compareNeSigned32 1 6 (.imm 1024),
   .branch 1 prologue.length]

def epilogue : List Instruction :=
  [.toGlobal 13 7, .toHalf 33 68, .mulWideSigned32 14 1 2,
   .addSigned64 15 13 (.reg 14), .storeHalf 15 0 33, .ret]

def program : List Instruction :=
  prologue ++ (List.range 16).flatMap term ++ loopControl ++ epilogue

theorem prologue_length : prologue.length = 12 := rfl
theorem program_length : program.length = 119 := by decide

theorem program_term : ∀ (j : Fin 16) (q : Fin 6),
    program[12 + 6*j.val + q.val]? = (term j.val)[q.val]? := by decide

theorem step_in_term (ops : Ops α) (rows t j q : Nat) (hj : j < 16) (hq : q < 6)
    (s u : Machine α) (instruction : Instruction)
    (hpc : s.pc = 12 + 6*j + q) (hs : s.registers.stopped = false)
    (hi : (term j)[q]? = some instruction)
    (he : execute ops (layout rows) (geometry rows) t instruction s = some u) :
    Steps ops (layout rows) (geometry rows) t program s u := by
  have hf := program_term ⟨j, hj⟩ ⟨q, hq⟩
  rw [hi] at hf
  apply one_step
  rw [transition_at ops (layout rows) (geometry rows) t program s instruction hs]
  · exact he
  · rw [hpc]
    exact hf

def matrixCell (t c j : Nat) : Location := ⟨.global, 0, 0, t*1024+16*c+j⟩
def vectorCell (c j : Nat) : Location := ⟨.global, 0, 1, 16*c+j⟩
def matrixPointer (t c : Nat) : Pointer := ⟨0, ((t*2048+16+32*c : Nat) : Int), true⟩
def vectorPointer (c : Nat) : Pointer := ⟨1, ((32*c : Nat) : Int), true⟩

theorem matrix_address (t c j : Nat) (ht : t < 512) (hc : c < 64) (hj : j < 16) :
    address (layout 512) (geometry 512) t (matrixPointer t c) (((2*j : Nat) : Int) - 16) false =
      some (matrixCell t c j) := by
  have he : ((t*2048+16+32*c : Nat) : Int) + (((2*j : Nat) : Int) - 16) =
      ((t*1024+16*c+j : Nat) : Int) * 2 := by
    simp only [Int.natCast_add, Int.natCast_mul]
    omega
  have hn : 0 ≤ ((t*1024+16*c+j : Nat) : Int) * 2 := by omega
  have hs : signed64 (((t*1024+16*c+j : Nat) : Int) * 2) := by
    unfold signed64
    simp only [Int.natCast_add, Int.natCast_mul]
    omega
  have hb : t*1024+16*c+j < 512*1024 := by omega
  unfold matrixPointer
  rw [aligned_address (layout 512) (geometry 512) t 0 (t*1024+16*c+j) _ _ false he hs]
  exact read_location _ _ t 0 _ ⟨.input, 512*1024⟩ (by rfl) hb

theorem vector_address (t c j : Nat) (hc : c < 64) (hj : j < 16) :
    address (layout 512) (geometry 512) t (vectorPointer c) (2*j : Nat) false =
      some (vectorCell c j) := by
  have he : ((32*c : Nat) : Int) + ((2*j : Nat) : Int) = ((16*c+j : Nat) : Int) * 2 := by
    simp only [Int.natCast_add, Int.natCast_mul]
    omega
  have hn : 0 ≤ ((16*c+j : Nat) : Int) * 2 := by omega
  have hs : signed64 (((16*c+j : Nat) : Int) * 2) := by
    unfold signed64
    simp only [Int.natCast_add, Int.natCast_mul]
    omega
  have hb : 16*c+j < 1024 := by omega
  unfold vectorPointer
  rw [aligned_address (layout 512) (geometry 512) t 1 (16*c+j) _ _ false he hs]
  exact read_location _ _ t 1 _ ⟨.input, 1024⟩ (by rfl) hb

def inputRegister (j : Nat) : Nat := if j = 0 then 68 else 2*j+35
def sumRegister (j : Nat) : Nat := if j = 15 then 68 else 2*j+37

def termLoadA (t c j : Nat) (a : α) (s : Machine α) : Machine α :=
  loadedHalf s t (2*j+1) (matrixCell t c j) a

def termCastA (ops : Ops α) (t c j : Nat) (a : α) (s : Machine α) : Machine α :=
  setFloat (termLoadA t c j a s) (2*j+4) (ops.fromHalf a)

def termLoadB (ops : Ops α) (t c j : Nat) (a b : α) (s : Machine α) : Machine α :=
  loadedHalf (termCastA ops t c j a s) t (2*j+2) (vectorCell c j) b

def termCastB (ops : Ops α) (t c j : Nat) (a b : α) (s : Machine α) : Machine α :=
  setFloat (termLoadB ops t c j a b s) (2*j+5) (ops.fromHalf b)

def termProduct (ops : Ops α) (t c j : Nat) (a b : α) (s : Machine α) : Machine α :=
  setFloat (termCastB ops t c j a b s) (2*j+36) (ops.mul (ops.fromHalf a) (ops.fromHalf b))

def termResult (ops : Ops α) (t c j : Nat) (a b acc : α) (s : Machine α) : Machine α :=
  setFloat (termProduct ops t c j a b s) (sumRegister j)
    (ops.add acc (ops.mul (ops.fromHalf a) (ops.fromHalf b)))

theorem term_execute (ops : Ops α) (t c j : Nat) (a b acc : α) (s : Machine α)
    (ht : t < 512) (hc : c < 64) (hj : j < 16)
    (hpc : s.pc = 12 + 6*j) (hs : s.registers.stopped = false)
    (hpA : s.registers.pointer 17 = some (matrixPointer t c))
    (hpB : s.registers.pointer 16 = some (vectorPointer c))
    (ha : s.registers.base.memory (matrixCell t c j) = some a)
    (hb : s.registers.base.memory (vectorCell c j) = some b)
    (hacc : s.registers.scalar (inputRegister j) = some acc) :
    Steps ops (layout 512) (geometry 512) t program s (termResult ops t c j a b acc s) := by
  have h1 := step_in_term ops 512 t j 0 hj (by decide) s (termLoadA t c j a s)
    (.loadHalf (2*j+1) 17 (((2*j : Nat) : Int)-16))
    (by simpa only [Nat.add_zero] using hpc) hs (by rfl)
    (loadHalf_step ops (layout 512) (geometry 512) t (2*j+1) 17 _ s _ _ a hpA
      (matrix_address t c j ht hc hj) ha)
  have h2 := step_in_term ops 512 t j 1 hj (by decide)
    (termLoadA t c j a s) (termCastA ops t c j a s) (.fromHalf (2*j+4) (2*j+1))
    (by simp only [termLoadA, loadedHalf_pc]; omega)
    (by change s.registers.stopped = false; exact hs) (by rfl)
    (fromHalf_step ops (layout 512) (geometry 512) t (2*j+4) (2*j+1) _ a
      (by simp [termLoadA]))
  have h3 := step_in_term ops 512 t j 2 hj (by decide)
    (termCastA ops t c j a s) (termLoadB ops t c j a b s)
    (.loadHalf (2*j+2) 16 (2*j : Nat))
    (by simp only [termCastA, termLoadA, setFloat_pc, loadedHalf_pc]; omega)
    (by change s.registers.stopped = false; exact hs) (by rfl)
    (loadHalf_step ops (layout 512) (geometry 512) t (2*j+2) 16 _ _ _ _ b
      (by simpa only [termCastA, termLoadA, setFloat_pointer, loadedHalf_pointer] using hpB)
      (vector_address t c j hc hj)
      (by simpa only [termCastA, termLoadA, setFloat_memory, loadedHalf_memory] using hb))
  have h4 := step_in_term ops 512 t j 3 hj (by decide)
    (termLoadB ops t c j a b s) (termCastB ops t c j a b s) (.fromHalf (2*j+5) (2*j+2))
    (by simp only [termLoadB, termCastA, termLoadA, setFloat_pc, loadedHalf_pc]; omega)
    (by change s.registers.stopped = false; exact hs) (by rfl)
    (fromHalf_step ops (layout 512) (geometry 512) t (2*j+5) (2*j+2) _ b
      (by simp [termLoadB]))
  have hrAB : 2*j+4 ≠ 2*j+5 := by omega
  have h5 := step_in_term ops 512 t j 4 hj (by decide)
    (termCastB ops t c j a b s) (termProduct ops t c j a b s)
    (.binaryFloat (2*j+36) .mul (2*j+4) (2*j+5))
    (by simp only [termCastB, termLoadB, termCastA, termLoadA, setFloat_pc, loadedHalf_pc]; omega)
    (by change s.registers.stopped = false; exact hs) (by rfl)
    (binaryFloat_step ops (layout 512) (geometry 512) t (2*j+36) (2*j+4) (2*j+5) .mul _ _ _
      (by simp [termCastB, termLoadB, termCastA, hrAB])
      (by simp [termCastB]))
  have hrA : inputRegister j ≠ 2*j+4 := by unfold inputRegister; split <;> omega
  have hrB : inputRegister j ≠ 2*j+5 := by unfold inputRegister; split <;> omega
  have hrP : inputRegister j ≠ 2*j+36 := by unfold inputRegister; split <;> omega
  have h6 := step_in_term ops 512 t j 5 hj (by decide)
    (termProduct ops t c j a b s) (termResult ops t c j a b acc s)
    (.binaryFloat (sumRegister j) .add (inputRegister j) (2*j+36))
    (by simp only [termProduct, termCastB, termLoadB, termCastA, termLoadA, setFloat_pc, loadedHalf_pc]; omega)
    (by change s.registers.stopped = false; exact hs) (by rfl)
    (binaryFloat_step ops (layout 512) (geometry 512) t (sumRegister j) (inputRegister j) (2*j+36) .add _ _ _
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

def accumulatorRegister (j : Nat) : Nat := if j = 0 ∨ j = 16 then 68 else 2*j+35

theorem source_accumulator : ∀ j : Fin 16,
    inputRegister j.val = accumulatorRegister j.val ∧
    sumRegister j.val = accumulatorRegister (j.val+1) := by decide

def Reads (input : Nat → Nat → α) (s : Machine α) : Prop :=
  (∀ i, i < 512*1024 → s.registers.base.memory ⟨.global, 0, 0, i⟩ = some (input 0 i)) ∧
  (∀ i, i < 1024 → s.registers.base.memory ⟨.global, 0, 1, i⟩ = some (input 1 i))

structure BodyInvariant (input : Nat → Nat → α) (t c j : Nat) (acc : α) (s : Machine α) : Prop where
  pc : s.pc = 12 + 6*j
  stopped : s.registers.stopped = false
  matrix : s.registers.pointer 17 = some (matrixPointer t c)
  vector : s.registers.pointer 16 = some (vectorPointer c)
  accumulator : s.registers.scalar (accumulatorRegister j) = some acc
  reads : Reads input s
  row : s.registers.i32 1 = some (t : Int)
  counter : s.registers.i32 6 = some ((16*c : Nat) : Int)
  output : s.registers.pointer 7 = some ⟨2, 0, false⟩

def nextValue (ops : Ops α) (input : Nat → Nat → α) (t c j : Nat) (acc : α) : α :=
  ops.add acc (ops.mul (ops.fromHalf (input 0 (t*1024+16*c+j))) (ops.fromHalf (input 1 (16*c+j))))

def chunkStep (ops : Ops α) (input : Nat → Nat → α) (t c j : Nat) (acc : α) (s : Machine α) : Machine α :=
  termResult ops t c j (input 0 (t*1024+16*c+j)) (input 1 (16*c+j)) acc s

theorem chunk_step (ops : Ops α) (input : Nat → Nat → α) (t c j : Nat) (acc : α) (s : Machine α)
    (ht : t < 512) (hc : c < 64) (hj : j < 16) (h : BodyInvariant input t c j acc s) :
    Steps ops (layout 512) (geometry 512) t program s (chunkStep ops input t c j acc s) ∧
    BodyInvariant input t c (j+1) (nextValue ops input t c j acc) (chunkStep ops input t c j acc s) := by
  have hreg := source_accumulator ⟨j, hj⟩
  constructor
  · apply term_execute ops t c j _ _ acc s ht hc hj h.pc h.stopped h.matrix h.vector
    · exact h.reads.1 _ (by omega)
    · exact h.reads.2 _ (by omega)
    · rw [hreg.1]
      exact h.accumulator
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [chunkStep, termResult_pc]
      have hp := h.pc
      omega
    · change s.registers.stopped = false
      exact h.stopped
    · simpa only [chunkStep, termResult_pointer] using h.matrix
    · simpa only [chunkStep, termResult_pointer] using h.vector
    · change (termResult ops t c j _ _ acc s).registers.scalar (accumulatorRegister (j+1)) = _
      rw [← hreg.2]
      exact termResult_scalar ops t c j _ _ acc s
    · change Reads input s
      exact h.reads
    · change s.registers.i32 1 = some (t : Int)
      exact h.row
    · change s.registers.i32 6 = some ((16*c : Nat) : Int)
      exact h.counter
    · simpa only [chunkStep, termResult_pointer] using h.output

def foldTerms (ops : Ops α) (input : Nat → Nat → α) (t c : Nat) : Nat → Nat → α → α
  | _, 0, acc => acc
  | j, r+1, acc => foldTerms ops input t c (j+1) r (nextValue ops input t c j acc)

def unroll (ops : Ops α) (input : Nat → Nat → α) (t c : Nat) : Nat → Nat → α → Machine α → Machine α
  | _, 0, _, s => s
  | j, r+1, acc, s => unroll ops input t c (j+1) r (nextValue ops input t c j acc)
      (chunkStep ops input t c j acc s)

theorem unroll_execute (ops : Ops α) (input : Nat → Nat → α) (t c r j : Nat) (acc : α) (s : Machine α)
    (ht : t < 512) (hc : c < 64) (hcount : j+r ≤ 16) (h : BodyInvariant input t c j acc s) :
    Steps ops (layout 512) (geometry 512) t program s (unroll ops input t c j r acc s) ∧
    BodyInvariant input t c (j+r) (foldTerms ops input t c j r acc) (unroll ops input t c j r acc s) := by
  induction r generalizing j acc s with
  | zero => exact ⟨.refl _, by simpa only [Nat.add_zero, foldTerms, unroll] using h⟩
  | succ r ih =>
      have hj : j < 16 := by omega
      have first := chunk_step ops input t c j acc s ht hc hj h
      have rest := ih (j+1) (nextValue ops input t c j acc) (chunkStep ops input t c j acc s)
        (by omega) first.2
      constructor
      · exact steps_trans _ _ _ _ _ _ _ _ first.1 rest.1
      · have he : j+(r+1) = (j+1)+r := by omega
        simpa only [unroll, foldTerms, he] using rest.2

theorem unroll_memory (ops : Ops α) (input : Nat → Nat → α) (t c r j : Nat) (acc : α) (s : Machine α) :
    (unroll ops input t c j r acc s).registers.base.memory = s.registers.base.memory := by
  induction r generalizing j acc s with
  | zero => rfl
  | succ r ih =>
      simp only [unroll]
      rw [ih]
      rfl

def matrixAdvanced (t c : Nat) (s : Machine α) : Machine α :=
  setPointer s 17 (matrixPointer t (c+1))

def vectorAdvanced (t c : Nat) (s : Machine α) : Machine α :=
  setPointer (matrixAdvanced t c s) 16 (vectorPointer (c+1))

def countedState (t c : Nat) (s : Machine α) : Machine α :=
  setIndex32 (vectorAdvanced t c s) 6 ((16*(c+1) : Nat) : Int)

def comparedState (t c : Nat) (s : Machine α) : Machine α :=
  setPredicate (countedState t c s) 1 (((16*(c+1) : Nat) : Int) != 1024)

def controlResult (t c : Nat) (s : Machine α) : Machine α :=
  { comparedState t c s with pc := if (((16*(c+1) : Nat) : Int) != 1024)
      then 12 else (comparedState t c s).pc+1 }

theorem matrix_control_pointer (t c : Nat) :
    { matrixPointer t c with offset := (matrixPointer t c).offset+32 } =
      matrixPointer t (c+1) := by
  have ho : ((t*2048+16+32*c : Nat) : Int)+32 =
      ((t*2048+16+32*(c+1) : Nat) : Int) := by
    simp only [Int.natCast_add, Int.natCast_mul]
    omega
  exact congrArg (fun off : Int => (⟨0, off, true⟩ : Pointer)) ho

theorem vector_control_pointer (c : Nat) :
    { vectorPointer c with offset := (vectorPointer c).offset+32 } =
      vectorPointer (c+1) := by
  have ho : ((32*c : Nat) : Int)+32 = ((32*(c+1) : Nat) : Int) := by
    simp only [Int.natCast_add, Int.natCast_mul]
    omega
  exact congrArg (fun off : Int => (⟨1, off, true⟩ : Pointer)) ho

theorem control_execute (ops : Ops α) (input : Nat → Nat → α) (t c : Nat) (acc : α) (s : Machine α)
    (ht : t < 512) (hc : c < 64) (h : BodyInvariant input t c 16 acc s) :
    Steps ops (layout 512) (geometry 512) t program s (controlResult t c s) := by
  have hpc : s.pc = 108 := h.pc
  have hgA : signed64 32 ∧ signed64 ((matrixPointer t c).offset + 32) := by
    unfold signed64 matrixPointer
    simp only [Int.natCast_add, Int.natCast_mul]
    omega
  have heA : { matrixPointer t c with offset := (matrixPointer t c).offset+32 } =
      matrixPointer t (c+1) := matrix_control_pointer t c
  have e1 := pointer_add_step ops (layout 512) (geometry 512) t 17 17 (.imm 32)
    (matrixPointer t c) 32 s (pointer_values _ _ _ h.matrix) (by rfl) hgA
  rw [heA] at e1
  have h1 : Steps ops (layout 512) (geometry 512) t program s (matrixAdvanced t c s) := by
    apply one_step
    rw [transition_at ops (layout 512) (geometry 512) t program s (.addSigned64 17 17 (.imm 32))
      h.stopped (by rw [hpc]; rfl)]
    exact e1
  have hpB : (matrixAdvanced t c s).registers.pointer 16 = some (vectorPointer c) := by
    simpa [matrixAdvanced] using h.vector
  have hgB : signed64 32 ∧ signed64 ((vectorPointer c).offset+32) := by
    unfold signed64 vectorPointer
    simp only [Int.natCast_mul]
    omega
  have heB : { vectorPointer c with offset := (vectorPointer c).offset+32 } =
      vectorPointer (c+1) := vector_control_pointer c
  have e2 := pointer_add_step ops (layout 512) (geometry 512) t 16 16 (.imm 32)
    (vectorPointer c) 32 (matrixAdvanced t c s) (pointer_values _ _ _ hpB) (by rfl) hgB
  rw [heB] at e2
  have h2 : Steps ops (layout 512) (geometry 512) t program (matrixAdvanced t c s) (vectorAdvanced t c s) := by
    apply one_step
    rw [transition_at ops (layout 512) (geometry 512) t program (matrixAdvanced t c s)
      (.addSigned64 16 16 (.imm 32))
      (by change s.registers.stopped = false; exact h.stopped)
      (by simp only [matrixAdvanced, setPointer_pc, hpc]; rfl)]
    exact e2
  have hcounter : (vectorAdvanced t c s).registers.i32 6 = some ((16*c : Nat) : Int) := by
    change s.registers.i32 6 = _
    exact h.counter
  have hgC : signed32 ((16*c : Nat) : Int) ∧ signed32 16 ∧ signed32 (((16*c : Nat) : Int)+16) := by
    unfold signed32
    simp only [Int.natCast_mul]
    omega
  have heC : ((16*c : Nat) : Int)+16 = ((16*(c+1) : Nat) : Int) := by
    simp only [Int.natCast_mul, Int.natCast_add]
    omega
  have e3 := add32_step ops (layout 512) (geometry 512) t 6 6 (.imm 16)
    (vectorAdvanced t c s) ((16*c : Nat) : Int) 16 hcounter (by rfl) hgC
  rw [heC] at e3
  have h3 : Steps ops (layout 512) (geometry 512) t program (vectorAdvanced t c s) (countedState t c s) := by
    apply one_step
    rw [transition_at ops (layout 512) (geometry 512) t program (vectorAdvanced t c s)
      (.addSigned32 6 6 (.imm 16))
      (by change s.registers.stopped = false; exact h.stopped)
      (by simp only [vectorAdvanced, matrixAdvanced, setPointer_pc, hpc]; rfl)]
    exact e3
  have hgP : signed32 ((16*(c+1) : Nat) : Int) ∧ signed32 1024 := by
    unfold signed32
    simp only [Int.natCast_mul, Int.natCast_add]
    omega
  have e4 := compare_ne_step ops (layout 512) (geometry 512) t 1 6 (.imm 1024)
    (countedState t c s) ((16*(c+1) : Nat) : Int) 1024 (by simp [countedState]) (by rfl) hgP
  have h4 : Steps ops (layout 512) (geometry 512) t program (countedState t c s) (comparedState t c s) := by
    apply one_step
    rw [transition_at ops (layout 512) (geometry 512) t program (countedState t c s)
      (.compareNeSigned32 1 6 (.imm 1024))
      (by change s.registers.stopped = false; exact h.stopped)
      (by simp only [countedState, vectorAdvanced, matrixAdvanced, setIndex32_pc, setPointer_pc, hpc]; rfl)]
    exact e4
  have h5 : Steps ops (layout 512) (geometry 512) t program (comparedState t c s) (controlResult t c s) := by
    apply one_step
    rw [transition_at ops (layout 512) (geometry 512) t program (comparedState t c s) (.branch 1 12)
      (by change s.registers.stopped = false; exact h.stopped)
      (by simp only [comparedState, countedState, vectorAdvanced, matrixAdvanced,
          setPredicate_pc, setIndex32_pc, setPointer_pc, hpc]; rfl)]
    simp only [execute, comparedState, setPredicate, bind, pure, Option.bind]
    rfl
  apply steps_trans _ _ _ _ _ _ _ _ h1
  apply steps_trans _ _ _ _ _ _ _ _ h2
  apply steps_trans _ _ _ _ _ _ _ _ h3
  exact steps_trans _ _ _ _ _ _ _ _ h4 h5

theorem control_pc (t c : Nat) (s : Machine α) (hc : c < 64) (hpc : s.pc = 108) :
    (controlResult t c s).pc = if c+1 < 64 then 12 else 113 := by
  by_cases hnext : c+1 < 64
  · have hn : (16 : Int) * ((c : Int)+1) ≠ 1024 := by omega
    simp [controlResult, hn, hnext]
  · have he : c+1 = 64 := by omega
    simp [controlResult, comparedState, countedState, vectorAdvanced, matrixAdvanced, he, hnext, hpc]

structure LoopInvariant (input : Nat → Nat → α) (t c : Nat) (acc : α) (s : Machine α) : Prop where
  pc : s.pc = if c < 64 then 12 else 113
  stopped : s.registers.stopped = false
  matrix : s.registers.pointer 17 = some (matrixPointer t c)
  vector : s.registers.pointer 16 = some (vectorPointer c)
  accumulator : s.registers.scalar 68 = some acc
  reads : Reads input s
  row : s.registers.i32 1 = some (t : Int)
  counter : s.registers.i32 6 = some ((16*c : Nat) : Int)
  output : s.registers.pointer 7 = some ⟨2, 0, false⟩

theorem control_invariant (input : Nat → Nat → α) (t c : Nat) (acc : α) (s : Machine α)
    (hc : c < 64) (h : BodyInvariant input t c 16 acc s) :
    LoopInvariant input t (c+1) acc (controlResult t c s) := by
  refine ⟨control_pc t c s hc h.pc, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change s.registers.stopped = false
    exact h.stopped
  · rfl
  · rfl
  · change s.registers.scalar 68 = some acc
    simpa [accumulatorRegister] using h.accumulator
  · change Reads input s
    exact h.reads
  · change s.registers.i32 1 = some (t : Int)
    exact h.row
  · rfl
  · change s.registers.pointer 7 = some ⟨2, 0, false⟩
    exact h.output

theorem loop_body (input : Nat → Nat → α) (t c : Nat) (acc : α) (s : Machine α)
    (hc : c < 64) (h : LoopInvariant input t c acc s) :
    BodyInvariant input t c 0 acc s := by
  refine ⟨?_, h.stopped, h.matrix, h.vector, ?_, h.reads, h.row, h.counter, h.output⟩
  · simpa [hc] using h.pc
  · simpa [accumulatorRegister] using h.accumulator

def iteration (ops : Ops α) (input : Nat → Nat → α) (t c : Nat) (acc : α) (s : Machine α) : Machine α :=
  controlResult t c (unroll ops input t c 0 16 acc s)

theorem iteration_execute (ops : Ops α) (input : Nat → Nat → α) (t c : Nat) (acc : α) (s : Machine α)
    (ht : t < 512) (hc : c < 64) (h : LoopInvariant input t c acc s) :
    Steps ops (layout 512) (geometry 512) t program s (iteration ops input t c acc s) ∧
    LoopInvariant input t (c+1) (foldTerms ops input t c 0 16 acc) (iteration ops input t c acc s) := by
  have body := unroll_execute ops input t c 16 0 acc s ht hc (by decide) (loop_body input t c acc s hc h)
  have control := control_execute ops input t c _ _ ht hc body.2
  exact ⟨steps_trans _ _ _ _ _ _ _ _ body.1 control, control_invariant input t c _ _ hc body.2⟩

theorem control_memory (t c : Nat) (s : Machine α) :
    (controlResult t c s).registers.base.memory = s.registers.base.memory := rfl

theorem iteration_memory (ops : Ops α) (input : Nat → Nat → α) (t c : Nat) (acc : α) (s : Machine α) :
    (iteration ops input t c acc s).registers.base.memory = s.registers.base.memory := by
  simp only [iteration, control_memory, unroll_memory]

def foldChunks (ops : Ops α) (input : Nat → Nat → α) (t : Nat) : Nat → Nat → α → α
  | _, 0, acc => acc
  | c, r+1, acc => foldChunks ops input t (c+1) r (foldTerms ops input t c 0 16 acc)

def runChunks (ops : Ops α) (input : Nat → Nat → α) (t : Nat) : Nat → Nat → α → Machine α → Machine α
  | _, 0, _, s => s
  | c, r+1, acc, s => runChunks ops input t (c+1) r (foldTerms ops input t c 0 16 acc)
      (iteration ops input t c acc s)

theorem runChunks_execute (ops : Ops α) (input : Nat → Nat → α) (t c r : Nat) (acc : α) (s : Machine α)
    (ht : t < 512) (hcount : c+r ≤ 64) (h : LoopInvariant input t c acc s) :
    Steps ops (layout 512) (geometry 512) t program s (runChunks ops input t c r acc s) ∧
    LoopInvariant input t (c+r) (foldChunks ops input t c r acc) (runChunks ops input t c r acc s) := by
  induction r generalizing c acc s with
  | zero => exact ⟨.refl _, by simpa only [Nat.add_zero, foldChunks, runChunks] using h⟩
  | succ r ih =>
      have hc : c < 64 := by omega
      have first := iteration_execute ops input t c acc s ht hc h
      have rest := ih (c+1) (foldTerms ops input t c 0 16 acc) (iteration ops input t c acc s)
        (by omega) first.2
      constructor
      · exact steps_trans _ _ _ _ _ _ _ _ first.1 rest.1
      · have he : c+(r+1) = (c+1)+r := by omega
        simpa only [runChunks, foldChunks, he] using rest.2

theorem runChunks_memory (ops : Ops α) (input : Nat → Nat → α) (t c r : Nat) (acc : α) (s : Machine α) :
    (runChunks ops input t c r acc s).registers.base.memory = s.registers.base.memory := by
  induction r generalizing c acc s with
  | zero => rfl
  | succ r ih =>
      simp only [runChunks]
      rw [ih, iteration_memory]

def start (s : State α) : Machine α := { registers := { base := s } }

def parameterA (s : State α) : Machine α :=
  advance (start s) (putPointer (start s).registers 8 ⟨0, 0, false⟩)

def parameterAB (s : State α) : Machine α :=
  advance (parameterA s) (putPointer (parameterA s).registers 9 ⟨1, 0, false⟩)

def parameterState (s : State α) : Machine α :=
  advance (parameterAB s) (putPointer (parameterAB s).registers 7 ⟨2, 0, false⟩)

theorem parameters_execute (ops : Ops α) (rows t : Nat) (s : State α) :
    Steps ops (layout rows) (geometry rows) t program (start s) (parameterState s) := by
  exact .next (u := parameterA s) (by rfl)
    (.next (u := parameterAB s) (by rfl)
      (.next (u := parameterState s) (by rfl) (.refl _)))

theorem parameterState_memory (s : State α) :
    (parameterState s).registers.base = s := rfl

theorem parameterState_pc (s : State α) : (parameterState s).pc = 3 := rfl

def vectorState (s : State α) : Machine α :=
  advance (parameterState s) (putPointer (parameterState s).registers 16 ⟨1, 0, true⟩)

def indexedState (t : Nat) (s : State α) : Machine α :=
  advance (vectorState s) (putI32 (vectorState s).registers 1 t)

theorem vector_execute (ops : Ops α) (rows t : Nat) (s : State α) :
    Steps ops (layout rows) (geometry rows) t program (parameterState s) (vectorState s) :=
  .next (by rfl) (.refl _)

theorem index_execute (ops : Ops α) (rows t : Nat) (s : State α) (ht : t < 512) :
    Steps ops (layout rows) (geometry rows) t program (vectorState s) (indexedState t s) := by
  have hblock : 0 < (geometry rows).block ∧ t / (geometry rows).block < 4294967296 := by
    simp only [geometry, Nat.div_one]
    omega
  have h := blockId_step ops (layout rows) (geometry rows) t 1 (vectorState s) hblock
  have hnormalized : execute ops (layout rows) (geometry rows) t (.blockId 1) (vectorState s) =
      some (indexedState t s) := by
    simpa only [indexedState, geometry, Nat.div_one] using h
  apply one_step
  rw [transition_at ops (layout rows) (geometry rows) t program (vectorState s) (.blockId 1)
      (by rfl) (by rfl)]
  exact hnormalized

def rowState (t : Nat) (s : State α) : Machine α :=
  advance (indexedState t s) (putI32 (indexedState t s).registers 5 ((t*1024 : Nat) : Int))

def matrixGlobalState (t : Nat) (s : State α) : Machine α :=
  advance (rowState t s) (putPointer (rowState t s).registers 10 ⟨0, 0, true⟩)

def wideState (t : Nat) (s : State α) : Machine α :=
  advance (matrixGlobalState t s) (putI64 (matrixGlobalState t s).registers 11 ((t*2048 : Nat) : Int))

def matrixState (t : Nat) (s : State α) : Machine α :=
  advance (wideState t s) (putPointer (wideState t s).registers 12 ⟨0, ((t*2048 : Nat) : Int), true⟩)

def matrixOffsetState (t : Nat) (s : State α) : Machine α :=
  advance (matrixState t s) (putPointer (matrixState t s).registers 17 ⟨0, ((t*2048+16 : Nat) : Int), true⟩)

def zeroState (ops : Ops α) (t : Nat) (s : State α) : Machine α :=
  advance (matrixOffsetState t s)
    (putScalar (matrixOffsetState t s).registers 68 (ops.literal 0 1))

def initializedState (ops : Ops α) (t : Nat) (s : State α) : Machine α :=
  advance (zeroState ops t s) (putI32 (zeroState ops t s).registers 6 0)

theorem row_execute (ops : Ops α) (rows t : Nat) (s : State α) (ht : t < 512) :
    Steps ops (layout rows) (geometry rows) t program (indexedState t s) (rowState t s) := by
  have hu : unsigned32 (t : Int) := by unfold unsigned32; omega
  have hp : (2 : Int) ^ min 10 32 = 1024 := by decide
  have hm : ((t : Int) * 1024) % 4294967296 = ((t*1024 : Nat) : Int) := by
    simp only [Int.natCast_mul]
    omega
  have h := shiftLeft_step ops (layout rows) (geometry rows) t 5 1 10 (indexedState t s) t
    (by rfl) hu
  rw [hp, hm] at h
  apply one_step
  rw [transition_at ops (layout rows) (geometry rows) t program (indexedState t s)
      (.shiftLeft32 5 1 10) (by rfl) (by rfl)]
  exact h

theorem matrix_global_execute (ops : Ops α) (rows t : Nat) (s : State α) :
    Steps ops (layout rows) (geometry rows) t program (rowState t s) (matrixGlobalState t s) :=
  .next (by rfl) (.refl _)

theorem wide_execute (ops : Ops α) (rows t : Nat) (s : State α) (ht : t < 512) :
    Steps ops (layout rows) (geometry rows) t program (matrixGlobalState t s) (wideState t s) := by
  have hb : signed32 ((t*1024 : Nat) : Int) ∧ signed32 2 ∧
      signed64 (((t*1024 : Nat) : Int) * 2) := by
    unfold signed32 signed64
    simp only [Int.natCast_mul]
    omega
  have hm : (((t*1024 : Nat) : Int) * 2) = ((t*2048 : Nat) : Int) := by
    simp only [Int.natCast_mul]
    omega
  have h := wide_step ops (layout rows) (geometry rows) t 11 5 2 ((t*1024 : Nat) : Int)
    (matrixGlobalState t s) (by rfl) hb
  rw [hm] at h
  apply one_step
  rw [transition_at ops (layout rows) (geometry rows) t program (matrixGlobalState t s)
      (.mulWideSigned32 11 5 2) (by rfl) (by rfl)]
  exact h

theorem matrix_address_execute (ops : Ops α) (rows t : Nat) (s : State α) (ht : t < 512) :
    Steps ops (layout rows) (geometry rows) t program (wideState t s) (matrixState t s) := by
  have hb : signed64 ((t*2048 : Nat) : Int) ∧ signed64 (0 + ((t*2048 : Nat) : Int)) := by
    unfold signed64
    simp only [Int.natCast_mul]
    omega
  have h := pointer_add_step ops (layout rows) (geometry rows) t 12 10 (.reg 11)
    ⟨0, 0, true⟩ ((t*2048 : Nat) : Int) (wideState t s) (by rfl) (by rfl) hb
  simp only [Int.zero_add] at h
  apply one_step
  rw [transition_at ops (layout rows) (geometry rows) t program (wideState t s)
      (.addSigned64 12 10 (.reg 11)) (by rfl) (by rfl)]
  exact h

theorem matrix_offset_execute (ops : Ops α) (rows t : Nat) (s : State α) (ht : t < 512) :
    Steps ops (layout rows) (geometry rows) t program (matrixState t s) (matrixOffsetState t s) := by
  have hb : signed64 16 ∧ signed64 (((t*2048 : Nat) : Int) + 16) := by
    unfold signed64
    simp only [Int.natCast_mul]
    omega
  have h := pointer_add_step ops (layout rows) (geometry rows) t 17 12 (.imm 16)
    ⟨0, ((t*2048 : Nat) : Int), true⟩ 16 (matrixState t s) (by rfl) (by rfl) hb
  have he : ((t*2048 : Nat) : Int) + 16 = ((t*2048+16 : Nat) : Int) := by omega
  rw [he] at h
  apply one_step
  rw [transition_at ops (layout rows) (geometry rows) t program (matrixState t s)
      (.addSigned64 17 12 (.imm 16)) (by rfl) (by rfl)]
  exact h

theorem zero_execute (ops : Ops α) (rows t : Nat) (s : State α) :
    Steps ops (layout rows) (geometry rows) t program (matrixOffsetState t s) (zeroState ops t s) :=
  .next (by rfl) (.refl _)

theorem initialize_execute (ops : Ops α) (rows t : Nat) (s : State α) :
    Steps ops (layout rows) (geometry rows) t program (zeroState ops t s) (initializedState ops t s) :=
  .next (by rfl) (.refl _)

theorem prologue_execute (ops : Ops α) (rows t : Nat) (s : State α) (ht : t < 512) :
    Steps ops (layout rows) (geometry rows) t program (start s) (initializedState ops t s) := by
  apply steps_trans _ _ _ _ _ _ _ _ (parameters_execute ops rows t s)
  apply steps_trans _ _ _ _ _ _ _ _ (vector_execute ops rows t s)
  apply steps_trans _ _ _ _ _ _ _ _ (index_execute ops rows t s ht)
  apply steps_trans _ _ _ _ _ _ _ _ (row_execute ops rows t s ht)
  apply steps_trans _ _ _ _ _ _ _ _ (matrix_global_execute ops rows t s)
  apply steps_trans _ _ _ _ _ _ _ _ (wide_execute ops rows t s ht)
  apply steps_trans _ _ _ _ _ _ _ _ (matrix_address_execute ops rows t s ht)
  apply steps_trans _ _ _ _ _ _ _ _ (matrix_offset_execute ops rows t s ht)
  exact steps_trans _ _ _ _ _ _ _ _ (zero_execute ops rows t s) (initialize_execute ops rows t s)

theorem initialized_pc (ops : Ops α) (t : Nat) (s : State α) :
    (initializedState ops t s).pc = 12 := rfl

theorem initialized_memory (ops : Ops α) (t : Nat) (s : State α) :
    (initializedState ops t s).registers.base = s := rfl

theorem initialized_loop (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α)
    (hreads : Reads input (start s)) :
    LoopInvariant input t 0 (ops.literal 0 1) (initializedState ops t s) := by
  refine ⟨by rfl, by rfl, by rfl, by rfl, by rfl, ?_, by rfl, by rfl, by rfl⟩
  change Reads input (start s)
  exact hreads

def dotValue (ops : Ops α) (input : Nat → Nat → α) (t : Nat) : α :=
  foldChunks ops input t 0 64 (ops.literal 0 1)

def loopExit (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) : Machine α :=
  runChunks ops input t 0 64 (ops.literal 0 1) (initializedState ops t s)

theorem source_to_loop_exit (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α)
    (ht : t < 512) (hreads : Reads input (start s)) :
    Steps ops (layout 512) (geometry 512) t program (start s) (loopExit ops input t s) ∧
    LoopInvariant input t 64 (dotValue ops input t) (loopExit ops input t s) := by
  have loop := runChunks_execute ops input t 0 64 (ops.literal 0 1) (initializedState ops t s)
    ht (by decide) (initialized_loop ops input t s hreads)
  exact ⟨steps_trans _ _ _ _ _ _ _ _ (prologue_execute ops 512 t s ht) loop.1, loop.2⟩

theorem loopExit_memory (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) :
    (loopExit ops input t s).registers.base.memory = s.memory := by
  simp only [loopExit, runChunks_memory]
  rfl

def outputCell (t : Nat) : Location := ⟨.global, 0, 2, t⟩

def exitGlobal (s : Machine α) : Machine α := setPointer s 13 ⟨2, 0, true⟩

def exitHalf (ops : Ops α) (acc : α) (s : Machine α) : Machine α :=
  setHalf (exitGlobal s) 33 (ops.toHalf acc)

def exitWide (ops : Ops α) (t : Nat) (acc : α) (s : Machine α) : Machine α :=
  advance (exitHalf ops acc s) (putI64 (exitHalf ops acc s).registers 14 ((t*2 : Nat) : Int))

def exitAddress (ops : Ops α) (t : Nat) (acc : α) (s : Machine α) : Machine α :=
  setPointer (exitWide ops t acc s) 15 ⟨2, ((t*2 : Nat) : Int), true⟩

def exitStored (ops : Ops α) (t : Nat) (acc : α) (s : Machine α) : Machine α :=
  storedHalf (exitAddress ops t acc s) t (outputCell t) (ops.toHalf acc)

def exitReturned (ops : Ops α) (t : Nat) (acc : α) (s : Machine α) : Machine α :=
  returned (exitStored ops t acc s)

theorem output_address (t : Nat) (ht : t < 512) :
    address (layout 512) (geometry 512) t ⟨2, ((t*2 : Nat) : Int), true⟩ 0 true =
      some (outputCell t) := by
  have hs : signed64 ((t : Int)*2) := by unfold signed64; omega
  have hrole : (Role.output == Role.input) = false := rfl
  rw [aligned_address (layout 512) (geometry 512) t 2 t _ 0 true (by simp) hs]
  simp [location, layout, ht, outputCell, hrole]

theorem epilogue_execute (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (acc : α) (s : Machine α)
    (ht : t < 512) (h : LoopInvariant input t 64 acc s) :
    Steps ops (layout 512) (geometry 512) t program s (exitReturned ops t acc s) := by
  have hpc : s.pc = 113 := by simpa using h.pc
  have e1 := global_step ops (layout 512) (geometry 512) t 13 7 s ⟨2, 0, false⟩ h.output
  have h1 : Steps ops (layout 512) (geometry 512) t program s (exitGlobal s) := by
    apply one_step
    rw [transition_at ops (layout 512) (geometry 512) t program s (.toGlobal 13 7)
      h.stopped (by rw [hpc]; rfl)]
    exact e1
  have e2 := half_step ops (layout 512) (geometry 512) t 33 68 (exitGlobal s) acc
    (by change s.registers.scalar 68 = some acc; exact h.accumulator)
  have h2 : Steps ops (layout 512) (geometry 512) t program (exitGlobal s) (exitHalf ops acc s) := by
    apply one_step
    rw [transition_at ops (layout 512) (geometry 512) t program (exitGlobal s) (.toHalf 33 68)
      (by change s.registers.stopped = false; exact h.stopped)
      (by change program[s.pc+1]? = _; rw [hpc]; rfl)]
    exact e2
  have hb : signed32 (t : Int) ∧ signed32 2 ∧ signed64 ((t : Int)*2) := by
    unfold signed32 signed64
    omega
  have e3 := wide_step ops (layout 512) (geometry 512) t 14 1 2 (t : Int) (exitHalf ops acc s)
    (by change s.registers.i32 1 = some (t : Int); exact h.row) hb
  have he : (t : Int)*2 = ((t*2 : Nat) : Int) := by simp
  rw [he] at e3
  have h3 : Steps ops (layout 512) (geometry 512) t program (exitHalf ops acc s) (exitWide ops t acc s) := by
    apply one_step
    rw [transition_at ops (layout 512) (geometry 512) t program (exitHalf ops acc s)
      (.mulWideSigned32 14 1 2)
      (by change s.registers.stopped = false; exact h.stopped)
      (by change program[(s.pc+1)+1]? = _; rw [hpc]; rfl)]
    exact e3
  have hp : signed64 ((t*2 : Nat) : Int) ∧ signed64 (0+((t*2 : Nat) : Int)) := by
    unfold signed64
    simp only [Int.natCast_mul]
    omega
  have e4 := pointer_add_step ops (layout 512) (geometry 512) t 15 13 (.reg 14) ⟨2, 0, true⟩
    ((t*2 : Nat) : Int) (exitWide ops t acc s) (by rfl) (by rfl) hp
  simp only [Int.zero_add] at e4
  have h4 : Steps ops (layout 512) (geometry 512) t program (exitWide ops t acc s) (exitAddress ops t acc s) := by
    apply one_step
    rw [transition_at ops (layout 512) (geometry 512) t program (exitWide ops t acc s)
      (.addSigned64 15 13 (.reg 14))
      (by change s.registers.stopped = false; exact h.stopped)
      (by change program[((s.pc+1)+1)+1]? = _; rw [hpc]; rfl)]
    exact e4
  have e5 := store_step ops (layout 512) (geometry 512) t 15 33 0 (exitAddress ops t acc s)
    ⟨2, ((t*2 : Nat) : Int), true⟩ (outputCell t) (ops.toHalf acc) (by rfl) (output_address t ht) (by rfl)
  have h5 : Steps ops (layout 512) (geometry 512) t program (exitAddress ops t acc s) (exitStored ops t acc s) := by
    apply one_step
    rw [transition_at ops (layout 512) (geometry 512) t program (exitAddress ops t acc s)
      (.storeHalf 15 0 33)
      (by change s.registers.stopped = false; exact h.stopped)
      (by change program[(((s.pc+1)+1)+1)+1]? = _; rw [hpc]; rfl)]
    exact e5
  have h6 : Steps ops (layout 512) (geometry 512) t program (exitStored ops t acc s) (exitReturned ops t acc s) := by
    apply one_step
    rw [transition_at ops (layout 512) (geometry 512) t program (exitStored ops t acc s) .ret
      (by change s.registers.stopped = false; exact h.stopped)
      (by change program[((((s.pc+1)+1)+1)+1)+1]? = _; rw [hpc]; rfl)]
    exact return_step ops (layout 512) (geometry 512) t _
  apply steps_trans _ _ _ _ _ _ _ _ h1
  apply steps_trans _ _ _ _ _ _ _ _ h2
  apply steps_trans _ _ _ _ _ _ _ _ h3
  apply steps_trans _ _ _ _ _ _ _ _ h4
  exact steps_trans _ _ _ _ _ _ _ _ h5 h6

theorem exitReturned_stopped (ops : Ops α) (t : Nat) (acc : α) (s : Machine α) :
    (exitReturned ops t acc s).registers.stopped = true := rfl

theorem exitReturned_memory (ops : Ops α) (t : Nat) (acc : α) (s : Machine α) :
    (exitReturned ops t acc s).registers.base.memory =
      fun l => if l = outputCell t then some (ops.toHalf acc) else s.registers.base.memory l := rfl

def laneResult (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) : Machine α :=
  exitReturned ops t (dotValue ops input t) (loopExit ops input t s)

theorem source_to_return (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α)
    (ht : t < 512) (hreads : Reads input (start s)) :
    Steps ops (layout 512) (geometry 512) t program (start s) (laneResult ops input t s) ∧
    (laneResult ops input t s).registers.stopped = true := by
  have loop := source_to_loop_exit ops input t s ht hreads
  exact ⟨steps_trans _ _ _ _ _ _ _ _ loop.1 (epilogue_execute ops input t _ _ ht loop.2), rfl⟩

theorem laneResult_memory (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) :
    (laneResult ops input t s).registers.base.memory =
      fun l => if l = outputCell t then some (ops.toHalf (dotValue ops input t)) else s.memory l := by
  simp only [laneResult, exitReturned_memory, loopExit_memory]

def referenceTerm (ops : Ops α) (input : Nat → Nat → α) (t k : Nat) (acc : α) : α :=
  ops.add acc (ops.mul (ops.fromHalf (input 0 (t*1024+k))) (ops.fromHalf (input 1 k)))

def referenceFold (ops : Ops α) (input : Nat → Nat → α) (t : Nat) : Nat → Nat → α → α
  | _, 0, acc => acc
  | k, r+1, acc => referenceFold ops input t (k+1) r (referenceTerm ops input t k acc)

theorem foldTerms_reference (ops : Ops α) (input : Nat → Nat → α) (t c j r : Nat) (acc : α) :
    foldTerms ops input t c j r acc = referenceFold ops input t (16*c+j) r acc := by
  induction r generalizing j acc with
  | zero => rfl
  | succ r ih =>
      simp only [foldTerms, ih, referenceFold, nextValue, referenceTerm, Nat.add_assoc]

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
      rw [foldChunks, ih, foldTerms_reference]
      have he : 16*(r+1) = 16+16*r := by omega
      rw [he, referenceFold_append]
      have hc : 16*(c+1) = 16*c+16 := by omega
      simp only [hc, Nat.add_zero]

def reference (ops : Ops α) (input : Nat → Nat → α) (t : Nat) : α :=
  ops.toHalf (referenceFold ops input t 0 1024 (ops.literal 0 1))

theorem dotValue_reference (ops : Ops α) (input : Nat → Nat → α) (t : Nat) :
    ops.toHalf (dotValue ops input t) = reference ops input t := by
  unfold dotValue reference
  rw [foldChunks_reference]

theorem laneResult_reference (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) :
    (laneResult ops input t s).registers.base.memory =
      fun l => if l = outputCell t then some (reference ops input t) else s.memory l := by
  rw [laneResult_memory, dotValue_reference]

end Gemv

#print axioms steps_trans
#print axioms one_step
#print axioms transition_halted
#print axioms branch_uninitialized
#print axioms Gemv.program_length
#print axioms Gemv.parameters_execute
#print axioms transition_at
#print axioms blockId_step
#print axioms Gemv.vector_execute
#print axioms Gemv.index_execute
#print axioms shiftLeft_step
#print axioms wide_step
#print axioms pointer_add_step
#print axioms Gemv.prologue_execute
#print axioms Gemv.program_term
#print axioms loadHalf_step
#print axioms fromHalf_step
#print axioms binaryFloat_step
#print axioms Gemv.step_in_term
#print axioms Gemv.matrix_address
#print axioms Gemv.vector_address
#print axioms Gemv.term_execute
#print axioms Gemv.chunk_step
#print axioms Gemv.unroll_execute
#print axioms Gemv.unroll_memory
#print axioms pointer_values
#print axioms add32_step
#print axioms compare_ne_step
#print axioms Gemv.control_execute
#print axioms Gemv.control_pc
#print axioms Gemv.matrix_control_pointer
#print axioms Gemv.vector_control_pointer
#print axioms Gemv.control_invariant
#print axioms Gemv.loop_body
#print axioms Gemv.iteration_execute
#print axioms Gemv.control_memory
#print axioms Gemv.iteration_memory
#print axioms Gemv.runChunks_execute
#print axioms Gemv.runChunks_memory
#print axioms Gemv.initialized_loop
#print axioms Gemv.source_to_loop_exit
#print axioms Gemv.loopExit_memory
#print axioms global_step
#print axioms half_step
#print axioms store_step
#print axioms return_step
#print axioms Gemv.output_address
#print axioms Gemv.epilogue_execute
#print axioms Gemv.exitReturned_stopped
#print axioms Gemv.exitReturned_memory
#print axioms Gemv.source_to_return
#print axioms Gemv.laneResult_memory
#print axioms Gemv.foldTerms_reference
#print axioms Gemv.referenceFold_append
#print axioms Gemv.foldChunks_reference
#print axioms Gemv.dotValue_reference
#print axioms Gemv.laneResult_reference
end LarkPtxDot
