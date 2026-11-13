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
end LarkPtxDot
