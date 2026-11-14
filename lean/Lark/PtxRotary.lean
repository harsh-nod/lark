import Lark.PtxMatrix

/-!
Predicate and unconditional-branch instructions used by the unchanged compiled
FP16 interleaved RoPE program. Every operand reads the actual typed register
or predicate state. Uninitialized operands fail; predicates are not assumed.

The guarded abstract model remains separate from IEEE and NVIDIA conformance.
These instruction lemmas alone establish no RoPE kernel or launch theorem.
-/
namespace LarkPtxRotary
open LarkNonlinear LarkPtxPointwise LarkPtxDot
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

inductive Instruction where
  | base : LarkPtxMatrix.Instruction → Instruction
  | compareEqBits32 : Nat → Nat → Operand → Instruction
  | predicateLiteral : Nat → Bool → Instruction
  | predicateXor : Nat → Nat → Nat → Instruction
  | predicateNot : Nat → Nat → Instruction
  | branchAlways : Nat → Instruction
  deriving DecidableEq, Repr

def validBits32 (value : Int) : Prop := -2147483648 ≤ value ∧ value < 4294967296
instance (value : Int) : Decidable (validBits32 value) :=
  inferInstanceAs (Decidable (-2147483648 ≤ value ∧ value < 4294967296))

def execute (ops : Ops α) (layout : Layout) (g : Geometry) (t : Nat)
    (instruction : Instruction) (s : Machine α) : Option (Machine α) := do
  match instruction with
  | .base instruction => LarkPtxMatrix.execute ops layout g t instruction s
  | .compareEqBits32 d a b =>
      let x ← s.registers.i32 a
      let y ← operand32 s.registers b
      if validBits32 x ∧ validBits32 y then
        some (setPredicate s d (LarkPtxMatrix.bits32 x == LarkPtxMatrix.bits32 y))
      else none
  | .predicateLiteral d value => some (setPredicate s d value)
  | .predicateXor d a b =>
      let x ← s.predicates a
      let y ← s.predicates b
      some (setPredicate s d (x != y))
  | .predicateNot d a =>
      let x ← s.predicates a
      some (setPredicate s d (!x))
  | .branchAlways target => some { s with pc := target }

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

theorem transition_halted (ops : Ops α) (layout : Layout) (g : Geometry) (t : Nat)
    (program : List Instruction) (s : Machine α) (h : s.registers.stopped = true) :
    transition ops layout g t program s = none := by
  simp [transition, h]

theorem base_step (ops : Ops α) (layout : Layout) (g : Geometry) (t : Nat)
    (instruction : LarkPtxMatrix.Instruction) (s : Machine α) :
    execute ops layout g t (.base instruction) s =
      LarkPtxMatrix.execute ops layout g t instruction s := rfl

theorem compare_step (ops : Ops α) (layout : Layout) (g : Geometry)
    (t d a : Nat) (b : Operand) (x y : Int) (s : Machine α)
    (hx : s.registers.i32 a = some x) (hy : operand32 s.registers b = some y)
    (hb : validBits32 x ∧ validBits32 y) :
    execute ops layout g t (.compareEqBits32 d a b) s =
      some (setPredicate s d (LarkPtxMatrix.bits32 x == LarkPtxMatrix.bits32 y)) := by
  simp [execute, hx, hy, hb]

theorem predicate_literal_step (ops : Ops α) (layout : Layout) (g : Geometry)
    (t d : Nat) (value : Bool) (s : Machine α) :
    execute ops layout g t (.predicateLiteral d value) s = some (setPredicate s d value) := rfl

theorem predicate_xor_step (ops : Ops α) (layout : Layout) (g : Geometry)
    (t d a b : Nat) (x y : Bool) (s : Machine α)
    (hx : s.predicates a = some x) (hy : s.predicates b = some y) :
    execute ops layout g t (.predicateXor d a b) s = some (setPredicate s d (x != y)) := by
  simp [execute, hx, hy]

theorem predicate_not_step (ops : Ops α) (layout : Layout) (g : Geometry)
    (t d a : Nat) (x : Bool) (s : Machine α) (hx : s.predicates a = some x) :
    execute ops layout g t (.predicateNot d a) s = some (setPredicate s d (!x)) := by
  simp [execute, hx]

theorem branch_always_step (ops : Ops α) (layout : Layout) (g : Geometry)
    (t target : Nat) (s : Machine α) :
    execute ops layout g t (.branchAlways target) s = some { s with pc := target } := rfl

theorem predicate_not_uninitialized (ops : Ops α) (layout : Layout) (g : Geometry)
    (t d a : Nat) (s : Machine α) (h : s.predicates a = none) :
    execute ops layout g t (.predicateNot d a) s = none := by
  simp [execute, h]

theorem predicate_xor_uninitialized_left (ops : Ops α) (layout : Layout) (g : Geometry)
    (t d a b : Nat) (s : Machine α) (h : s.predicates a = none) :
    execute ops layout g t (.predicateXor d a b) s = none := by
  simp [execute, h]

theorem predicate_xor_uninitialized_right (ops : Ops α) (layout : Layout) (g : Geometry)
    (t d a b : Nat) (x : Bool) (s : Machine α)
    (hx : s.predicates a = some x) (hy : s.predicates b = none) :
    execute ops layout g t (.predicateXor d a b) s = none := by
  simp [execute, hx, hy]

#print axioms steps_trans
#print axioms one_step
#print axioms transition_at
#print axioms transition_halted
#print axioms base_step
#print axioms compare_step
#print axioms predicate_literal_step
#print axioms predicate_xor_step
#print axioms predicate_not_step
#print axioms branch_always_step
#print axioms predicate_not_uninitialized
#print axioms predicate_xor_uninitialized_left
#print axioms predicate_xor_uninitialized_right
end LarkPtxRotary
