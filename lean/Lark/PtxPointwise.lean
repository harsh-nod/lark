import Lark.Pointwise

/-!
Finite straight-line PTX execution for a source-bound FP16 pointwise profile.
Registers, parameter pointers, byte offsets, conversions and memory events are
executed explicitly. Pointer provenance and abstract scalar operations are
trusted interpretations, as in the existing bounded PTX reader. This is not
an IEEE or NVIDIA hardware-conformance theorem.

The finite instruction list is structurally recursive. No existing CUDA task,
launch, buffer, dtype, machine fuel or proof-resource limit is changed.
-/
namespace LarkPtxPointwise
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

structure Pointer where
  buffer : Nat
  offset : Int
  isGlobal : Bool
  deriving DecidableEq, Repr

inductive Register where
  | int32 : Nat → Register
  | int64 : Nat → Register
  | float32 : Nat → Register
  | bit16 : Nat → Register
  deriving DecidableEq, Repr

inductive Value (α : Type) where
  | integer : Int → Value α
  | address : Pointer → Value α
  | number : α → Value α

structure Registers (α : Type) where
  values : Register → Option (Value α) := fun _ => none
  base : State α
  stopped : Bool := false

namespace Registers
def i32 (s : Registers α) (r : Nat) : Option Int :=
  match s.values (.int32 r) with
  | some (.integer v) => some v
  | _ => none
def i64 (s : Registers α) (r : Nat) : Option Int :=
  match s.values (.int64 r) with
  | some (.integer v) => some v
  | _ => none
def pointer (s : Registers α) (r : Nat) : Option Pointer :=
  match s.values (.int64 r) with
  | some (.address v) => some v
  | _ => none
def scalar (s : Registers α) (r : Nat) : Option α :=
  match s.values (.float32 r) with
  | some (.number v) => some v
  | _ => none
def half (s : Registers α) (r : Nat) : Option α :=
  match s.values (.bit16 r) with
  | some (.number v) => some v
  | _ => none
end Registers

inductive Instruction where
  | parameter : Nat → Nat → Instruction
  | toGlobal : Nat → Nat → Instruction
  | blockId : Nat → Instruction
  | mulWideS32 : Nat → Nat → Int → Instruction
  | addPointerS64 : Nat → Nat → Nat → Instruction
  | loadHalf : Nat → Nat → Instruction
  | fromHalf : Nat → Nat → Instruction
  | literal : Nat → Int → Nat → Instruction
  | binary : Nat → Binary → Nat → Nat → Instruction
  | toHalf : Nat → Nat → Instruction
  | storeHalf : Nat → Nat → Instruction
  | ret : Instruction
  deriving DecidableEq, Repr

def signed32 (i : Int) : Prop := -2147483648 ≤ i ∧ i < 2147483648
def signed64 (i : Int) : Prop := -9223372036854775808 ≤ i ∧ i < 9223372036854775808
instance (i : Int) : Decidable (signed32 i) :=
  inferInstanceAs (Decidable (-2147483648 ≤ i ∧ i < 2147483648))
instance (i : Int) : Decidable (signed64 i) :=
  inferInstanceAs (Decidable (-9223372036854775808 ≤ i ∧ i < 9223372036854775808))

def halfAddress (n : Nat) (p : Pointer) : Option Location :=
  if p.isGlobal ∧ p.buffer < 2 ∧ 0 ≤ p.offset ∧ p.offset % 2 = 0 ∧
      (p.offset / 2).toNat < n then
    some ⟨.global, 0, p.buffer, (p.offset / 2).toNat⟩
  else none

def putValue (s : Registers α) (d : Register) (v : Value α) : Registers α :=
  { s with values := fun r => if r = d then some v else s.values r }

def putPointer (s : Registers α) (d : Nat) (p : Pointer) : Registers α :=
  putValue s (.int64 d) (.address p)

def putI32 (s : Registers α) (d : Nat) (v : Int) : Registers α :=
  putValue s (.int32 d) (.integer v)

def putI64 (s : Registers α) (d : Nat) (v : Int) : Registers α :=
  putValue s (.int64 d) (.integer v)

def putScalar (s : Registers α) (d : Nat) (v : α) : Registers α :=
  putValue s (.float32 d) (.number v)

def putHalf (s : Registers α) (d : Nat) (v : α) : Registers α :=
  putValue s (.bit16 d) (.number v)

def step (ops : Ops α) (n t : Nat) (ins : Instruction)
    (s : Registers α) : Option (Registers α) := do
  match ins with
  | .parameter d b =>
      if b < 2 then
        some (putPointer s d ⟨b, 0, false⟩)
      else none
  | .toGlobal d a =>
      let p ← s.pointer a
      some (putPointer s d { p with isGlobal := true })
  | .blockId d =>
      if t < 4294967296 then
        some (putI32 s d t)
      else none
  | .mulWideS32 d a c =>
      let v ← s.i32 a
      if signed32 v ∧ signed32 c ∧ signed64 (v * c) then
        some (putI64 s d (v * c))
      else none
  | .addPointerS64 d a b =>
      let p ← s.pointer a
      let v ← s.i64 b
      if signed64 (p.offset + v) then
        some (putPointer s d { p with offset := p.offset + v })
      else none
  | .loadHalf d a =>
      let p ← s.pointer a
      let l ← halfAddress n p
      let v ← s.base.memory l
      some { putHalf s d v with base := record s.base t l false }
  | .fromHalf d a =>
      let v ← s.half a
      some (putScalar s d (ops.fromHalf v))
  | .literal d a b =>
      if b ≠ 0 then
        some (putScalar s d (ops.literal a b))
      else none
  | .binary d op a b =>
      let x ← s.scalar a
      let y ← s.scalar b
      some (putScalar s d (applyBinary ops op x y))
  | .toHalf d a =>
      let v ← s.scalar a
      some (putHalf s d (ops.toHalf v))
  | .storeHalf a b =>
      let p ← s.pointer a
      let l ← halfAddress n p
      let v ← s.half b
      if p.buffer = 1 then
        some { s with base := { record s.base t l true with
                                memory := fun k => if k = l then some v else s.base.memory k } }
      else none
  | .ret => some { s with stopped := true }

theorem mulWide_step (ops : Ops α) (n t d a : Nat) (c v : Int) (s : Registers α)
    (hv : s.i32 a = some v) (h : signed32 v ∧ signed32 c ∧ signed64 (v * c)) :
    step ops n t (.mulWideS32 d a c) s = some (putI64 s d (v * c)) := by
  simp only [step, hv, bind, pure, Option.bind]
  exact if_pos h

theorem addPointer_step (ops : Ops α) (n t d a b : Nat) (p : Pointer) (v : Int)
    (s : Registers α) (hp : s.pointer a = some p) (hv : s.i64 b = some v)
    (h : signed64 (p.offset + v)) :
    step ops n t (.addPointerS64 d a b) s =
      some (putPointer s d { p with offset := p.offset + v }) := by
  simp only [step, hp, hv, bind, pure, Option.bind]
  exact if_pos h

theorem storeHalf_step (ops : Ops α) (n t a b : Nat) (p : Pointer) (l : Location)
    (v : α) (s : Registers α) (hp : s.pointer a = some p)
    (hl : halfAddress n p = some l) (hv : s.half b = some v) (hb : p.buffer = 1) :
    step ops n t (.storeHalf a b) s =
      some { s with base := { record s.base t l true with
                               memory := fun k => if k = l then some v else s.base.memory k } } := by
  simp only [step, hp, hl, hv, bind, pure, Option.bind]
  exact if_pos hb

def steps (ops : Ops α) (n t : Nat) : List Instruction → Registers α → Option (Registers α)
  | [], s => some s
  | i :: is, s => if s.stopped then none else (step ops n t i s).bind (steps ops n t is)

theorem steps_cons_of_step (ops : Ops α) (n t : Nat) (i : Instruction)
    (is : List Instruction) (s next : Registers α) (hs : s.stopped = false)
    (he : step ops n t i s = some next) :
    steps ops n t (i :: is) s = steps ops n t is next := by
  simp only [steps, hs, Bool.false_eq_true, ↓reduceIte, he, Option.some_bind]

def run (ops : Ops α) (n t : Nat) (p : List Instruction)
    (s : Registers α) : Option (Registers α) := do
  let final ← steps ops n t p s
  if final.stopped then some final else none

theorem steps_append (ops : Ops α) (n t : Nat) (p q : List Instruction) (s : Registers α) :
    steps ops n t (p ++ q) s =
      (steps ops n t p s).bind (steps ops n t q) := by
  induction p generalizing s with
  | nil => rfl
  | cons i is ih =>
      cases hs : s.stopped with
      | true => simp [steps, hs]
      | false =>
          cases he : step ops n t i s <;>
            simp [steps, hs, he, ih]

def parameters : List Instruction :=
  [.parameter 1 0, .parameter 2 1, .toGlobal 3 2, .toGlobal 4 1]
def addresses : List Instruction :=
  [.blockId 1, .mulWideS32 5 1 2, .addPointerS64 6 4 5]
def loads : List Instruction := [.loadHalf 1 6, .fromHalf 1 1]
def arithmetic : List Instruction := [.literal 3 0 1, .binary 2 .max 1 3, .toHalf 2 2]
def stores : List Instruction := [.addPointerS64 7 3 5, .storeHalf 7 2, .ret]
def program : List Instruction := parameters ++ (addresses ++ (loads ++ (arithmetic ++ stores)))

def body : LarkPointwise.Scalar := .bin .max .input (.lit 0 1)

def after (ops : Ops α) (t : Nat) (x : α) (s : State α) : State α :=
  { record (record s t (LarkPointwise.inputCell t) false) t (LarkPointwise.outputCell t) true
    with memory := fun l => if l = LarkPointwise.outputCell t
                           then some (LarkPointwise.result ops body x) else s.memory l }

def runLane (ops : Ops α) (n t : Nat) (p : List Instruction) (s : State α) : Option (State α) :=
  (run ops n t p { base := s }).map (·.base)

theorem runLane_of_steps (ops : Ops α) (n t : Nat) (p : List Instruction)
    (s : State α) (final : Registers α)
    (h : steps ops n t p { base := s } = some final) (hs : final.stopped = true) :
    runLane ops n t p s = some final.base := by
  simp only [runLane, run, h, bind, pure, Option.bind, hs, ↓reduceIte, Option.map]

theorem halfAddress_at (n t b : Nat) (ht : t < n) (hb : b < 2) :
    halfAddress n ⟨b, (t : Int) * 2, true⟩ = some ⟨.global, 0, b, t⟩ := by
  have hnonneg : 0 ≤ (t : Int) * 2 := by omega
  simp [halfAddress, hb, ht, hnonneg]

def parameterState (s : State α) : Registers α :=
  putPointer (putPointer (putPointer (putPointer { base := s }
    1 ⟨0, 0, false⟩) 2 ⟨1, 0, false⟩) 3 ⟨1, 0, true⟩) 4 ⟨0, 0, true⟩

def addressState (t : Nat) (s : State α) : Registers α :=
  putPointer (putI64 (putI32 (parameterState s) 1 t) 5 ((t : Int) * 2))
    6 ⟨0, (t : Int) * 2, true⟩

def loadState (ops : Ops α) (t : Nat) (x : α) (s : State α) : Registers α :=
  putScalar { putHalf (addressState t s) 1 x
              with base := record s t (LarkPointwise.inputCell t) false }
    1 (ops.fromHalf x)

def arithmeticState (ops : Ops α) (t : Nat) (x : α) (s : State α) : Registers α :=
  putHalf (putScalar (putScalar (loadState ops t x s) 3 (ops.literal 0 1))
    2 (ops.max (ops.fromHalf x) (ops.literal 0 1)))
    2 (LarkPointwise.result ops body x)

def storeAddressState (ops : Ops α) (t : Nat) (x : α) (s : State α) : Registers α :=
  putPointer (arithmeticState ops t x s) 7 ⟨1, (t : Int) * 2, true⟩

def storeMemoryState (ops : Ops α) (t : Nat) (x : α) (s : State α) : Registers α :=
  { storeAddressState ops t x s with base := after ops t x s }

def storeState (ops : Ops α) (t : Nat) (x : α) (s : State α) : Registers α :=
  { storeMemoryState ops t x s with stopped := true }

theorem putPointer_base (s : Registers α) (d : Nat) (p : Pointer) :
    (putPointer s d p).base = s.base := rfl

theorem putPointer_stopped (s : Registers α) (d : Nat) (p : Pointer) :
    (putPointer s d p).stopped = s.stopped := rfl

theorem arithmeticState_pointer (ops : Ops α) (t : Nat) (x : α) (s : State α) (r : Nat) :
    (arithmeticState ops t x s).pointer r = (loadState ops t x s).pointer r := rfl

theorem loadState_pointer (ops : Ops α) (t : Nat) (x : α) (s : State α) (r : Nat) :
    (loadState ops t x s).pointer r = (addressState t s).pointer r := rfl

theorem addressState_pointer3 (t : Nat) (s : State α) :
    (addressState t s).pointer 3 = some ⟨1, 0, true⟩ := rfl

theorem arithmeticState_i64 (ops : Ops α) (t : Nat) (x : α) (s : State α) (r : Nat) :
    (arithmeticState ops t x s).i64 r = (loadState ops t x s).i64 r := rfl

theorem loadState_i64 (ops : Ops α) (t : Nat) (x : α) (s : State α) (r : Nat) :
    (loadState ops t x s).i64 r = (addressState t s).i64 r := rfl

theorem addressState_i645 (t : Nat) (s : State α) :
    (addressState t s).i64 5 = some ((t : Int) * 2) := rfl

theorem arithmeticState_base (ops : Ops α) (t : Nat) (x : α) (s : State α) :
    (arithmeticState ops t x s).base = (loadState ops t x s).base := rfl

theorem loadState_base (ops : Ops α) (t : Nat) (x : α) (s : State α) :
    (loadState ops t x s).base = record s t (LarkPointwise.inputCell t) false := rfl

theorem arithmeticState_stopped (ops : Ops α) (t : Nat) (x : α) (s : State α) :
    (arithmeticState ops t x s).stopped = false := by
  change (loadState ops t x s).stopped = false
  change (addressState t s).stopped = false
  change (parameterState s).stopped = false
  rfl

theorem storeAddress_stopped (ops : Ops α) (t : Nat) (x : α) (s : State α) :
    (storeAddressState ops t x s).stopped = false := by
  change (putPointer (arithmeticState ops t x s) 7 ⟨1, (t : Int) * 2, true⟩).stopped = false
  rw [putPointer_stopped, arithmeticState_stopped]

theorem storeMemory_stopped (ops : Ops α) (t : Nat) (x : α) (s : State α) :
    (storeMemoryState ops t x s).stopped = false := by
  change (storeAddressState ops t x s).stopped = false
  exact storeAddress_stopped ops t x s

theorem parameters_eq (ops : Ops α) (n t : Nat) (s : State α) :
    steps ops n t parameters { base := s } = some (parameterState s) := by
  simp [steps, parameters, step, parameterState, putPointer, putValue,
    Registers.pointer, bind, pure, Option.bind]

theorem addresses_eq (ops : Ops α) (n t : Nat) (s : State α) (hb : t < 2147483648) :
    steps ops n t addresses (parameterState s) = some (addressState t s) := by
  have h32 : t < 4294967296 := by omega
  have hindex : signed32 (t : Int) := by dsimp [signed32]; omega
  have hwide : signed64 ((t : Int) * 2) := by dsimp [signed64]; omega
  let a := putI32 (parameterState s) 1 t
  let b := putI64 a 5 ((t : Int) * 2)
  have h1 : step ops n t (.blockId 1) (parameterState s) = some a := by
    simp only [step, h32, ↓reduceIte]
    rfl
  have h2 : step ops n t (.mulWideS32 5 1 2) a = some b := by
    have ha : a.i32 1 = some (t : Int) := rfl
    have htwo : signed32 2 := by dsimp [signed32]; omega
    exact mulWide_step ops n t 5 1 2 t a ha ⟨hindex, htwo, hwide⟩
  have h3 : step ops n t (.addPointerS64 6 4 5) b = some (addressState t s) := by
    have hp : b.pointer 4 = some ⟨0, 0, true⟩ := rfl
    have hi : b.i64 5 = some ((t : Int) * 2) := rfl
    have h : signed64 (0 + (t : Int) * 2) := by simpa only [Int.zero_add] using hwide
    change step ops n t (.addPointerS64 6 4 5) b =
      some (putPointer b 6 ⟨0, (t : Int) * 2, true⟩)
    simpa only [Int.zero_add] using addPointer_step ops n t 6 4 5
      ⟨0, 0, true⟩ ((t : Int) * 2) b hp hi h
  have hs0 : (parameterState s).stopped = false := rfl
  have hs1 : a.stopped = false := rfl
  have hs2 : b.stopped = false := rfl
  simp [steps, addresses, hs0, h1, hs1, h2, hs2, h3, bind, pure, Option.bind]

theorem loads_eq (ops : Ops α) (n t : Nat) (s : State α) (x : α) (ht : t < n)
    (hx : s.memory (LarkPointwise.inputCell t) = some x) :
    steps ops n t loads (addressState t s) = some (loadState ops t x s) := by
  let a : Registers α :=
    { putHalf (addressState t s) 1 x with base := record s t (LarkPointwise.inputCell t) false }
  have h1 : step ops n t (.loadHalf 1 6) (addressState t s) = some a := by
    have hp : (addressState t s).pointer 6 = some ⟨0, (t : Int) * 2, true⟩ := rfl
    have hbase : (addressState t s).base = s := rfl
    have hx' : s.memory ⟨.global, 0, 0, t⟩ = some x := hx
    simp only [step, hp, hbase, Option.some_bind, halfAddress_at n t 0 ht (by decide), hx',
      bind, pure, Option.bind]
    rfl
  have h2 : step ops n t (.fromHalf 1 1) a = some (loadState ops t x s) := by
    have hh : a.half 1 = some x := rfl
    simp only [step, hh, Option.some_bind, bind, pure, Option.bind]
    rfl
  have hs0 : (addressState t s).stopped = false := rfl
  have hs1 : a.stopped = false := rfl
  simp [steps, loads, hs0, h1, hs1, h2, bind, pure, Option.bind]

theorem arithmetic_eq (ops : Ops α) (n t : Nat) (s : State α) (x : α) :
    steps ops n t arithmetic (loadState ops t x s) = some (arithmeticState ops t x s) := by
  let a := putScalar (loadState ops t x s) 3 (ops.literal 0 1)
  let b := putScalar a 2 (ops.max (ops.fromHalf x) (ops.literal 0 1))
  have h1 : step ops n t (.literal 3 0 1) (loadState ops t x s) = some a := by
    simp only [step, Nat.one_ne_zero, ↓reduceIte]
    rfl
  have h2 : step ops n t (.binary 2 .max 1 3) a = some b := by
    have hleft : a.scalar 1 = some (ops.fromHalf x) := rfl
    have hright : a.scalar 3 = some (ops.literal 0 1) := rfl
    simp only [step, hleft, hright, Option.some_bind, applyBinary, bind, pure, Option.bind]
    rfl
  have h3 : step ops n t (.toHalf 2 2) b = some (arithmeticState ops t x s) := by
    have hv : b.scalar 2 = some (ops.max (ops.fromHalf x) (ops.literal 0 1)) := rfl
    simp only [step, hv, Option.some_bind, bind, pure, Option.bind]
    rfl
  have hs0 : (loadState ops t x s).stopped = false := rfl
  have hs1 : a.stopped = false := rfl
  have hs2 : b.stopped = false := rfl
  simp [steps, arithmetic, hs0, h1, hs1, h2, hs2, h3, bind, pure, Option.bind]

theorem store_address_eq (ops : Ops α) (n t : Nat) (s : State α) (x : α)
    (hb : t < 2147483648) :
    step ops n t (.addPointerS64 7 3 5) (arithmeticState ops t x s) =
      some (storeAddressState ops t x s) := by
  have hwide : signed64 ((t : Int) * 2) := by dsimp [signed64]; omega
  have hp : (arithmeticState ops t x s).pointer 3 = some ⟨1, 0, true⟩ := by
    rw [arithmeticState_pointer, loadState_pointer, addressState_pointer3]
  have hi : (arithmeticState ops t x s).i64 5 = some ((t : Int) * 2) := by
    rw [arithmeticState_i64, loadState_i64, addressState_i645]
  have h : signed64 (0 + (t : Int) * 2) := by simpa only [Int.zero_add] using hwide
  change step ops n t (.addPointerS64 7 3 5) (arithmeticState ops t x s) =
    some (putPointer (arithmeticState ops t x s) 7 ⟨1, (t : Int) * 2, true⟩)
  simpa only [Int.zero_add] using addPointer_step ops n t 7 3 5
    ⟨1, 0, true⟩ ((t : Int) * 2) (arithmeticState ops t x s) hp hi h

theorem store_memory_eq (ops : Ops α) (n t : Nat) (s : State α) (x : α) (ht : t < n) :
    step ops n t (.storeHalf 7 2) (storeAddressState ops t x s) =
      some (storeMemoryState ops t x s) := by
  have hp : (storeAddressState ops t x s).pointer 7 = some ⟨1, (t : Int) * 2, true⟩ := rfl
  have hv : (storeAddressState ops t x s).half 2 =
      some (LarkPointwise.result ops body x) := rfl
  have hbase : (storeAddressState ops t x s).base =
      record s t (LarkPointwise.inputCell t) false := by
    change (putPointer (arithmeticState ops t x s) 7 ⟨1, (t : Int) * 2, true⟩).base = _
    rw [putPointer_base, arithmeticState_base, loadState_base]
  have hl : halfAddress n ⟨1, (t : Int) * 2, true⟩ =
      some (LarkPointwise.outputCell t) := halfAddress_at n t 1 ht (by decide)
  have h := storeHalf_step ops n t 7 2 ⟨1, (t : Int) * 2, true⟩
    (LarkPointwise.outputCell t) (LarkPointwise.result ops body x)
    (storeAddressState ops t x s) hp hl hv rfl
  simpa only [storeMemoryState, hbase, after, record] using h

theorem store_ret_eq (ops : Ops α) (n t : Nat) (s : State α) (x : α) :
    step ops n t .ret (storeMemoryState ops t x s) = some (storeState ops t x s) := rfl

theorem stores_eq (ops : Ops α) (n t : Nat) (s : State α) (x : α)
    (ht : t < n) (hb : t < 2147483648) :
    steps ops n t stores (arithmeticState ops t x s) = some (storeState ops t x s) := by
  change steps ops n t [.addPointerS64 7 3 5, .storeHalf 7 2, .ret]
    (arithmeticState ops t x s) = some (storeState ops t x s)
  rw [steps_cons_of_step ops n t _ _ _ _ (arithmeticState_stopped ops t x s)
    (store_address_eq ops n t s x hb)]
  rw [steps_cons_of_step ops n t _ _ _ _ (storeAddress_stopped ops t x s)
    (store_memory_eq ops n t s x ht)]
  rw [steps_cons_of_step ops n t _ _ _ _ (storeMemory_stopped ops t x s)
    (store_ret_eq ops n t s x)]
  rfl

theorem lane_eq (ops : Ops α) (n t : Nat) (s : State α) (x : α)
    (ht : t < n) (hb : t < 2147483648)
    (hx : s.memory (LarkPointwise.inputCell t) = some x) :
    runLane ops n t program s = some (after ops t x s) := by
  have h : steps ops n t program { base := s } = some (storeState ops t x s) := by
    change steps ops n t (parameters ++ (addresses ++ (loads ++ (arithmetic ++ stores))))
      { base := s } = some (storeState ops t x s)
    rw [steps_append, parameters_eq, Option.some_bind]
    rw [steps_append, addresses_eq ops n t s hb, Option.some_bind]
    rw [steps_append, loads_eq ops n t s x ht hx, Option.some_bind]
    rw [steps_append, arithmetic_eq, Option.some_bind]
    exact stores_eq ops n t s x ht hb
  exact runLane_of_steps ops n t program s (storeState ops t x s) h rfl

#print axioms LarkPtxPointwise.mulWide_step
#print axioms LarkPtxPointwise.addPointer_step
#print axioms LarkPtxPointwise.storeHalf_step
#print axioms LarkPtxPointwise.steps_append
#print axioms LarkPtxPointwise.halfAddress_at
#print axioms LarkPtxPointwise.parameters_eq
#print axioms LarkPtxPointwise.addresses_eq
#print axioms LarkPtxPointwise.loads_eq
#print axioms LarkPtxPointwise.arithmetic_eq
#print axioms LarkPtxPointwise.store_address_eq
#print axioms LarkPtxPointwise.store_memory_eq
#print axioms LarkPtxPointwise.store_ret_eq
#print axioms LarkPtxPointwise.stores_eq
#print axioms LarkPtxPointwise.lane_eq

end LarkPtxPointwise
