import Lark.Nonlinear

/-! Opt-in initialization for explicitly declared initialized, mutable buffers.
Execution, bounds, writes, synchronization and extraction use the pinned
LarkNonlinear machine unchanged. This does not permit argument-buffer aliases.
-/
namespace LarkInOut
open LarkNonlinear

def seededOutside (layout : Layout) (buffers : List Nat)
    (input : Nat → Nat → α) (outside : Location → Option α)
    (l : Location) : Option α :=
  if l.space = .global ∧ l.owner = 0 ∧ l.buffer ∈ buffers then
    match layout.global[l.buffer]? with
    | some b => if l.offset < b.size then some (input l.buffer l.offset) else outside l
    | none => outside l
  else outside l

def initial (layout : Layout) (buffers : List Nat) (input : Nat → Nat → α)
    (outside : Location → Option α) : State α :=
  LarkNonlinear.initial layout input (seededOutside layout buffers input outside)

def Valid (layout : Layout) (buffers : List Nat) : Prop :=
  buffers.Nodup ∧ ∀ id ∈ buffers, ∃ b, layout.global[id]? = some b ∧ b.role = .output

theorem initial_mutable (layout : Layout) (buffers : List Nat)
    (input : Nat → Nat → α) (outside : Location → Option α) (id offset : Nat) (b : Buffer)
    (hm : id ∈ buffers) (hb : layout.global[id]? = some b) (ho : b.role = .output)
    (hi : offset < b.size) :
    (initial layout buffers input outside).memory ⟨.global, 0, id, offset⟩ =
      some (input id offset) := by
  simp [initial, LarkNonlinear.initial, seededOutside, hb, ho, hi, hm]

theorem initial_readonly (layout : Layout) (buffers : List Nat)
    (input : Nat → Nat → α) (outside : Location → Option α) (id offset : Nat) (b : Buffer)
    (hb : layout.global[id]? = some b) (hr : b.role = .input) (hi : offset < b.size) :
    (initial layout buffers input outside).memory ⟨.global, 0, id, offset⟩ =
      some (input id offset) :=
  initial_places layout input (seededOutside layout buffers input outside) id offset b hb hr hi

theorem initial_controls (layout : Layout) (buffers : List Nat)
    (input : Nat → Nat → α) (outside : Location → Option α) :
    (initial layout buffers input outside).pc = (fun _ => 0) ∧
    (initial layout buffers input outside).trace = [] ∧
    (initial layout buffers input outside).epochs = (fun _ => {}) := ⟨rfl, rfl, rfl⟩

def StdPre (layout : Layout) (buffers : List Nat) (input : Nat → Nat → α)
    (s : State α) : Prop := ∃ outside, s = initial layout buffers input outside

theorem pre_satisfiable (layout : Layout) (buffers : List Nat) (input : Nat → Nat → α) :
    ∃ s, StdPre layout buffers input s := ⟨_, (fun _ => none), rfl⟩

#print axioms initial_mutable
#print axioms initial_readonly
#print axioms initial_controls
#print axioms pre_satisfiable
end LarkInOut
