import Lark.NativeRopeHeader

/-! Source-header entry facts for the pair cycles, read-only memory frames,
and classification of the two actual gathered-cache accesses. -/
namespace LarkNativeRope
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem query_header_ready (ops : Ops α) (input : Nat → Nat → α) (neox : Bool)
    (row pair t : Nat) (s : State α) (h0 : s.indices t 0 = some (row : Int))
    (h1 : s.indices t 1 = some (pair : Int)) :
    (queryHeaderAfter ops input neox row pair t s).pc t = 13 ∧
    (queryHeaderAfter ops input neox row pair t s).indices t 0 = some (row : Int) ∧
    (queryHeaderAfter ops input neox row pair t s).indices t 1 = some (pair : Int) ∧
    (queryHeaderAfter ops input neox row pair t s).indices t 8 = some ((address 0 row pair neox false : Nat) : Int) ∧
    (queryHeaderAfter ops input neox row pair t s).indices t 9 = some ((address 0 row pair neox true : Nat) : Int) ∧
    (queryHeaderAfter ops input neox row pair t s).regs t 0 = some (ops.fromHalf (input 2 (cacheCos row pair))) ∧
    (queryHeaderAfter ops input neox row pair t s).regs t 1 = some (ops.fromHalf (input 2 (cacheSin row pair))) := by
  simp [queryHeaderAfter, setIndex, LarkReduction.setIndex, setReg, record, advance, h0, h1]

theorem key_header_ready (ops : Ops α) (input : Nat → Nat → α) (neox : Bool)
    (row pair t : Nat) (s : State α) (h0 : s.indices t 0 = some (row : Int))
    (h1 : s.indices t 10 = some (pair : Int)) :
    (keyHeaderAfter ops input neox row pair t s).pc t = 37 ∧
    (keyHeaderAfter ops input neox row pair t s).indices t 0 = some (row : Int) ∧
    (keyHeaderAfter ops input neox row pair t s).indices t 10 = some (pair : Int) ∧
    (keyHeaderAfter ops input neox row pair t s).indices t 17 = some ((address 1 row pair neox false : Nat) : Int) ∧
    (keyHeaderAfter ops input neox row pair t s).indices t 18 = some ((address 1 row pair neox true : Nat) : Int) ∧
    (keyHeaderAfter ops input neox row pair t s).regs t 10 = some (ops.fromHalf (input 2 (cacheCos row pair))) ∧
    (keyHeaderAfter ops input neox row pair t s).regs t 11 = some (ops.fromHalf (input 2 (cacheSin row pair))) := by
  simp [keyHeaderAfter, setIndex, LarkReduction.setIndex, setReg, record, advance, h0, h1]

theorem query_header_memory (ops : Ops α) (input : Nat → Nat → α) (neox : Bool)
    (row pair t : Nat) (s : State α) : (queryHeaderAfter ops input neox row pair t s).memory = s.memory := rfl

theorem key_header_memory (ops : Ops α) (input : Nat → Nat → α) (neox : Bool)
    (row pair t : Nat) (s : State α) : (keyHeaderAfter ops input neox row pair t s).memory = s.memory := rfl

theorem query_header_trace (ops : Ops α) (input : Nat → Nat → α) (neox : Bool)
    (row pair t : Nat) (s : State α) :
    (queryHeaderAfter ops input neox row pair t s).trace =
      ⟨t, globalCell 2 (cacheSin row pair), false, s.epochs t⟩ ::
      ⟨t, globalCell 2 (cacheCos row pair), false, s.epochs t⟩ :: s.trace := rfl

theorem key_header_trace (ops : Ops α) (input : Nat → Nat → α) (neox : Bool)
    (row pair t : Nat) (s : State α) :
    (keyHeaderAfter ops input neox row pair t s).trace =
      ⟨t, globalCell 2 (cacheSin row pair), false, s.epochs t⟩ ::
      ⟨t, globalCell 2 (cacheCos row pair), false, s.epochs t⟩ :: s.trace := rfl

theorem query_header_epochs (ops : Ops α) (input : Nat → Nat → α) (neox : Bool)
    (row pair t : Nat) (s : State α) : (queryHeaderAfter ops input neox row pair t s).epochs = s.epochs := rfl

theorem key_header_epochs (ops : Ops α) (input : Nat → Nat → α) (neox : Bool)
    (row pair t : Nat) (s : State α) : (keyHeaderAfter ops input neox row pair t s).epochs = s.epochs := rfl

theorem query_header_other (ops : Ops α) (input : Nat → Nat → α) (neox : Bool)
    (row pair t u : Nat) (s : State α) (hne : u ≠ t) :
    (queryHeaderAfter ops input neox row pair t s).pc u = s.pc u ∧
    (queryHeaderAfter ops input neox row pair t s).indices u = s.indices u ∧
    (queryHeaderAfter ops input neox row pair t s).regs u = s.regs u := by
  simp [queryHeaderAfter, setIndex, LarkReduction.setIndex, setReg, record, advance, hne]

theorem key_header_other (ops : Ops α) (input : Nat → Nat → α) (neox : Bool)
    (row pair t u : Nat) (s : State α) (hne : u ≠ t) :
    (keyHeaderAfter ops input neox row pair t s).pc u = s.pc u ∧
    (keyHeaderAfter ops input neox row pair t s).indices u = s.indices u ∧
    (keyHeaderAfter ops input neox row pair t s).regs u = s.regs u := by
  simp [keyHeaderAfter, setIndex, LarkReduction.setIndex, setReg, record, advance, hne]

theorem query_header_good (neox : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row pair t : Nat) (s : State α) (old : ∀ a ∈ s.trace, Good neox a) :
    ∀ a ∈ (queryHeaderAfter ops input neox row pair t s).trace, Good neox a := by
  intro a hm
  rw [query_header_trace] at hm
  rcases List.mem_cons.mp hm with rfl | hm
  · exact cache_access_good neox t _ _
  rcases List.mem_cons.mp hm with rfl | hm
  · exact cache_access_good neox t _ _
  · exact old a hm

theorem key_header_good (neox : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row pair t : Nat) (s : State α) (old : ∀ a ∈ s.trace, Good neox a) :
    ∀ a ∈ (keyHeaderAfter ops input neox row pair t s).trace, Good neox a := by
  intro a hm
  rw [key_header_trace] at hm
  rcases List.mem_cons.mp hm with rfl | hm
  · exact cache_access_good neox t _ _
  rcases List.mem_cons.mp hm with rfl | hm
  · exact cache_access_good neox t _ _
  · exact old a hm

#print axioms query_header_ready
#print axioms key_header_ready
#print axioms query_header_memory
#print axioms key_header_memory
#print axioms query_header_trace
#print axioms key_header_trace
#print axioms query_header_epochs
#print axioms key_header_epochs
#print axioms query_header_other
#print axioms key_header_other
#print axioms query_header_good
#print axioms key_header_good
end LarkNativeRope
