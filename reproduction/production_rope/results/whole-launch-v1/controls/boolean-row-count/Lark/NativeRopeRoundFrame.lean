import Lark.NativeRopeRound

/-! Full native-round values, exact six-access traces and memory frames. -/
namespace LarkNativeRope
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem address_pair_distinct (buffer row pair : Nat) (neox : Bool) :
    address buffer row pair neox false ≠ address buffer row pair neox true := by
  intro he
  have hc : pairColumn neox pair false = pairColumn neox pair true := Nat.add_left_cancel he
  exact pair_columns_distinct neox pair hc

theorem address_different_pairs (buffer row pair other : Nat) (neox imaginary otherImaginary : Bool)
    (hne : pair ≠ other) : address buffer row pair neox imaginary ≠ address buffer row other neox otherImaginary := by
  intro he
  have hc : pairColumn neox pair imaginary = pairColumn neox other otherImaginary := Nat.add_left_cancel he
  have hi := congrArg (pairOfColumn neox) hc
  simp only [pair_inverse] at hi
  exact hne hi

theorem query_round_values (ops : Ops α) (input : Nat → Nat → α) (neox : Bool)
    (row pair t : Nat) (s : State α) :
    (queryRound ops input neox row pair t s).memory (globalCell 0 (address 0 row pair neox false)) =
      some (rotated ops input 0 row pair neox false) ∧
    (queryRound ops input neox row pair t s).memory (globalCell 0 (address 0 row pair neox true)) =
      some (rotated ops input 0 row pair neox true) := by
  exact query_pair_values ops t (address 0 row pair neox false) (address 0 row pair neox true)
    (input 0 (address 0 row pair neox false)) (input 0 (address 0 row pair neox true))
    (ops.fromHalf (input 2 (cacheCos row pair))) (ops.fromHalf (input 2 (cacheSin row pair)))
    (queryHeaderAfter ops input neox row pair t s) (address_pair_distinct 0 row pair neox)

theorem query_round_memory_frame (ops : Ops α) (input : Nat → Nat → α) (neox : Bool)
    (row pair t : Nat) (s : State α) (l : Location)
    (ha : l ≠ globalCell 0 (address 0 row pair neox false))
    (hb : l ≠ globalCell 0 (address 0 row pair neox true)) :
    (queryRound ops input neox row pair t s).memory l = s.memory l := by
  exact query_pair_memory_frame ops t (address 0 row pair neox false) (address 0 row pair neox true)
    (input 0 (address 0 row pair neox false)) (input 0 (address 0 row pair neox true))
    (ops.fromHalf (input 2 (cacheCos row pair))) (ops.fromHalf (input 2 (cacheSin row pair)))
    (queryHeaderAfter ops input neox row pair t s) l ha hb

theorem query_round_ready (ops : Ops α) (input : Nat → Nat → α) (neox : Bool)
    (row pair t : Nat) (s : State α) (h0 : s.indices t 0 = some (row : Int)) :
    (queryRound ops input neox row pair t s).pc t = 2 ∧
    (queryRound ops input neox row pair t s).indices t 0 = some (row : Int) ∧
    (queryRound ops input neox row pair t s).indices t 1 = some ((pair + 512 : Nat) : Int) := by
  simp [queryRound, queryBody, queryPairAfter, queryHeaderAfter, setIndex, LarkReduction.setIndex, setReg, written, record, advance, h0]

theorem query_round_other_pc (ops : Ops α) (input : Nat → Nat → α) (neox : Bool)
    (row pair t u : Nat) (s : State α) (hne : u ≠ t) :
    (queryRound ops input neox row pair t s).pc u = s.pc u := by
  simp [queryRound, queryBody, queryPairAfter, queryHeaderAfter, setIndex, LarkReduction.setIndex, setReg, written, record, advance, hne]

theorem query_round_epochs (ops : Ops α) (input : Nat → Nat → α) (neox : Bool)
    (row pair t : Nat) (s : State α) : (queryRound ops input neox row pair t s).epochs = s.epochs := rfl

theorem query_round_trace (ops : Ops α) (input : Nat → Nat → α) (neox : Bool)
    (row pair t : Nat) (s : State α) :
    (queryRound ops input neox row pair t s).trace =
      ⟨t, globalCell 0 (address 0 row pair neox true), true, s.epochs t⟩ ::
      ⟨t, globalCell 0 (address 0 row pair neox false), true, s.epochs t⟩ ::
      ⟨t, globalCell 0 (address 0 row pair neox true), false, s.epochs t⟩ ::
      ⟨t, globalCell 0 (address 0 row pair neox false), false, s.epochs t⟩ ::
      ⟨t, globalCell 2 (cacheSin row pair), false, s.epochs t⟩ ::
      ⟨t, globalCell 2 (cacheCos row pair), false, s.epochs t⟩ :: s.trace := rfl

theorem query_round_trace_length (ops : Ops α) (input : Nat → Nat → α) (neox : Bool)
    (row pair t : Nat) (s : State α) : (queryRound ops input neox row pair t s).trace.length = s.trace.length + 6 := by
  simp [query_round_trace, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem query_round_good (neox : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row pair t : Nat) (s : State α)
    (ha : writer 0 (address 0 row pair neox false) neox = t)
    (hb : writer 0 (address 0 row pair neox true) neox = t)
    (old : ∀ a ∈ s.trace, Good neox a) :
    ∀ a ∈ (queryRound ops input neox row pair t s).trace, Good neox a := by
  exact query_pair_good neox ops t (address 0 row pair neox false) (address 0 row pair neox true)
    (input 0 (address 0 row pair neox false)) (input 0 (address 0 row pair neox true))
    (ops.fromHalf (input 2 (cacheCos row pair))) (ops.fromHalf (input 2 (cacheSin row pair)))
    (queryHeaderAfter ops input neox row pair t s) ha hb (query_header_good neox ops input row pair t s old)

#print axioms query_round_values
#print axioms query_round_memory_frame
#print axioms query_round_ready
#print axioms query_round_other_pc
#print axioms query_round_epochs
#print axioms query_round_trace
#print axioms query_round_trace_length
#print axioms query_round_good

theorem key_round_values (ops : Ops α) (input : Nat → Nat → α) (neox : Bool)
    (row pair t : Nat) (s : State α) :
    (keyRound ops input neox row pair t s).memory (globalCell 1 (address 1 row pair neox false)) =
      some (rotated ops input 1 row pair neox false) ∧
    (keyRound ops input neox row pair t s).memory (globalCell 1 (address 1 row pair neox true)) =
      some (rotated ops input 1 row pair neox true) := by
  exact key_pair_values ops t (address 1 row pair neox false) (address 1 row pair neox true)
    (input 1 (address 1 row pair neox false)) (input 1 (address 1 row pair neox true))
    (ops.fromHalf (input 2 (cacheCos row pair))) (ops.fromHalf (input 2 (cacheSin row pair)))
    (keyHeaderAfter ops input neox row pair t s) (address_pair_distinct 1 row pair neox)

theorem key_round_memory_frame (ops : Ops α) (input : Nat → Nat → α) (neox : Bool)
    (row pair t : Nat) (s : State α) (l : Location)
    (ha : l ≠ globalCell 1 (address 1 row pair neox false))
    (hb : l ≠ globalCell 1 (address 1 row pair neox true)) :
    (keyRound ops input neox row pair t s).memory l = s.memory l := by
  exact key_pair_memory_frame ops t (address 1 row pair neox false) (address 1 row pair neox true)
    (input 1 (address 1 row pair neox false)) (input 1 (address 1 row pair neox true))
    (ops.fromHalf (input 2 (cacheCos row pair))) (ops.fromHalf (input 2 (cacheSin row pair)))
    (keyHeaderAfter ops input neox row pair t s) l ha hb

theorem key_round_ready (ops : Ops α) (input : Nat → Nat → α) (neox : Bool)
    (row pair t : Nat) (s : State α) (h0 : s.indices t 0 = some (row : Int)) :
    (keyRound ops input neox row pair t s).pc t = 26 ∧
    (keyRound ops input neox row pair t s).indices t 0 = some (row : Int) ∧
    (keyRound ops input neox row pair t s).indices t 10 = some ((pair + 512 : Nat) : Int) := by
  simp [keyRound, keyBody, keyPairAfter, keyHeaderAfter, setIndex, LarkReduction.setIndex, setReg, written, record, advance, h0]

theorem key_round_other_pc (ops : Ops α) (input : Nat → Nat → α) (neox : Bool)
    (row pair t u : Nat) (s : State α) (hne : u ≠ t) :
    (keyRound ops input neox row pair t s).pc u = s.pc u := by
  simp [keyRound, keyBody, keyPairAfter, keyHeaderAfter, setIndex, LarkReduction.setIndex, setReg, written, record, advance, hne]

theorem key_round_epochs (ops : Ops α) (input : Nat → Nat → α) (neox : Bool)
    (row pair t : Nat) (s : State α) : (keyRound ops input neox row pair t s).epochs = s.epochs := rfl

theorem key_round_trace (ops : Ops α) (input : Nat → Nat → α) (neox : Bool)
    (row pair t : Nat) (s : State α) :
    (keyRound ops input neox row pair t s).trace =
      ⟨t, globalCell 1 (address 1 row pair neox true), true, s.epochs t⟩ ::
      ⟨t, globalCell 1 (address 1 row pair neox false), true, s.epochs t⟩ ::
      ⟨t, globalCell 1 (address 1 row pair neox true), false, s.epochs t⟩ ::
      ⟨t, globalCell 1 (address 1 row pair neox false), false, s.epochs t⟩ ::
      ⟨t, globalCell 2 (cacheSin row pair), false, s.epochs t⟩ ::
      ⟨t, globalCell 2 (cacheCos row pair), false, s.epochs t⟩ :: s.trace := rfl

theorem key_round_trace_length (ops : Ops α) (input : Nat → Nat → α) (neox : Bool)
    (row pair t : Nat) (s : State α) : (keyRound ops input neox row pair t s).trace.length = s.trace.length + 6 := by
  simp [key_round_trace, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem key_round_good (neox : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row pair t : Nat) (s : State α)
    (ha : writer 1 (address 1 row pair neox false) neox = t)
    (hb : writer 1 (address 1 row pair neox true) neox = t)
    (old : ∀ a ∈ s.trace, Good neox a) :
    ∀ a ∈ (keyRound ops input neox row pair t s).trace, Good neox a := by
  exact key_pair_good neox ops t (address 1 row pair neox false) (address 1 row pair neox true)
    (input 1 (address 1 row pair neox false)) (input 1 (address 1 row pair neox true))
    (ops.fromHalf (input 2 (cacheCos row pair))) (ops.fromHalf (input 2 (cacheSin row pair)))
    (keyHeaderAfter ops input neox row pair t s) ha hb (key_header_good neox ops input row pair t s old)

#print axioms key_round_values
#print axioms key_round_memory_frame
#print axioms key_round_ready
#print axioms key_round_other_pc
#print axioms key_round_epochs
#print axioms key_round_trace
#print axioms key_round_trace_length
#print axioms key_round_good

#print axioms address_pair_distinct
#print axioms address_different_pairs
end LarkNativeRope
