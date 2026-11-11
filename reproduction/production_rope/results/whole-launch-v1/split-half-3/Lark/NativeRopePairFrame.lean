import Lark.NativeRopePair

/-! Exact pair values, memory frames and the actual four-access extension.
These lemmas are used to retain pending pairs during native lane/grid folds. -/
namespace LarkNativeRope
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem query_pair_trace (ops : Ops α) (t a b : Nat) (x y c sn : α) (s : State α) :
    (queryPairAfter ops t a b x y c sn s).trace =
      ⟨t, globalCell 0 b, true, s.epochs t⟩ ::
      ⟨t, globalCell 0 a, true, s.epochs t⟩ ::
      ⟨t, globalCell 0 b, false, s.epochs t⟩ ::
      ⟨t, globalCell 0 a, false, s.epochs t⟩ :: s.trace := rfl

theorem key_pair_trace (ops : Ops α) (t a b : Nat) (x y c sn : α) (s : State α) :
    (keyPairAfter ops t a b x y c sn s).trace =
      ⟨t, globalCell 1 b, true, s.epochs t⟩ ::
      ⟨t, globalCell 1 a, true, s.epochs t⟩ ::
      ⟨t, globalCell 1 b, false, s.epochs t⟩ ::
      ⟨t, globalCell 1 a, false, s.epochs t⟩ :: s.trace := rfl

theorem query_pair_values (ops : Ops α) (t a b : Nat) (x y c sn : α) (s : State α) (hne : a ≠ b) :
    (queryPairAfter ops t a b x y c sn s).memory (globalCell 0 a) = some (ops.toHalf (pairReal ops x y c sn)) ∧
    (queryPairAfter ops t a b x y c sn s).memory (globalCell 0 b) = some (ops.toHalf (pairImaginary ops x y c sn)) := by
  simp [queryPairAfter, written, setReg, record, advance, globalCell, hne]

theorem key_pair_values (ops : Ops α) (t a b : Nat) (x y c sn : α) (s : State α) (hne : a ≠ b) :
    (keyPairAfter ops t a b x y c sn s).memory (globalCell 1 a) = some (ops.toHalf (pairReal ops x y c sn)) ∧
    (keyPairAfter ops t a b x y c sn s).memory (globalCell 1 b) = some (ops.toHalf (pairImaginary ops x y c sn)) := by
  simp [keyPairAfter, written, setReg, record, advance, globalCell, hne]

theorem query_pair_memory_frame (ops : Ops α) (t a b : Nat) (x y c sn : α) (s : State α)
    (l : Location) (ha : l ≠ globalCell 0 a) (hb : l ≠ globalCell 0 b) :
    (queryPairAfter ops t a b x y c sn s).memory l = s.memory l := by
  simp [queryPairAfter, written, setReg, record, advance, ha, hb]

theorem key_pair_memory_frame (ops : Ops α) (t a b : Nat) (x y c sn : α) (s : State α)
    (l : Location) (ha : l ≠ globalCell 1 a) (hb : l ≠ globalCell 1 b) :
    (keyPairAfter ops t a b x y c sn s).memory l = s.memory l := by
  simp [keyPairAfter, written, setReg, record, advance, ha, hb]

theorem query_pair_controls (ops : Ops α) (t a b : Nat) (x y c sn : α) (s : State α) :
    (queryPairAfter ops t a b x y c sn s).pc t = 23 ∧
    (queryPairAfter ops t a b x y c sn s).indices = s.indices ∧
    (queryPairAfter ops t a b x y c sn s).epochs = s.epochs := by
  exact ⟨by simp [queryPairAfter, written, advance], rfl, rfl⟩

theorem key_pair_controls (ops : Ops α) (t a b : Nat) (x y c sn : α) (s : State α) :
    (keyPairAfter ops t a b x y c sn s).pc t = 47 ∧
    (keyPairAfter ops t a b x y c sn s).indices = s.indices ∧
    (keyPairAfter ops t a b x y c sn s).epochs = s.epochs := by
  exact ⟨by simp [keyPairAfter, written, advance], rfl, rfl⟩

theorem query_pair_other_pc (ops : Ops α) (t a b u : Nat) (x y c sn : α) (s : State α)
    (hne : u ≠ t) : (queryPairAfter ops t a b x y c sn s).pc u = s.pc u := by
  simp [queryPairAfter, written, setReg, record, advance, hne]

theorem key_pair_other_pc (ops : Ops α) (t a b u : Nat) (x y c sn : α) (s : State α)
    (hne : u ≠ t) : (keyPairAfter ops t a b x y c sn s).pc u = s.pc u := by
  simp [keyPairAfter, written, setReg, record, advance, hne]

theorem query_pair_trace_length (ops : Ops α) (t a b : Nat) (x y c sn : α) (s : State α) :
    (queryPairAfter ops t a b x y c sn s).trace.length = s.trace.length + 4 := by
  simp [query_pair_trace, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

theorem key_pair_trace_length (ops : Ops α) (t a b : Nat) (x y c sn : α) (s : State α) :
    (keyPairAfter ops t a b x y c sn s).trace.length = s.trace.length + 4 := by
  simp [key_pair_trace, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

theorem mutable_access_good (neox : Bool) (t buffer offset : Nat) (write : Bool) (epoch : Epoch)
    (hb : buffer = 0 ∨ buffer = 1) (hw : writer buffer offset neox = t) :
    Good neox ⟨t, globalCell buffer offset, write, epoch⟩ :=
  .mutableGlobal rfl rfl hb hw.symm

theorem query_pair_good (neox : Bool) (ops : Ops α) (t a b : Nat) (x y c sn : α) (s : State α)
    (ha : writer 0 a neox = t) (hb : writer 0 b neox = t)
    (old : ∀ access ∈ s.trace, Good neox access) :
    ∀ access ∈ (queryPairAfter ops t a b x y c sn s).trace, Good neox access := by
  intro access hm
  rw [query_pair_trace] at hm
  simp only [List.mem_cons] at hm
  rcases hm with rfl | rfl | rfl | rfl | hm
  · exact mutable_access_good neox t 0 b true _ (Or.inl rfl) hb
  · exact mutable_access_good neox t 0 a true _ (Or.inl rfl) ha
  · exact mutable_access_good neox t 0 b false _ (Or.inl rfl) hb
  · exact mutable_access_good neox t 0 a false _ (Or.inl rfl) ha
  · exact old access hm

theorem key_pair_good (neox : Bool) (ops : Ops α) (t a b : Nat) (x y c sn : α) (s : State α)
    (ha : writer 1 a neox = t) (hb : writer 1 b neox = t)
    (old : ∀ access ∈ s.trace, Good neox access) :
    ∀ access ∈ (keyPairAfter ops t a b x y c sn s).trace, Good neox access := by
  intro access hm
  rw [key_pair_trace] at hm
  simp only [List.mem_cons] at hm
  rcases hm with rfl | rfl | rfl | rfl | hm
  · exact mutable_access_good neox t 1 b true _ (Or.inr rfl) hb
  · exact mutable_access_good neox t 1 a true _ (Or.inr rfl) ha
  · exact mutable_access_good neox t 1 b false _ (Or.inr rfl) hb
  · exact mutable_access_good neox t 1 a false _ (Or.inr rfl) ha
  · exact old access hm

#print axioms query_pair_trace
#print axioms key_pair_trace
#print axioms query_pair_values
#print axioms key_pair_values
#print axioms query_pair_memory_frame
#print axioms key_pair_memory_frame
#print axioms query_pair_controls
#print axioms key_pair_controls
#print axioms query_pair_other_pc
#print axioms key_pair_other_pc
#print axioms query_pair_trace_length
#print axioms key_pair_trace_length
#print axioms mutable_access_good
#print axioms query_pair_good
#print axioms key_pair_good
end LarkNativeRope
