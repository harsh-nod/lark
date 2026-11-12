import Lark.NativeFlashInferRmsNormInit

/-! Source-order scalar values and the read-only input invariant. -/
namespace LarkNativeFlashInferRmsNorm
open LarkNonlinear
open LarkReduction (setIndex setReg)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def loaded (ops : Ops α) (input : Nat → Nat → α) (row tid iteration component : Nat) : α :=
  ops.fromHalf (input 1 (address row (column tid iteration component)))

def squared (ops : Ops α) (input : Nat → Nat → α) (row tid iteration component : Nat) : α :=
  let x := loaded ops input row tid iteration component
  ops.mul x x

def folded (ops : Ops α) (input : Nat → Nat → α) (row tid iteration : Nat) : Nat → Nat → α → α
  | _, 0, acc => acc
  | component, remaining + 1, acc => folded ops input row tid iteration (component + 1) remaining
      (ops.add acc (squared ops input row tid iteration component))

def threadSum (ops : Ops α) (input : Nat → Nat → α) (row tid : Nat) : α :=
  folded ops input row tid 1 0 8 (folded ops input row tid 0 0 8 (ops.literal 0 1))

def slot (tid ordinal : Nat) : Nat := column tid (ordinal / 8) (ordinal % 8)
def flatAddress (row tid ordinal : Nat) : Nat := address row (slot tid ordinal)

theorem slot_rank (tid iteration component : Nat) (hc : component < 8) :
    slot tid (iteration * 8 + component) = column tid iteration component := by
  have hd : (iteration * 8 + component) / 8 = iteration := by omega
  have hm : (iteration * 8 + component) % 8 = component := by omega
  simp only [slot, hd, hm]

theorem slot_bound (tid ordinal : Nat) (ht : tid < 1024) (ho : ordinal < 16) :
    slot tid ordinal < 16384 :=
  column_bound tid (ordinal / 8) (ordinal % 8) ht (by omega) (Nat.mod_lt _ (by decide))

def InputReady (input : Nat → Nat → α) (row tid : Nat) (s : State α) : Prop :=
  ∀ j, j < 16 → s.memory (globalCell 1 (flatAddress row tid j)) =
    some (input 1 (flatAddress row tid j))

theorem initial_input_ready (p : Shape) (input : Nat → Nat → α) (outside : Location → Option α)
    (row tid : Nat) (hr : row < p.rows) (ht : tid < 1024) :
    InputReady input row tid (initial p input outside) := by
  intro j hj
  have hb : flatAddress row tid j < p.rows * 16384 := by
    have h := slot_bound tid j ht hj
    unfold flatAddress address
    omega
  exact initial_input p input outside _ hb

def componentAfter (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component t : Nat) (acc : α) (s : State α) : State α :=
  let col := column tid iteration component
  let offset := address row col
  let x := loaded ops input row tid iteration component
  let square := ops.mul x x
  let s := advance s t 10
  let s := setIndex s t 6 (col : Int) 11
  let s := setIndex s t 7 (offset : Int) 12
  let s := setReg (record s t (globalCell 1 offset) false) t 2 x 13
  let s := setReg s t 3 square 14
  let s := setReg s t 0 (ops.add acc square) 15
  let s := setIndex s t 5 ((component + 1 : Nat) : Int) 16
  advance s t 9

theorem component_memory (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component t : Nat) (acc : α) (s : State α) :
    (componentAfter ops input row tid iteration component t acc s).memory = s.memory := rfl

theorem component_input_ready (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component t : Nat) (acc : α) (s : State α)
    (ready : InputReady input row tid s) :
    InputReady input row tid (componentAfter ops input row tid iteration component t acc s) := ready

theorem component_fields (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component t : Nat) (acc : α) (s : State α) :
    (componentAfter ops input row tid iteration component t acc s).pc t = 9 ∧
    (componentAfter ops input row tid iteration component t acc s).indices t 0 = s.indices t 0 ∧
    (componentAfter ops input row tid iteration component t acc s).indices t 1 = s.indices t 1 ∧
    (componentAfter ops input row tid iteration component t acc s).indices t 4 = s.indices t 4 ∧
    (componentAfter ops input row tid iteration component t acc s).indices t 5 = some ((component + 1 : Nat) : Int) ∧
    (componentAfter ops input row tid iteration component t acc s).regs t 0 =
      some (ops.add acc (squared ops input row tid iteration component)) := by
  simp [componentAfter, squared, setReg, setIndex, record, advance]

theorem component_epochs (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component t : Nat) (acc : α) (s : State α) :
    (componentAfter ops input row tid iteration component t acc s).epochs = s.epochs := rfl

theorem component_trace (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component t : Nat) (acc : α) (s : State α) :
    (componentAfter ops input row tid iteration component t acc s).trace =
      ⟨t, globalCell 1 (address row (column tid iteration component)), false, s.epochs t⟩ :: s.trace := rfl

theorem component_good (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component t : Nat) (acc : α) (s : State α)
    (good : ∀ a ∈ s.trace, Good a) :
    ∀ a ∈ (componentAfter ops input row tid iteration component t acc s).trace, Good a := by
  intro a ha
  simp only [component_trace, List.mem_cons] at ha
  rcases ha with rfl | ha
  · exact Good.input rfl rfl (Or.inl rfl) rfl
  · exact good a ha

theorem component_other (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component t u : Nat) (acc : α) (s : State α) (hu : u ≠ t) :
    (componentAfter ops input row tid iteration component t acc s).pc u = s.pc u ∧
    (componentAfter ops input row tid iteration component t acc s).indices u = s.indices u ∧
    (componentAfter ops input row tid iteration component t acc s).regs u = s.regs u := by
  simp [componentAfter, setIndex, setReg, record, advance, hu]

#print axioms slot_rank
#print axioms slot_bound
#print axioms initial_input_ready
#print axioms component_memory
#print axioms component_input_ready
#print axioms component_fields
#print axioms component_epochs
#print axioms component_trace
#print axioms component_good
#print axioms component_other
end LarkNativeFlashInferRmsNorm
