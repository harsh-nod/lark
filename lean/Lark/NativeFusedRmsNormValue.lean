import Lark.NativeFusedRmsNormInit

/-! Source-ordered local values and the in-place remaining-cell invariant.
The residual cast is retained; shared memory keeps the original unrounded sum.
-/
namespace LarkNativeFusedRmsNorm
open LarkNonlinear
open LarkReduction (setIndex setReg)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def added (ops : Ops α) (input : Nat → Nat → α) (row tid iteration component : Nat) : α :=
  let offset := address row (column tid iteration component)
  ops.add (ops.fromHalf (input 0 offset)) (ops.fromHalf (input 1 offset))

def squared (ops : Ops α) (input : Nat → Nat → α) (row tid iteration component : Nat) : α :=
  let x := added ops input row tid iteration component
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

theorem slot_injective (tid a b : Nat) (_ha : a < 16) (_hb : b < 16)
    (he : slot tid a = slot tid b) : a = b := by
  unfold slot column at he
  omega

theorem flat_address_injective (row tid a b : Nat) (ha : a < 16) (hb : b < 16)
    (he : flatAddress row tid a = flatAddress row tid b) : a = b := by
  have hs : slot tid a = slot tid b := by unfold flatAddress address at he; omega
  exact slot_injective tid a b ha hb hs

def Pending (input : Nat → Nat → α) (row tid ordinal : Nat) (s : State α) : Prop :=
  (∀ j, j < 16 → s.memory (globalCell 0 (flatAddress row tid j)) =
    some (input 0 (flatAddress row tid j))) ∧
  (∀ j, ordinal ≤ j → j < 16 → s.memory (globalCell 1 (flatAddress row tid j)) =
    some (input 1 (flatAddress row tid j)))

theorem initial_pending (p : Shape) (input : Nat → Nat → α) (outside : Location → Option α)
    (row tid : Nat) (hr : row < p.rows) (ht : tid < 1024) :
    Pending input row tid 0 (initial p input outside) := by
  constructor
  · intro j hj
    have hb : flatAddress row tid j < p.rows * 16384 := by
      have h := slot_bound tid j ht hj
      unfold flatAddress address
      omega
    exact (initial_values p input outside _ hb).1
  · intro j hk hj
    have hb : flatAddress row tid j < p.rows * 16384 := by
      have h := slot_bound tid j ht hj
      unfold flatAddress address
      omega
    exact (initial_values p input outside _ hb).2

def componentAfter (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component t : Nat) (acc : α) (s : State α) : State α :=
  let col := column tid iteration component
  let offset := address row col
  let x := added ops input row tid iteration component
  let s := advance s t 10
  let s := setIndex s t 6 (col : Int) 11
  let s := setIndex s t 7 (offset : Int) 12
  let s := setReg (record s t (globalCell 0 offset) false) t 2 (ops.fromHalf (input 0 offset)) 13
  let s := setReg (record s t (globalCell 1 offset) false) t 3 (ops.fromHalf (input 1 offset)) 14
  let s := setReg s t 2 x 15
  let s := setReg s t 4 (ops.mul x x) 16
  let s := setReg s t 0 (ops.add acc (ops.mul x x)) 17
  let s := written t 18 (globalCell 1 offset) (ops.toHalf x) s
  let s := written t 19 (unroundedCell t col) x s
  let s := setIndex s t 5 ((component + 1 : Nat) : Int) 20
  advance s t 9

theorem component_memory (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component t : Nat) (acc : α) (s : State α) (l : Location) :
    (componentAfter ops input row tid iteration component t acc s).memory l =
      if l = unroundedCell t (column tid iteration component) then
        some (added ops input row tid iteration component)
      else if l = globalCell 1 (address row (column tid iteration component)) then
        some (ops.toHalf (added ops input row tid iteration component)) else s.memory l := rfl

theorem component_values (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component t : Nat) (acc : α) (s : State α) :
    (componentAfter ops input row tid iteration component t acc s).memory
        (globalCell 1 (address row (column tid iteration component))) =
      some (ops.toHalf (added ops input row tid iteration component)) ∧
    (componentAfter ops input row tid iteration component t acc s).memory
        (unroundedCell t (column tid iteration component)) =
      some (added ops input row tid iteration component) := by
  constructor <;> simp [component_memory, globalCell, unroundedCell]

theorem component_pending (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component t : Nat) (acc : α) (s : State α)
    (_hi : iteration < 2) (hc : component < 8)
    (pending : Pending input row tid (iteration * 8 + component) s) :
    Pending input row tid (iteration * 8 + component + 1)
      (componentAfter ops input row tid iteration component t acc s) := by
  constructor
  · intro j hj
    simpa [component_memory, globalCell, unroundedCell] using pending.1 j hj
  · intro j hk hj
    have hn : flatAddress row tid j ≠ address row (column tid iteration component) := by
      intro he
      have he' : flatAddress row tid j = flatAddress row tid (iteration * 8 + component) := by
        simpa only [flatAddress, slot_rank tid iteration component hc] using he
      have heq := flat_address_injective row tid j (iteration * 8 + component) hj (by omega) he'
      omega
    simpa [component_memory, globalCell, unroundedCell, hn] using pending.2 j (by omega) hj

theorem component_fields (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component t : Nat) (acc : α) (s : State α) :
    (componentAfter ops input row tid iteration component t acc s).pc t = 9 ∧
    (componentAfter ops input row tid iteration component t acc s).indices t 0 = s.indices t 0 ∧
    (componentAfter ops input row tid iteration component t acc s).indices t 1 = s.indices t 1 ∧
    (componentAfter ops input row tid iteration component t acc s).indices t 4 = s.indices t 4 ∧
    (componentAfter ops input row tid iteration component t acc s).indices t 5 = some ((component + 1 : Nat) : Int) ∧
    (componentAfter ops input row tid iteration component t acc s).regs t 0 =
      some (ops.add acc (squared ops input row tid iteration component)) := by
  simp [componentAfter, squared, setReg, setIndex, written, record, advance]

theorem component_epochs (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component t : Nat) (acc : α) (s : State α) :
    (componentAfter ops input row tid iteration component t acc s).epochs = s.epochs := rfl

theorem component_trace (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component t : Nat) (acc : α) (s : State α) :
    (componentAfter ops input row tid iteration component t acc s).trace =
      ⟨t, unroundedCell t (column tid iteration component), true, s.epochs t⟩ ::
      ⟨t, globalCell 1 (address row (column tid iteration component)), true, s.epochs t⟩ ::
      ⟨t, globalCell 1 (address row (column tid iteration component)), false, s.epochs t⟩ ::
      ⟨t, globalCell 0 (address row (column tid iteration component)), false, s.epochs t⟩ :: s.trace := rfl

theorem component_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component t : Nat) (acc : α) (s : State α)
    (ht : tid < 1024) (hi : iteration < 2) (hc : component < 8) (he : t = row * 1024 + tid)
    (good : ∀ a ∈ s.trace, Good a) :
    ∀ a ∈ (componentAfter ops input row tid iteration component t acc s).trace, Good a := by
  have hw := he.trans (address_writer p row tid iteration component ht hi hc).symm
  intro a ha
  simp only [component_trace, List.mem_cons] at ha
  rcases ha with rfl | rfl | rfl | rfl | ha
  · apply Good.unrounded rfl rfl rfl
    change t % 1024 = (column tid iteration component / 8) % 1024
    simp only [column]
    omega
  · exact Good.mutableGlobal rfl rfl (Or.inr rfl) hw
  · exact Good.mutableGlobal rfl rfl (Or.inr rfl) hw
  · exact Good.mutableGlobal rfl rfl (Or.inl rfl) hw
  · exact good a ha

#print axioms slot_injective
#print axioms initial_pending
#print axioms component_values
#print axioms component_pending
#print axioms component_fields
#print axioms component_trace
#print axioms component_good
end LarkNativeFusedRmsNorm
