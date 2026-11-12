import Lark.NativeSglangRmsNormPreloads

/-! Paired square values and exact source-order state updates. -/
namespace LarkNativeSglangRmsNorm
open LarkNonlinear
open LarkReduction (setIndex setReg)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def pairLoaded (ops : Ops α) (input : Nat → Nat → α) (row tid iteration component : Nat) : α :=
  ops.fromHalf (input 1 (address row (column tid iteration component)))
def pairSquare (ops : Ops α) (input : Nat → Nat → α) (row tid iteration pair : Nat) : α :=
  let x := pairLoaded ops input row tid iteration (pair * 2)
  let y := pairLoaded ops input row tid iteration (pair * 2 + 1)
  ops.add (ops.mul x x) (ops.mul y y)
def pairFold (ops : Ops α) (input : Nat → Nat → α) (row tid iteration : Nat) : Nat → Nat → α → α
  | _,0,acc => acc
  | pair,remaining + 1,acc => pairFold ops input row tid iteration (pair + 1) remaining
      (ops.add acc (pairSquare ops input row tid iteration pair))
def threadSum (ops : Ops α) (input : Nat → Nat → α) (row tid : Nat) : α :=
  pairFold ops input row tid 1 0 4 (pairFold ops input row tid 0 0 4 (ops.literal 0 1))

theorem cached_input_at (input : Nat → Nat → α) (row tid iteration component t : Nat)
    (s : State α) (hi : iteration < 2) (hc : component < 8)
    (cached : InputPrefix input row tid 16 t s) :
    s.memory (privateCell t 0 (iteration * 8 + component)) =
      some (input 1 (address row (column tid iteration component))) := by
  have hd : (iteration * 8 + component) / 8 = iteration := by omega
  have hm : (iteration * 8 + component) % 8 = component := by omega
  simpa only [hd,hm] using cached (iteration * 8 + component) (by omega)

def pairAfter (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration pair t : Nat) (acc : α) (s : State α) : State α :=
  let slot := iteration * 8 + pair * 2
  let x := pairLoaded ops input row tid iteration (pair * 2)
  let y := pairLoaded ops input row tid iteration (pair * 2 + 1)
  let s := advance s t 33
  let s := setIndex s t 15 (slot : Int) 34
  let s := setReg (record s t (privateCell t 0 slot) false) t 2 x 35
  let s := setReg (record s t (privateCell t 0 (slot + 1)) false) t 3 y 36
  let s := setReg s t 4 (ops.mul x x) 37
  let s := setReg s t 5 (ops.mul y y) 38
  let s := setReg s t 6 (pairSquare ops input row tid iteration pair) 39
  let s := setReg s t 0 (ops.add acc (pairSquare ops input row tid iteration pair)) 40
  let s := setIndex s t 14 ((pair + 1 : Nat) : Int) 41
  advance s t 32

theorem pair_memory (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration pair t : Nat) (acc : α) (s : State α) :
    (pairAfter ops input row tid iteration pair t acc s).memory = s.memory := rfl

theorem pair_fields (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration pair t : Nat) (acc : α) (s : State α) :
    (pairAfter ops input row tid iteration pair t acc s).pc t = 32 ∧
    (pairAfter ops input row tid iteration pair t acc s).indices t 0 = s.indices t 0 ∧
    (pairAfter ops input row tid iteration pair t acc s).indices t 1 = s.indices t 1 ∧
    (pairAfter ops input row tid iteration pair t acc s).indices t 13 = s.indices t 13 ∧
    (pairAfter ops input row tid iteration pair t acc s).indices t 14 = some ((pair + 1 : Nat) : Int) ∧
    (pairAfter ops input row tid iteration pair t acc s).regs t 0 =
      some (ops.add acc (pairSquare ops input row tid iteration pair)) := by
  simp [pairAfter,setReg,setIndex,record,advance]

theorem pair_epochs (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration pair t : Nat) (acc : α) (s : State α) :
    (pairAfter ops input row tid iteration pair t acc s).epochs = s.epochs := rfl

theorem pair_trace (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration pair t : Nat) (acc : α) (s : State α) :
    (pairAfter ops input row tid iteration pair t acc s).trace =
      ⟨t,privateCell t 0 (iteration * 8 + pair * 2 + 1),false,s.epochs t⟩ ::
      ⟨t,privateCell t 0 (iteration * 8 + pair * 2),false,s.epochs t⟩ :: s.trace := rfl

theorem pair_good (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration pair t : Nat) (acc : α) (s : State α) (good : ∀ a ∈ s.trace, Good a) :
    ∀ a ∈ (pairAfter ops input row tid iteration pair t acc s).trace, Good a := by
  intro a ha
  simp only [pair_trace,List.mem_cons] at ha
  rcases ha with rfl | rfl | ha
  · exact Good.localAccess rfl rfl
  · exact Good.localAccess rfl rfl
  · exact good a ha

theorem pair_other (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration pair t u : Nat) (acc : α) (s : State α) (hu : u ≠ t) :
    (pairAfter ops input row tid iteration pair t acc s).pc u = s.pc u ∧
    (pairAfter ops input row tid iteration pair t acc s).indices u = s.indices u ∧
    (pairAfter ops input row tid iteration pair t acc s).regs u = s.regs u := by
  simp [pairAfter,setIndex,setReg,record,advance,hu]

#print axioms cached_input_at
#print axioms pair_memory
#print axioms pair_fields
#print axioms pair_epochs
#print axioms pair_trace
#print axioms pair_good
#print axioms pair_other
end LarkNativeSglangRmsNorm
