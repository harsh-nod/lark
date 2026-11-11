import Lark.NativeSoftmaxMaxComponent

/-! Induction over the actual first-pass eight-component loop. -/
namespace LarkNativeSoftmax
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def maxFold (ops : Ops α) (input : Nat → Nat → α) (row tid iteration : Nat) :
    Nat → Nat → α → α
  | _,0,acc => acc
  | component,count+1,acc => maxFold ops input row tid iteration (component+1) count
      (ops.max acc (maxValue ops input row tid iteration component))

def maxComponents (ops : Ops α) (input : Nat → Nat → α) (row tid iteration t : Nat) :
    Nat → Nat → α → State α → State α
  | _,0,_,s => s
  | component,count+1,acc,s => maxComponents ops input row tid iteration t (component+1) count
      (ops.max acc (maxValue ops input row tid iteration component))
      (maxComponentAfter ops input row tid iteration component t acc s)

def maxComponentsCost (tid iteration : Nat) : Nat → Nat → Nat
  | _,0 => 0
  | component,count+1 => maxComponentCost tid iteration component +
      maxComponentsCost tid iteration (component+1) count

theorem max_components_ready (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t component count : Nat) (acc : α) (s : State α)
    (ready : MaxReady p input row tid iteration component t acc s) :
    MaxReady p input row tid iteration (component + count) t
      (maxFold ops input row tid iteration component count acc)
      (maxComponents ops input row tid iteration t component count acc s) := by
  induction count generalizing component acc s with
  | zero => simpa [maxFold,maxComponents] using ready
  | succ count ih =>
    have head := max_component_ready p ops input row tid iteration component t acc s ready
    have tail := ih (component+1) _ _ head
    simpa only [maxFold,maxComponents,show component + 1 + count = component + (count+1) by omega]
      using tail

theorem max_components_eq (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t component count extra : Nat) (acc : α) (s : State α)
    (hr : row < p.rows) (ht : tid < 1024) (hi : iteration < 7) (hc : component + count ≤ 8)
    (ready : MaxReady p input row tid iteration component t acc s) :
    LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t
        (extra + maxComponentsCost tid iteration component count) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t extra
        (maxComponents ops input row tid iteration t component count acc s) := by
  induction count generalizing component acc s with
  | zero => rfl
  | succ count ih =>
    have head := max_component_ready p ops input row tid iteration component t acc s ready
    simp only [maxComponentsCost,maxComponents]
    rewrite [show extra + (maxComponentCost tid iteration component +
        maxComponentsCost tid iteration (component+1) count) =
        (extra + maxComponentsCost tid iteration (component+1) count) +
          maxComponentCost tid iteration component by omega]
    rewrite [max_component_cycle p guarded ops input row tid iteration component t _ acc s
      hr ht hi (by omega) ready.rowIndex ready.baseIndex ready.componentIndex ready.accumulator
      ready.pc ready.reads]
    exact ih (component+1) _ _ (by omega) head

theorem max_component_cost_bounds (tid iteration component : Nat) :
    8 ≤ maxComponentCost tid iteration component ∧ maxComponentCost tid iteration component ≤ 9 := by
  unfold maxComponentCost clampCost
  split <;> decide

theorem max_components_cost_bound (tid iteration component count : Nat) :
    maxComponentsCost tid iteration component count ≤ 9 * count := by
  induction count generalizing component with
  | zero => simp [maxComponentsCost]
  | succ count ih =>
    have head := (max_component_cost_bounds tid iteration component).2
    have tail := ih (component+1)
    simp only [maxComponentsCost]
    omega

theorem max_components_frames (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t component count : Nat) (acc : α) (s : State α) :
    (maxComponents ops input row tid iteration t component count acc s).memory = s.memory ∧
    (maxComponents ops input row tid iteration t component count acc s).epochs = s.epochs ∧
    (maxComponents ops input row tid iteration t component count acc s).trace.length =
      s.trace.length + count := by
  induction count generalizing component acc s with
  | zero => exact ⟨rfl,rfl,by simp [maxComponents]⟩
  | succ count ih =>
    obtain ⟨_,_,_,hm,he,ht⟩ := max_component_fields ops input row tid iteration component t acc s
    obtain ⟨tailm,taile,tailt⟩ := ih (component+1)
      (ops.max acc (maxValue ops input row tid iteration component))
      (maxComponentAfter ops input row tid iteration component t acc s)
    refine ⟨tailm.trans hm,taile.trans he,?_⟩
    change (maxComponents ops input row tid iteration t (component+1) count _ _).trace.length = _
    rewrite [tailt,ht]
    simp only [List.length_cons]
    omega

theorem max_components_index_other (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t component count r : Nat) (acc : α) (s : State α)
    (h5 : r ≠ 5) (h6 : r ≠ 6) (h7 : r ≠ 7) :
    (maxComponents ops input row tid iteration t component count acc s).indices t r = s.indices t r := by
  induction count generalizing component acc s with
  | zero => rfl
  | succ count ih =>
    simp only [maxComponents]
    rewrite [ih]
    exact max_component_index_other ops input row tid iteration component t r acc s h5 h6 h7

#print axioms max_components_ready
#print axioms max_components_eq
#print axioms max_component_cost_bounds
#print axioms max_components_cost_bound
#print axioms max_components_frames
#print axioms max_components_index_other
end LarkNativeSoftmax
