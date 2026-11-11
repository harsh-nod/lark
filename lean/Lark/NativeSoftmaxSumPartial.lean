import Lark.NativeSoftmaxSumStages

/-! Actual final XOR sum, logical-lane-zero partial store and third block barrier.
Each native wave has two distinct partial writers, one per logical32 group.
-/
namespace LarkNativeSoftmax
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem sum_partial_barrier (guarded : Bool) :
    (program guarded)[82]? = some (.scalar (.barrier .block)) := by cases guarded <;> decide

def sumPartialCell (t warp : Nat) : Location := ⟨.shared, t / 1024, 1, warp⟩
def sumPartialWritten (t warp : Nat) (value : α) (s : State α) : State α :=
  written t 82 (sumPartialCell t warp) value s
def sumPartialAfter (t lane warp : Nat) (value : α) (s : State α) : State α :=
  if lane = 0 then sumPartialWritten t warp value (advance s t 81) else advance s t 82

theorem sum_partial_branch_code (guarded : Bool) :
    (program guarded)[80]? = some (.scalar (.branch (.eq (.ivar 3) (.const 0)) 82)) := by cases guarded <;> decide
theorem sum_partial_store_code (guarded : Bool) :
    (program guarded)[81]? = some (.scalar (.store .shared 1 (.ivar 2) (.reg 6))) := by cases guarded <;> decide

theorem sum_partial_location (p : Shape) (t warp : Nat) (hw : warp < 32) :
    location (layout p) (geometry p) t .shared 1 (warp : Int) true = some (sumPartialCell t warp) := by
  simp [location, layout, geometry, sumPartialCell, show ¬ (warp : Int) < 0 by omega, hw]

theorem sum_partial_store_eq (p : Shape) (ops : Ops α) (t warp : Nat) (value : α) (s : State α)
    (hw : warp < 32) (hi : s.indices t 2 = some (warp : Int))
    (ha : s.regs t 6 = some value) (hp : s.pc t = 81) :
    execute ops (layout p) (geometry p) t (.store .shared 1 (.ivar 2) (.reg 6)) s =
      some (sumPartialWritten t warp value s) := by
  simp [execute, evalIndex, hi, sum_partial_location p t warp hw, evalExpr, ha, hp, sumPartialWritten, written, record]

theorem sum_partial_lane (p : Shape) (guarded : Bool) (ops : Ops α) (t lane warp extra : Nat) (value : α) (s : State α)
    (hw : warp < 32) (hi2 : s.indices t 3 = some (lane : Int))
    (hi3 : s.indices t 2 = some (warp : Int)) (ha : s.regs t 6 = some value) (hp : s.pc t = 80) :
    LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t (extra + 3) s =
      some (sumPartialAfter t lane warp value s) := by
  have heq : evalPredicate (geometry p) t s (.eq (.ivar 3) (.const 0)) = some (decide (lane = 0)) := by
    simp [evalPredicate, evalIndex, hi2, int32] <;> omega
  by_cases hl : lane = 0
  · have hg : evalPredicate (geometry p) t s (.eq (.ivar 3) (.const 0)) = some true := by simpa [hl] using heq
    let s1 := advance s t 81
    have e1 : execute ops (layout p) (geometry p) t (.branch (.eq (.ivar 3) (.const 0)) 82) s = some s1 := by
      simp [execute, hg, hp, s1]
    have e2 := sum_partial_store_eq p ops t warp value s1 hw hi3 ha (by simp [s1, advance])
    rewrite [scalar_step p guarded ops t 80 _ _ s s1 (sum_partial_branch_code guarded) hp e1]
    rewrite [scalar_step p guarded ops t 81 _ _ s1 _ (sum_partial_store_code guarded) (by simp [s1, advance]) e2]
    have hcut : LarkCollective.parked (program guarded) (sumPartialWritten t warp value s1) t = some .block := by
      simp only [LarkCollective.parked, sumPartialWritten, written, advance, ↓reduceIte]
      rewrite [sum_partial_barrier guarded]
      rfl
    rewrite [LarkCollective.runLane, hcut]
    simp only [sumPartialAfter, hl, ↓reduceIte]
    rfl
  · have hg : evalPredicate (geometry p) t s (.eq (.ivar 3) (.const 0)) = some false := by simpa [hl] using heq
    have e1 : execute ops (layout p) (geometry p) t (.branch (.eq (.ivar 3) (.const 0)) 82) s =
        some (advance s t 82) := by simp [execute, hg]
    rewrite [scalar_step p guarded ops t 80 _ _ s _ (sum_partial_branch_code guarded) hp e1]
    have hcut : LarkCollective.parked (program guarded) (advance s t 82) t = some .block := by
      simp only [LarkCollective.parked, advance, ↓reduceIte]
      rewrite [sum_partial_barrier guarded]
      rfl
    rewrite [LarkCollective.runLane, hcut]
    simp only [sumPartialAfter, hl, ↓reduceIte]

theorem sum_partial_fields (t lane warp : Nat) (value : α) (s : State α) :
    (sumPartialAfter t lane warp value s).pc t = 82 ∧
    (sumPartialAfter t lane warp value s).indices = s.indices ∧
    (sumPartialAfter t lane warp value s).regs = s.regs ∧
    (sumPartialAfter t lane warp value s).epochs = s.epochs := by
  unfold sumPartialAfter
  split <;> simp [sumPartialWritten, written, advance, record]

theorem sum_partial_other (t u lane warp : Nat) (value : α) (s : State α) (hu : u ≠ t) :
    (sumPartialAfter t lane warp value s).pc u = s.pc u := by
  unfold sumPartialAfter
  split <;> simp [sumPartialWritten, written, advance, record, hu]

theorem sum_partial_memory_other (t lane warp : Nat) (value : α) (s : State α) (l : Location)
    (hl : l ≠ sumPartialCell t warp) : (sumPartialAfter t lane warp value s).memory l = s.memory l := by
  unfold sumPartialAfter
  split <;> simp [sumPartialWritten, written_memory, advance, hl]

theorem sum_partial_value (t warp : Nat) (value : α) (s : State α) :
    (sumPartialAfter t 0 warp value s).memory (sumPartialCell t warp) = some value := by
  simp [sumPartialAfter, sumPartialWritten, written_memory, advance]

theorem sum_partial_good (t lane warp : Nat) (value : α) (s : State α)
    (hl : lane = (t % 1024) % 32) (hw : warp = (t % 1024) / 32) (he : (s.epochs t).block = 2)
    (good : ∀ a ∈ s.trace, Good a) :
    ∀ a ∈ (sumPartialAfter t lane warp value s).trace, Good a := by
  by_cases hz : lane = 0
  · intro a ha
    simp only [sumPartialAfter, hz, ↓reduceIte, sumPartialWritten, written, advance, record, List.mem_cons] at ha
    rcases ha with rfl | ha
    · apply Good.partialStore rfl rfl (by change 1 < 2; decide)
      · exact hw
      · change (t % 1024) % 32 = 0
        omega
      · simpa only [sumPartialCell,show 2*1=2 by decide] using he
      · rfl
    · exact good a ha
  · simpa only [sumPartialAfter, hz, ↓reduceIte, advance] using good

def sumLastAfter (ops : Ops α) (t : Nat) (a b : α) (s : State α) : State α :=
  sumPartialAfter t ((t % 1024) % 32) ((t % 1024) / 32) (ops.add a b) (sumCombineAfter ops t 79 a b s)

theorem sum_last_lane (p : Shape) (guarded : Bool) (ops : Ops α) (t : Nat) (a b : α) (s : State α)
    (hi : MaxNativeIndices t s) (ha : s.regs t 6 = some a) (hb : s.regs t 9 = some b) (hp : s.pc t = 79) :
    LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t fuel.lane s =
      some (sumLastAfter ops t a b s) := by
  rewrite [show fuel.lane = 4095 + 1 by decide,
    sum_combine_eq p guarded ops t 79 4095 a b s hp ha hb (by cases guarded <;> decide)]
  apply sum_partial_lane p guarded ops t ((t % 1024) % 32) ((t % 1024) / 32) 4092 (ops.add a b) (sumCombineAfter ops t 79 a b s)
    (by omega) hi.2.2.2 hi.2.2.1
  · simp [sumCombineAfter, LarkReduction.setReg, advance]
  · simp [sumCombineAfter, LarkReduction.setReg, advance]

theorem sum_last_fields (ops : Ops α) (t : Nat) (a b : α) (s : State α) :
    (sumLastAfter ops t a b s).pc t = 82 ∧
    (sumLastAfter ops t a b s).regs t 6 = some (ops.add a b) ∧
    (sumLastAfter ops t a b s).indices = s.indices ∧
    (sumLastAfter ops t a b s).epochs = s.epochs := by
  have h := sum_partial_fields t ((t % 1024) % 32) ((t % 1024) / 32) (ops.add a b) (sumCombineAfter ops t 79 a b s)
  refine ⟨h.1, ?_, h.2.1, h.2.2.2⟩
  rewrite [show (sumLastAfter ops t a b s).regs = (sumCombineAfter ops t 79 a b s).regs from h.2.2.1]
  simp [sumCombineAfter, LarkReduction.setReg, advance]

theorem sum_last_other (ops : Ops α) (t u : Nat) (a b : α) (s : State α) (hu : u ≠ t) :
    (sumLastAfter ops t a b s).pc u = s.pc u ∧
    (sumLastAfter ops t a b s).regs u = s.regs u := by
  have h := sum_partial_fields t ((t % 1024) % 32) ((t % 1024) / 32) (ops.add a b) (sumCombineAfter ops t 79 a b s)
  have other := sum_combine_other ops t 79 u a b s hu
  exact ⟨(sum_partial_other t u _ _ _ _ hu).trans other.1, (congrFun h.2.2.1 u).trans other.2⟩

theorem sum_last_good (ops : Ops α) (t : Nat) (a b : α) (s : State α)
    (he : (s.epochs t).block = 2) (good : ∀ a ∈ s.trace, Good a) :
    ∀ access ∈ (sumLastAfter ops t a b s).trace, Good access :=
  sum_partial_good t _ _ _ _ rfl rfl he good

#print axioms sum_partial_barrier
#print axioms sum_partial_branch_code
#print axioms sum_partial_store_code
#print axioms sum_partial_location
#print axioms sum_partial_store_eq
#print axioms sum_partial_lane
#print axioms sum_partial_fields
#print axioms sum_partial_other
#print axioms sum_partial_memory_other
#print axioms sum_partial_value
#print axioms sum_partial_good
#print axioms sum_last_lane
#print axioms sum_last_fields
#print axioms sum_last_other
#print axioms sum_last_good
end LarkNativeSoftmax
