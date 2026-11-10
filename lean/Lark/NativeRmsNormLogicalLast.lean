import Lark.NativeRmsNormScaleStore

/-! Execute each active lane's final logical shuffle tail through the real scale
store and second block barrier. Physical inactive lanes are composed separately.
-/
namespace LarkNativeRmsNorm
open LarkNonlinear
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def logicalLastAfter (ops : Ops α) (t row tid lane : Nat) (a b : α) (s : State α) : State α :=
  scaleAfter ops t row tid (if lane + 8 < 16 then ops.add a b else a)
    (guardedAfter ops t 50 lane 8 16 a b s)

theorem logical_last_lane (p : Shape) (ops : Ops α) (t row tid lane : Nat) (a b : α) (s : State α)
    (hr : t / 1024 = row) (hl : lane < 16)
    (hi1 : s.indices t 1 = some (tid : Int)) (hi2 : s.indices t 2 = some (lane : Int))
    (ha : s.regs t 0 = some a) (hb : s.regs t 1 = some b) (hp : s.pc t = 51) :
    LarkCollective.runLane ops (layout p) (geometry p) program t fuel.lane s =
      some (logicalLastAfter ops t row tid lane a b s) := by
  let next := guardedAfter ops t 50 lane 8 16 a b s
  let value := if lane + 8 < 16 then ops.add a b else a
  have hpres := guarded_preserves ops t 50 lane 8 16 a b s
  have hi' : next.indices t 1 = some (tid : Int) := (congrFun (congrFun hpres.1 t) 1).trans hi1
  have ha' : next.regs t 0 = some value := guarded_acc ops t 50 lane 8 16 a b s ha
  have hp' : next.pc t = 53 := guarded_pc ops t 50 lane 8 16 a b s
  have hv : evalIndex (geometry p) t s (.const 16) = some 16 := LarkReduction.int32_cast 16 (by decide)
  by_cases h : lane + 8 < 16
  · rewrite [show fuel.lane = 254 + 2 by decide,
      guarded_true_eq p ops t 50 lane 8 16 254 (.const 16) a b s (by omega) (by decide) hi2 hv ha hb hp
        (final_guard_code 3 (by decide)).1 (final_guard_code 3 (by decide)).2 h]
    exact scale_lane p ops t row tid 251 value next hr hi' ha' hp'
  · rewrite [show fuel.lane = 255 + 1 by decide,
      guarded_false_eq p ops t 50 lane 8 16 255 (.const 16) a b s (by omega) (by decide) hi2 hv hp
        (final_guard_code 3 (by decide)).1 h]
    exact scale_lane p ops t row tid 252 value next hr hi' ha' hp'

theorem logical_last_fields (ops : Ops α) (t row tid lane : Nat) (a b : α) (s : State α) :
    (logicalLastAfter ops t row tid lane a b s).pc t = 55 ∧
    (logicalLastAfter ops t row tid lane a b s).indices = s.indices ∧
    (logicalLastAfter ops t row tid lane a b s).epochs = s.epochs := by
  have h := scale_fields ops t row tid (if lane + 8 < 16 then ops.add a b else a)
    (guardedAfter ops t 50 lane 8 16 a b s)
  have hg := guarded_preserves ops t 50 lane 8 16 a b s
  exact ⟨h.1, h.2.1.trans hg.1, h.2.2.2.trans hg.2.2.1⟩

theorem logical_last_other (ops : Ops α) (t u row tid lane : Nat) (a b : α) (s : State α)
    (hu : u ≠ t) :
    (logicalLastAfter ops t row tid lane a b s).pc u = s.pc u ∧
    (logicalLastAfter ops t row tid lane a b s).regs u = s.regs u := by
  have hpc := scale_other ops t u row tid (if lane + 8 < 16 then ops.add a b else a)
    (guardedAfter ops t 50 lane 8 16 a b s) hu
  have hg := guarded_other ops t u 50 lane 8 16 a b s hu
  have hr := (scale_fields ops t row tid (if lane + 8 < 16 then ops.add a b else a)
    (guardedAfter ops t 50 lane 8 16 a b s)).2.2.1
  exact ⟨hpc.trans hg.1, (congrFun hr u).trans hg.2⟩

theorem logical_last_acc (ops : Ops α) (t row tid lane : Nat) (a b : α) (s : State α)
    (ha : s.regs t 0 = some a) :
    (logicalLastAfter ops t row tid lane a b s).regs t 0 =
      some (if lane + 8 < 16 then ops.add a b else a) := by
  have h := (scale_fields ops t row tid (if lane + 8 < 16 then ops.add a b else a)
    (guardedAfter ops t 50 lane 8 16 a b s)).2.2.1
  exact (congrFun (congrFun h t) 0).trans (guarded_acc ops t 50 lane 8 16 a b s ha)

theorem logical_last_memory_other (ops : Ops α) (t row tid lane : Nat) (a b : α) (s : State α)
    (l : Location) (hl : l ≠ scaleSlot row) :
    (logicalLastAfter ops t row tid lane a b s).memory l = s.memory l :=
  (scale_memory_other ops t row tid _ _ l hl).trans (congrFun (guarded_preserves ops t 50 lane 8 16 a b s).2.1 l)

theorem logical_last_memory_nonzero (ops : Ops α) (t row tid lane : Nat) (a b : α) (s : State α)
    (ht : tid ≠ 0) : (logicalLastAfter ops t row tid lane a b s).memory = s.memory := by
  change (scaleAfter ops t row tid _ _).memory = _
  simp only [scaleAfter, ht, ↓reduceIte, advance]
  exact (guarded_preserves ops t 50 lane 8 16 a b s).2.1

theorem logical_last_value (ops : Ops α) (t row : Nat) (a b : α) (s : State α) :
    (logicalLastAfter ops t row 0 0 a b s).memory (scaleSlot row) = some (scaleFrom ops (ops.add a b)) :=
  scale_value ops t row _ _

theorem logical_last_good (p : Shape) (ops : Ops α) (t row tid lane : Nat) (a b : α) (s : State α)
    (hr : t / 1024 = row) (ht : tid = t % 1024) (he : (s.epochs t).block = 1)
    (good : ∀ access ∈ s.trace, LarkReductionFootprint.Good (traversal p) 0 access) :
    ∀ access ∈ (logicalLastAfter ops t row tid lane a b s).trace,
      LarkReductionFootprint.Good (traversal p) 0 access := by
  have hpres := guarded_preserves ops t 50 lane 8 16 a b s
  apply scale_good p ops t row tid _ _ hr ht
  · exact (congrArg (fun epochs => (epochs t).block) hpres.2.2.1).trans he
  · exact fun access ha => good access (hpres.2.2.2 ▸ ha)

#print axioms logical_last_lane
#print axioms logical_last_value
#print axioms logical_last_good
end LarkNativeRmsNorm
