import Lark.Collective

/-! Register-only phase updates, composed with the actual collective lane fold. -/
namespace LarkCollective.RegisterPhase
open LarkNonlinear
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def added (next t : Nat) (v : α) (s : State α) : State α :=
  advance { s with regs := fun u r =>
    if u = t ∧ r = 0 then some v else s.regs u r } t next

def partialState (next : Nat) (v : Nat → α) (s : State α) : Nat → State α
  | 0 => s
  | k + 1 => added next k (v k) (partialState next v s k)

theorem partial_pc (next : Nat) (v : Nat → α) (s : State α) (k t : Nat) :
    (partialState next v s k).pc t = if t < k then next else s.pc t := by
  induction k with
  | zero => simp [partialState]
  | succ k ih =>
      simp only [partialState, added, advance, ih]
      by_cases he : t = k
      · simp [he]
      · by_cases ht : t < k
        · have hh : t < k + 1 := by omega
          simp [he, ht, hh]
        · have hh : ¬ t < k + 1 := by omega
          simp [he, ht, hh]

theorem partial_regs (next : Nat) (v : Nat → α) (s : State α) (k t r : Nat) :
    (partialState next v s k).regs t r =
      if t < k ∧ r = 0 then some (v t) else s.regs t r := by
  induction k with
  | zero => simp [partialState]
  | succ k ih =>
      simp only [partialState, added, advance, ih]
      by_cases he : t = k
      · simp [he]
      · by_cases ht : t < k
        · have hh : t < k + 1 := by omega
          simp [he, ht, hh]
        · have hh : ¬ t < k + 1 := by omega
          simp [he, ht, hh]

theorem partial_preserves (next : Nat) (v : Nat → α) (s : State α) (k : Nat) :
    (partialState next v s k).indices = s.indices ∧
    (partialState next v s k).memory = s.memory ∧
    (partialState next v s k).epochs = s.epochs ∧
    (partialState next v s k).trace = s.trace := by
  induction k with
  | zero => exact ⟨rfl, rfl, rfl, rfl⟩
  | succ k ih => simpa only [partialState, added, advance] using ih

theorem assign_step (ops : Ops α) (l : Layout) (g : Geometry) (pc t : Nat)
    (s : State α) (a b : α) (hp : s.pc t = pc)
    (ha : s.regs t 0 = some a) (hb : s.regs t 1 = some b) :
    execute ops l g t (.assign 0 (.bin .add (.reg 0) (.reg 1))) s =
      some (added (pc + 1) t (ops.add a b) s) := by
  simp [execute, evalExpr, applyBinary, ha, hb, hp, added, advance]

/-- The caller proves both instruction lookup and the actual following cut. -/
theorem lane_step (ops : Ops α) (l : Layout) (g : Geometry) (p : List Instr)
    (pc t extra : Nat) (s : State α) (a b : α) (cut : Cut)
    (hp : s.pc t = pc) (ha : s.regs t 0 = some a) (hb : s.regs t 1 = some b)
    (hi : p[pc]? = some (.scalar (.assign 0 (.bin .add (.reg 0) (.reg 1)))))
    (hc : parked p (added (pc + 1) t (ops.add a b) s) t = some cut) :
    runLane ops l g p t (extra + 2) s = some (added (pc + 1) t (ops.add a b) s) := by
  have hn : parked p s t = none := by simp [parked, hp, hi]
  have he := assign_step ops l g pc t s a b hp ha hb
  change runLane ops l g p t ((extra + 1) + 1) s = _
  rewrite [runLane, hn]
  simp only [hp, hi, bind, pure, Option.bind, he]
  simp only [runLane, hc]

#print axioms partial_preserves
#print axioms lane_step
end LarkCollective.RegisterPhase
