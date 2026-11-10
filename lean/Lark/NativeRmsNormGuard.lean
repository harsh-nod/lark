import Lark.NativeRmsNormShuffle

/-! Actual guarded scalar updates between native shuffle instructions.
The final stage's shared store is a separate execution obligation.
-/
namespace LarkNativeRmsNorm
open LarkNonlinear
open LarkReduction (setReg int32_cast execute_pure_of)
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem first_guard_code (n : Nat) (hn : n < 6) :
    program[18 + 3 * n + 1]? = some (.scalar (.branch
      (.lt (.add (.ivar 2) (.const (2 ^ n : Nat))) (.ivar 4)) (18 + 3 * n + 3))) ∧
    program[18 + 3 * n + 2]? = some (.scalar (.assign 0 (.bin .add (.reg 0) (.reg 1)))) := by
  have all : ∀ n : Fin 6,
    program[18 + 3 * n.val + 1]? = some (.scalar (.branch
      (.lt (.add (.ivar 2) (.const (2 ^ n.val : Nat))) (.ivar 4)) (18 + 3 * n.val + 3))) ∧
    program[18 + 3 * n.val + 2]? = some (.scalar (.assign 0 (.bin .add (.reg 0) (.reg 1)))) := by decide
  exact all ⟨n, hn⟩

theorem final_guard_code (n : Nat) (hn : n < 4) :
    program[41 + 3 * n + 1]? = some (.scalar (.branch
      (.lt (.add (.ivar 2) (.const (2 ^ n : Nat))) (.const 16)) (41 + 3 * n + 3))) ∧
    program[41 + 3 * n + 2]? = some (.scalar (.assign 0 (.bin .add (.reg 0) (.reg 1)))) := by
  have all : ∀ n : Fin 4,
    program[41 + 3 * n.val + 1]? = some (.scalar (.branch
      (.lt (.add (.ivar 2) (.const (2 ^ n.val : Nat))) (.const 16)) (41 + 3 * n.val + 3))) ∧
    program[41 + 3 * n.val + 2]? = some (.scalar (.assign 0 (.bin .add (.reg 0) (.reg 1)))) := by decide
  exact all ⟨n, hn⟩

def guardedAfter (ops : Ops α) (t pc lane distance valid : Nat) (a b : α) (s : State α) : State α :=
  if lane + distance < valid then setReg (advance s t (pc + 2)) t 0 (ops.add a b) (pc + 3)
  else advance s t (pc + 3)

theorem guarded_true_eq (p : Shape) (ops : Ops α) (t pc lane distance valid extra : Nat)
    (bound : Index) (a b : α) (s : State α) (hl : lane < 64) (hd : distance ≤ 32)
    (hi : s.indices t 2 = some (lane : Int)) (hv : evalIndex (geometry p) t s bound = some (valid : Int))
    (ha : s.regs t 0 = some a) (hb : s.regs t 1 = some b) (hp : s.pc t = pc + 1)
    (hbranch : program[pc + 1]? = some (.scalar (.branch
      (.lt (.add (.ivar 2) (.const (distance : Int))) bound) (pc + 3))))
    (hadd : program[pc + 2]? = some (.scalar (.assign 0 (.bin .add (.reg 0) (.reg 1)))))
    (hguard : lane + distance < valid) :
    LarkCollective.runLane ops (layout p) (geometry p) program t (extra + 2) s =
      LarkCollective.runLane ops (layout p) (geometry p) program t extra
        (guardedAfter ops t pc lane distance valid a b s) := by
  have hsum := LarkReduction.eval_add_of (geometry p) t s (.ivar 2) (.const (distance : Int))
    (lane : Int) (distance : Int) ((lane + distance : Nat) : Int) hi (int32_cast distance (by omega))
    ((congrArg int32 (Int.natCast_add lane distance).symm).trans (int32_cast _ (by omega)))
  have hg := LarkReduction.predicate_lt_of (geometry p) t s
    (.add (.ivar 2) (.const (distance : Int))) bound ((lane + distance : Nat) : Int) (valid : Int)
    hsum hv (by omega)
  let s1 := advance s t (pc + 2)
  have h1 : execute ops (layout p) (geometry p) t
      (.branch (.lt (.add (.ivar 2) (.const (distance : Int))) bound) (pc + 3)) s = some s1 := by
    simp only [execute, hg, hp, bind, pure, Option.bind]
    rfl
  have h2 := execute_pure_of ops (layout p) (geometry p) t 0 (pc + 3)
    (.bin .add (.reg 0) (.reg 1)) s1 (ops.add a b)
    (by simp [evalExpr, applyBinary, s1, advance, ha, hb]) (by simp [s1, advance])
  rewrite [scalar_step ops _ _ _ _ _ _ _ _
    (by simp [LarkCollective.parked, hp, hbranch]) (by simpa only [hp] using hbranch) h1]
  rewrite [scalar_step ops _ _ _ _ _ _ _ _
    (by simp [LarkCollective.parked, s1, advance, hadd]) (by simpa [s1, advance] using hadd) h2]
  simp only [guardedAfter, hguard, ↓reduceIte]
  rfl

theorem guarded_false_eq (p : Shape) (ops : Ops α) (t pc lane distance valid extra : Nat)
    (bound : Index) (a b : α) (s : State α) (hl : lane < 64) (hd : distance ≤ 32)
    (hi : s.indices t 2 = some (lane : Int)) (hv : evalIndex (geometry p) t s bound = some (valid : Int))
    (hp : s.pc t = pc + 1)
    (hbranch : program[pc + 1]? = some (.scalar (.branch
      (.lt (.add (.ivar 2) (.const (distance : Int))) bound) (pc + 3))))
    (hguard : ¬ lane + distance < valid) :
    LarkCollective.runLane ops (layout p) (geometry p) program t (extra + 1) s =
      LarkCollective.runLane ops (layout p) (geometry p) program t extra
        (guardedAfter ops t pc lane distance valid a b s) := by
  have hsum := LarkReduction.eval_add_of (geometry p) t s (.ivar 2) (.const (distance : Int))
    (lane : Int) (distance : Int) ((lane + distance : Nat) : Int) hi (int32_cast distance (by omega))
    ((congrArg int32 (Int.natCast_add lane distance).symm).trans (int32_cast _ (by omega)))
  have hg := LarkReduction.predicate_nlt_of (geometry p) t s
    (.add (.ivar 2) (.const (distance : Int))) bound ((lane + distance : Nat) : Int) (valid : Int)
    hsum hv (by omega)
  have h1 : execute ops (layout p) (geometry p) t
      (.branch (.lt (.add (.ivar 2) (.const (distance : Int))) bound) (pc + 3)) s =
      some (advance s t (pc + 3)) := by
    simp only [execute, hg, bind, pure, Option.bind]
    rfl
  rewrite [scalar_step ops _ _ _ _ _ _ _ _
    (by simp [LarkCollective.parked, hp, hbranch]) (by simpa only [hp] using hbranch) h1]
  simp only [guardedAfter, hguard, ↓reduceIte]

theorem guarded_eq (p : Shape) (ops : Ops α) (t pc lane distance valid extra : Nat)
    (bound : Index) (a b : α) (s : State α) (hl : lane < 64) (hd : distance ≤ 32)
    (hi : s.indices t 2 = some (lane : Int)) (hv : evalIndex (geometry p) t s bound = some (valid : Int))
    (ha : s.regs t 0 = some a) (hb : s.regs t 1 = some b) (hp : s.pc t = pc + 1)
    (hbranch : program[pc + 1]? = some (.scalar (.branch
      (.lt (.add (.ivar 2) (.const (distance : Int))) bound) (pc + 3))))
    (hadd : program[pc + 2]? = some (.scalar (.assign 0 (.bin .add (.reg 0) (.reg 1))))) :
    LarkCollective.runLane ops (layout p) (geometry p) program t
      (extra + (if lane + distance < valid then 2 else 1)) s =
      LarkCollective.runLane ops (layout p) (geometry p) program t extra
        (guardedAfter ops t pc lane distance valid a b s) := by
  by_cases h : lane + distance < valid
  · simp only [h, ↓reduceIte]
    exact guarded_true_eq p ops t pc lane distance valid extra bound a b s hl hd hi hv ha hb hp hbranch hadd h
  · simp only [h, ↓reduceIte]
    exact guarded_false_eq p ops t pc lane distance valid extra bound a b s hl hd hi hv hp hbranch h

theorem guarded_preserves (ops : Ops α) (t pc lane distance valid : Nat) (a b : α) (s : State α) :
    (guardedAfter ops t pc lane distance valid a b s).indices = s.indices ∧
    (guardedAfter ops t pc lane distance valid a b s).memory = s.memory ∧
    (guardedAfter ops t pc lane distance valid a b s).epochs = s.epochs ∧
    (guardedAfter ops t pc lane distance valid a b s).trace = s.trace := by
  unfold guardedAfter
  split <;> exact ⟨rfl, rfl, rfl, rfl⟩

theorem guarded_pc (ops : Ops α) (t pc lane distance valid : Nat) (a b : α) (s : State α) :
    (guardedAfter ops t pc lane distance valid a b s).pc t = pc + 3 := by
  unfold guardedAfter
  split <;> simp [setReg, advance]

theorem guarded_acc (ops : Ops α) (t pc lane distance valid : Nat) (a b : α) (s : State α)
    (ha : s.regs t 0 = some a) :
    (guardedAfter ops t pc lane distance valid a b s).regs t 0 =
      some (if lane + distance < valid then ops.add a b else a) := by
  by_cases h : lane + distance < valid <;> simp [guardedAfter, h, setReg, advance, ha]

theorem guarded_other (ops : Ops α) (t u pc lane distance valid : Nat) (a b : α) (s : State α)
    (hu : u ≠ t) :
    (guardedAfter ops t pc lane distance valid a b s).pc u = s.pc u ∧
    (guardedAfter ops t pc lane distance valid a b s).regs u = s.regs u := by
  unfold guardedAfter
  split <;> simp [setReg, advance, hu]

#print axioms guarded_eq
#print axioms guarded_preserves
#print axioms guarded_acc
end LarkNativeRmsNorm
