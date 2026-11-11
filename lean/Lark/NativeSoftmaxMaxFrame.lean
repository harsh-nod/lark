import Lark.NativeSoftmaxMaxPrefixCost

/-! Thread-local frames needed to assemble the actual native maximum wave.
No scheduler, shuffle or whole-wave result is asserted by this module. -/
namespace LarkNativeSoftmax
open LarkNonlinear
open LarkReduction (setIndex setReg)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def OtherThread (_t u : Nat) (before after : State α) : Prop :=
  after.pc u = before.pc u ∧ after.indices u = before.indices u ∧ after.regs u = before.regs u

theorem other_thread_trans (t u : Nat) (a b c : State α)
    (hab : OtherThread t u a b) (hbc : OtherThread t u b c) : OtherThread t u a c :=
  ⟨hbc.1.trans hab.1,hbc.2.1.trans hab.2.1,hbc.2.2.trans hab.2.2⟩

theorem initialized_other (ops : Ops α) (t u : Nat) (s : State α) (hu : u ≠ t) :
    OtherThread t u s (initialized ops t s) := by
  constructor
  · simp [initialized,indexedAt,setIndex,setReg,advance,hu]
  constructor <;> funext r <;> simp [initialized,indexedAt,setIndex,setReg,advance,hu]

theorem max_component_other (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component t u : Nat) (acc : α) (s : State α) (hu : u ≠ t) :
    OtherThread t u s (maxComponentAfter ops input row tid iteration component t acc s) := by
  by_cases hc : 50257 ≤ column tid iteration component
  all_goals
    constructor
    · simp [maxComponentAfter,clampedState,hc,setIndex,setReg,advance,record,hu]
    constructor <;> funext r <;>
      simp [maxComponentAfter,clampedState,hc,setIndex,setReg,advance,record,hu]

theorem max_components_other (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t component count u : Nat) (acc : α) (s : State α) (hu : u ≠ t) :
    OtherThread t u s (maxComponents ops input row tid iteration t component count acc s) := by
  induction count generalizing component acc s with
  | zero => exact ⟨rfl,rfl,rfl⟩
  | succ count ih =>
    exact other_thread_trans t u _ _ _
      (max_component_other ops input row tid iteration component t u acc s hu)
      (ih (component+1) _ _)

theorem max_begin_other (t u : Nat) (s : State α) (hu : u ≠ t) :
    OtherThread t u s (maxBeginRound t s) := by
  constructor
  · simp [maxBeginRound,setIndex,advance,hu]
  exact ⟨by funext r; simp [maxBeginRound,setIndex,advance,hu],rfl⟩

theorem max_end_other (t u tid iteration : Nat) (s : State α) (hu : u ≠ t) :
    OtherThread t u s (maxEndRound t tid iteration s) := by
  constructor
  · simp [maxEndRound,setIndex,advance,hu]
  exact ⟨by funext r; simp [maxEndRound,setIndex,advance,hu],rfl⟩

theorem max_round_other (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t u : Nat) (acc : α) (s : State α) (hu : u ≠ t) :
    OtherThread t u s (maxRoundAfter ops input row tid iteration t acc s) :=
  other_thread_trans t u _ _ _ (max_begin_other t u s hu)
    (other_thread_trans t u _ _ _
      (max_components_other ops input row tid iteration t 0 8 u acc (maxBeginRound t s) hu)
      (max_end_other t u tid iteration _ hu))

theorem max_rounds_other (ops : Ops α) (input : Nat → Nat → α)
    (row tid t iteration count u : Nat) (acc : α) (s : State α) (hu : u ≠ t) :
    OtherThread t u s (maxRounds ops input row tid t iteration count acc s) := by
  induction count generalizing iteration acc s with
  | zero => exact ⟨rfl,rfl,rfl⟩
  | succ count ih =>
    exact other_thread_trans t u _ _ _ (max_round_other ops input row tid iteration t u acc s hu)
      (ih (iteration+1) _ _)

theorem max_exit_other (ops : Ops α) (t u : Nat) (s : State α) (hu : u ≠ t) :
    OtherThread t u s (maxExit ops t s) := by
  constructor
  · simp [maxExit,setReg,advance,hu]
  exact ⟨rfl,by funext r; simp [maxExit,setReg,advance,hu]⟩

theorem max_prefix_other (ops : Ops α) (input : Nat → Nat → α)
    (t u : Nat) (s : State α) (hu : u ≠ t) : OtherThread t u s (maxPrefixState ops input t s) :=
  other_thread_trans t u _ _ _ (initialized_other ops t u s hu)
    (other_thread_trans t u _ _ _
      (max_rounds_other ops input (t/1024) (t%1024) t 0 7 u _ (initialized ops t s) hu)
      (max_exit_other ops t u _ hu))

theorem max_exit_indices (ops : Ops α) (t : Nat) (s : State α) : (maxExit ops t s).indices = s.indices := rfl

theorem max_prefix_native_indices (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) :
    (maxPrefixState ops input t s).indices t 0 = some ((t/1024 : Nat) : Int) ∧
    (maxPrefixState ops input t s).indices t 1 = some ((t%1024 : Nat) : Int) ∧
    (maxPrefixState ops input t s).indices t 2 = some (((t%1024)/32 : Nat) : Int) ∧
    (maxPrefixState ops input t s).indices t 3 = some (((t%1024)%32 : Nat) : Int) := by
  have frame (r : Nat) (hr : r < 4) :
      (maxPassState ops input t s).indices t r = (initialized ops t s).indices t r :=
    max_rounds_index_other ops input (t/1024) (t%1024) t 0 7 r _ _
      (by omega) (by omega) (by omega) (by omega)
  obtain ⟨_,h0,h1,h2,h3,_,_⟩ := initialized_fields ops t s
  unfold maxPrefixState
  rewrite [max_exit_indices]
  exact ⟨(frame 0 (by decide)).trans h0,(frame 1 (by decide)).trans h1,
    (frame 2 (by decide)).trans h2,(frame 3 (by decide)).trans h3⟩

#print axioms other_thread_trans
#print axioms initialized_other
#print axioms max_component_other
#print axioms max_components_other
#print axioms max_begin_other
#print axioms max_end_other
#print axioms max_round_other
#print axioms max_rounds_other
#print axioms max_exit_other
#print axioms max_prefix_other
#print axioms max_exit_indices
#print axioms max_prefix_native_indices
end LarkNativeSoftmax
