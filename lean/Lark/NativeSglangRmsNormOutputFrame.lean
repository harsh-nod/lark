import Lark.NativeSglangRmsNormOutputLane

/-! Output execution preserves every other thread's control/register/index
state, all shared inverses, every other private cache, read-only globals and
previous global outputs owned by other threads. This permits the real native
sequential lane/wave/block folds without assuming an initial trace is safe.
-/
namespace LarkNativeSglangRmsNorm
open LarkNonlinear
open LarkReduction (setIndex setReg)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
attribute [local irreducible] scalePairs scaleRounds outputCopies

theorem scale_pairs_other (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t pair remaining u : Nat) (inverse : α) (s : State α) (hu : u≠t) :
    (scalePairs ops input row tid iteration t inverse pair remaining s).pc u=s.pc u ∧
    (scalePairs ops input row tid iteration t inverse pair remaining s).indices u=s.indices u ∧
    (scalePairs ops input row tid iteration t inverse pair remaining s).regs u=s.regs u := by
  induction remaining generalizing pair s with
  | zero => rw [scalePairs]; exact ⟨rfl,rfl,rfl⟩
  | succ remaining ih =>
      rw [scalePairs]
      have h := ih (pair+1) (scalePairAfter ops input row tid iteration pair t inverse s)
      have hs := scale_pair_other ops input row tid iteration pair t u inverse s hu
      exact ⟨h.1.trans hs.1,h.2.1.trans hs.2.1,h.2.2.trans hs.2.2⟩

theorem scale_round_other (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t u : Nat) (inverse : α) (s : State α) (hu : u≠t) :
    (scaleRoundAfter ops input row tid iteration t inverse s).pc u=s.pc u ∧
    (scaleRoundAfter ops input row tid iteration t inverse s).indices u=s.indices u ∧
    (scaleRoundAfter ops input row tid iteration t inverse s).regs u=s.regs u := by
  have h := scale_pairs_other ops input row tid iteration t 0 4 u inverse (scaleRoundBegin t s) hu
  simpa [scaleRoundAfter,scaleRoundEnd,scaleRoundBegin,setIndex,advance,hu] using h

theorem scale_rounds_other (ops : Ops α) (input : Nat → Nat → α)
    (row tid t iteration remaining u : Nat) (inverse : α) (s : State α) (hu : u≠t) :
    (scaleRounds ops input row tid t inverse iteration remaining s).pc u=s.pc u ∧
    (scaleRounds ops input row tid t inverse iteration remaining s).indices u=s.indices u ∧
    (scaleRounds ops input row tid t inverse iteration remaining s).regs u=s.regs u := by
  induction remaining generalizing iteration s with
  | zero => rw [scaleRounds]; exact ⟨rfl,rfl,rfl⟩
  | succ remaining ih =>
      rw [scaleRounds]
      have h := ih (iteration+1) (scaleRoundAfter ops input row tid iteration t inverse s)
      have hs := scale_round_other ops input row tid iteration t u inverse s hu
      exact ⟨h.1.trans hs.1,h.2.1.trans hs.2.1,h.2.2.trans hs.2.2⟩

theorem scaled_lane_other (ops : Ops α) (input : Nat → Nat → α)
    (row tid t u : Nat) (inverse : α) (s : State α) (hu : u≠t) :
    (scaledLane ops input row tid t inverse s).pc u=s.pc u ∧
    (scaledLane ops input row tid t inverse s).indices u=s.indices u ∧
    (scaledLane ops input row tid t inverse s).regs u=s.regs u := by
  have h := scale_rounds_other ops input row tid t 0 2 u inverse (outputScaleStart t (tid/32) inverse s) hu
  simpa [scaledLane,outputScaleStart,setReg,setIndex,advance,record,hu] using h

theorem output_copies_other (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t component remaining u : Nat) (inverse : α) (s : State α) (hu : u≠t) :
    (outputCopies ops input row tid iteration t inverse component remaining s).pc u=s.pc u ∧
    (outputCopies ops input row tid iteration t inverse component remaining s).indices u=s.indices u ∧
    (outputCopies ops input row tid iteration t inverse component remaining s).regs u=s.regs u := by
  induction remaining generalizing component s with
  | zero => rw [outputCopies]; exact ⟨rfl,rfl,rfl⟩
  | succ remaining ih =>
      rw [outputCopies]
      have h := ih (component+1) (outputCopyAfter ops input row tid iteration component t inverse s)
      have hs := output_copy_other ops input row tid iteration component t u inverse s hu
      have hr := congrFun (output_copy_fields ops input row tid iteration component t inverse s).2.2.2.2.2.1 u
      exact ⟨h.1.trans hs.1,h.2.1.trans hs.2,h.2.2.trans hr⟩

theorem copy_round_other (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t u : Nat) (inverse : α) (s : State α) (hu : u≠t) :
    (copyRoundAfter ops input row tid iteration t inverse s).pc u=s.pc u ∧
    (copyRoundAfter ops input row tid iteration t inverse s).indices u=s.indices u ∧
    (copyRoundAfter ops input row tid iteration t inverse s).regs u=s.regs u := by
  have h := output_copies_other ops input row tid iteration t 0 8 u inverse (copyRoundBegin t s) hu
  simpa [copyRoundAfter,copyRoundEnd,copyRoundBegin,setIndex,advance,hu] using h

theorem copied_lane_other (ops : Ops α) (input : Nat → Nat → α)
    (row tid t u : Nat) (inverse : α) (s : State α) (hu : u≠t) :
    (copiedLane ops input row tid t inverse s).pc u=s.pc u ∧
    (copiedLane ops input row tid t inverse s).indices u=s.indices u ∧
    (copiedLane ops input row tid t inverse s).regs u=s.regs u := by
  have h0 := copy_round_other ops input row tid 0 t u inverse (copyStart t s) hu
  have h1 := copy_round_other ops input row tid 1 t u inverse (copyRoundAfter ops input row tid 0 t inverse (copyStart t s)) hu
  have h := And.intro (h1.1.trans h0.1) (And.intro (h1.2.1.trans h0.2.1) (h1.2.2.trans h0.2.2))
  simpa [copiedLane,copyTwoRounds,copyStart,setIndex,advance,hu] using h

theorem output_lane_other (ops : Ops α) (input : Nat → Nat → α)
    (row tid t u : Nat) (inverse : α) (s : State α) (hu : u≠t) :
    (outputLane ops input row tid t inverse s).pc u=s.pc u ∧
    (outputLane ops input row tid t inverse s).indices u=s.indices u ∧
    (outputLane ops input row tid t inverse s).regs u=s.regs u := by
  have h := copied_lane_other ops input row tid t u inverse (scaledLane ops input row tid t inverse s) hu
  have hs := scaled_lane_other ops input row tid t u inverse s hu
  exact ⟨h.1.trans hs.1,h.2.1.trans hs.2.1,h.2.2.trans hs.2.2⟩

theorem output_lane_other_private (ops : Ops α) (input : Nat → Nat → α)
    (row tid t u buffer slot : Nat) (inverse : α) (s : State α) (hu : u≠t) :
    (outputLane ops input row tid t inverse s).memory (privateCell u buffer slot)=s.memory (privateCell u buffer slot) := by
  apply output_lane_memory_outside
  · exact Or.inr (Or.inl hu)
  · intro iteration _ component _
    simp [privateCell,globalCell]

theorem output_lane_shared (ops : Ops α) (input : Nat → Nat → α)
    (row tid t : Nat) (inverse : α) (s : State α) (l : Location) (hl : l.space=.shared) :
    (outputLane ops input row tid t inverse s).memory l=s.memory l := by
  apply output_lane_memory_outside
  · exact Or.inl (by rw [hl]; decide)
  · intro iteration _ component _ he
    have hs := congrArg Location.space he
    simp only [globalCell,hl] at hs
    cases hs

theorem output_lane_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid t : Nat) (inverse : α) (s : State α) (reads : Reads p input s) :
    Reads p input (outputLane ops input row tid t inverse s) := by
  constructor
  · intro offset ho
    rw [output_lane_memory_outside ops input row tid t inverse s (globalCell 1 offset)
      (by simp [OutsideOutput,globalCell]) (by intro iteration _ component _; simp [globalCell])]
    exact reads.1 offset ho
  · intro offset ho
    rw [output_lane_memory_outside ops input row tid t inverse s (globalCell 2 offset)
      (by simp [OutsideOutput,globalCell]) (by intro iteration _ component _; simp [globalCell])]
    exact reads.2 offset ho

theorem output_lane_previous_output (ops : Ops α) (input : Nat → Nat → α)
    (row tid t offset : Nat) (inverse : α) (s : State α) (ht : tid<1024) (he : t=row*1024+tid)
    (owner : writer offset≠t) :
    (outputLane ops input row tid t inverse s).memory (globalCell 0 offset)=s.memory (globalCell 0 offset) := by
  apply output_lane_memory_outside
  · simp [OutsideOutput,globalCell]
  · intro iteration hi component hc hloc
    have hoff := congrArg Location.offset hloc
    change offset=address row (column tid iteration component) at hoff
    apply owner
    rw [hoff,address_writer row tid iteration component ht hi hc]
    exact he.symm

#print axioms scale_pairs_other
#print axioms scale_round_other
#print axioms scale_rounds_other
#print axioms scaled_lane_other
#print axioms output_copies_other
#print axioms copy_round_other
#print axioms copied_lane_other
#print axioms output_lane_other
#print axioms output_lane_other_private
#print axioms output_lane_shared
#print axioms output_lane_reads
#print axioms output_lane_previous_output
end LarkNativeSglangRmsNorm
