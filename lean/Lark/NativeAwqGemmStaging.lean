import Lark.NativeAwqGemmBValues

/-! Actual A-then-B source order for one lane reaches the middle barrier
within the original 512 fuel, with both shared value families retained. -/
namespace LarkNativeAwqGemm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option autoImplicit false
variable {α : Type}
attribute [local irreducible] aLoopState aRoundState aBodyState bChunksState bChunkState bChunkBody bLoopState bRoundState bBodyState

def stagingState (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (tile t : Nat) (s : State α) : State α :=
  bStageState p input tile t (aStageState p ops input tile t s)

def stagingCost (p : Shape) (t : Nat) : Nat := aStageCost p t+bStageCost p

theorem staging_eq (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile t extra : Nat) (s : State α) (hk : tile<p.k/32) (setup : SetupIndices p t s)
    (ki : s.indices t 13=some (tile : Int)) (reads : Reads p input s) (hp : s.pc t=firstBarrier p+1) :
    LarkMFMA.runLane ops (layout p) (geometry p) (program p) t (extra+stagingCost p t) s=
      LarkMFMA.runLane ops (layout p) (geometry p) (program p) t extra (stagingState p ops input tile t s) := by
  let a := aStageState p ops input tile t s
  have ai : AIndices p tile t 8 a := a_stage_indices p ops input tile t s setup ki
  rewrite [show extra+stagingCost p t=(extra+bStageCost p)+aStageCost p t by unfold stagingCost; omega,
    a_stage_eq p ops input tile t (extra+bStageCost p) s hk setup ki reads hp]
  exact b_stage_eq p ops input tile t extra a hk ai.setup ai.k
    (a_stage_reads p ops input tile t s reads) (a_stage_pc p ops input tile t s)

theorem staging_pc (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (tile t : Nat) (s : State α) :
    (stagingState p ops input tile t s).pc t=middleBarrier p := b_stage_pc p input tile t _

theorem staging_indices (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile t : Nat) (s : State α) (setup : SetupIndices p t s) (ki : s.indices t 13=some (tile : Int)) :
    BOuterIndices p tile t (banks p) (stagingState p ops input tile t s) := by
  have ai := a_stage_indices p ops input tile t s setup ki
  exact b_stage_indices p input tile t (aStageState p ops input tile t s) ai.setup ai.k

theorem staging_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (tile t : Nat) (s : State α)
    (reads : Reads p input s) : Reads p input (stagingState p ops input tile t s) :=
  b_stage_reads p input tile t _ (a_stage_reads p ops input tile t s reads)

theorem staging_frames (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (tile t : Nat) (s : State α) :
    (stagingState p ops input tile t s).regs=s.regs ∧ (stagingState p ops input tile t s).epochs=s.epochs := by
  have a := a_stage_frames p ops input tile t s
  have b := b_stage_frames p input tile t (aStageState p ops input tile t s)
  exact ⟨b.1.trans a.1,b.2.trans a.2⟩

theorem staging_a_value (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile t e : Nat) (s : State α) (he : e<8) :
    (stagingState p ops input tile t s).memory (aCell t e)=
      some (if inputRow p t<p.m then input 0 (aSourceOffset p tile t e) else ops.toHalf (ops.literal 0 1)) := by
  have frame := b_stage_memory_outside p input tile t (aStageState p ops input tile t s) (aCell t e)
    (by intro chunk hc q hq same; have impossible := congrArg Location.buffer same; cases impossible)
  exact frame.trans (a_stage_value p ops input tile t e s he)

theorem staging_b_value (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile t chunk e : Nat) (s : State α) (hc : chunk<banks p) (he : e<8) :
    (stagingState p ops input tile t s).memory (bCell p t chunk e)=
      some (input 1 (bSourceOffset p tile t chunk e)) := b_stage_value p input tile t chunk e _ hc he

theorem staging_memory_outside (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile t : Nat) (s : State α) (loc : Location)
    (ha : ∀ e, e<8 → loc≠aCell t e) (hb : ∀ chunk, chunk<banks p → ∀ e, e<8 → loc≠bCell p t chunk e) :
    (stagingState p ops input tile t s).memory loc=s.memory loc :=
  (b_stage_memory_outside p input tile t (aStageState p ops input tile t s) loc hb).trans
    (a_stage_memory_outside p ops input tile t s loc ha)

theorem staging_trace_length (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (tile t : Nat) (s : State α) :
    (stagingState p ops input tile t s).trace.length=
      s.trace.length+(if inputRow p t<p.m then 16 else 8)+16*banks p := by
  rw [stagingState,b_stage_trace_length,a_stage_trace_length]

theorem staging_fuel_bound (p : Shape) (t : Nat) : stagingCost p t<512 := by
  unfold stagingCost aStageCost bStageCost
  rcases banks_cases p with hb | hb <;> rw [hb] <;> split <;> omega

theorem middle_barrier_site (p : Shape) : (program p)[middleBarrier p]?=some blockBarrier := by
  rw [show middleBarrier p=16+4*banks p+22 by unfold middleBarrier; omega,staging_site p 22 (by decide)]
  rfl

theorem staging_run (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile t : Nat) (s : State α) (hk : tile<p.k/32) (setup : SetupIndices p t s)
    (ki : s.indices t 13=some (tile : Int)) (reads : Reads p input s) (hp : s.pc t=firstBarrier p+1) :
    LarkMFMA.runLane ops (layout p) (geometry p) (program p) t (fuel p).lane s=
      some (stagingState p ops input tile t s) := by
  have bound := staging_fuel_bound p t
  have step := staging_eq p ops input tile t (512-stagingCost p t) s hk setup ki reads hp
  rw [show 512-stagingCost p t+stagingCost p t=512 by omega] at step
  change LarkMFMA.runLane ops (layout p) (geometry p) (program p) t 512 s=_
  rw [step]
  exact run_lane_parked p ops t _ _ .block (by omega)
    (by simp only [LarkMFMA.parked,staging_pc,middle_barrier_site,blockBarrier,LarkMFMA.scalarCut])

#print axioms staging_eq
#print axioms staging_pc
#print axioms staging_indices
#print axioms staging_reads
#print axioms staging_frames
#print axioms staging_a_value
#print axioms staging_b_value
#print axioms staging_memory_outside
#print axioms staging_trace_length
#print axioms staging_fuel_bound
#print axioms middle_barrier_site
#print axioms staging_run
end LarkNativeAwqGemm
