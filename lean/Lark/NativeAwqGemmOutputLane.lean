import Lark.NativeAwqGemmOutputLoop

/-! Every output pair executes under the original scalar budget and parks at
the actual halt. The K-control continuation uses the remaining original fuel. -/
namespace LarkNativeAwqGemm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option autoImplicit false
variable {α : Type}
attribute [local irreducible] outputRound outputStored outputLoop

def outputLane (p : Shape) (ops : Ops α) (t : Nat) (values : Nat → α) (s : State α) : State α :=
  outputLoop p ops t values 0 (4*banks p) s

theorem output_lane_pc (p : Shape) (ops : Ops α) (t : Nat) (values : Nat → α) (s : State α)
    (hp : s.pc t=outputPC p) : (outputLane p ops t values s).pc t=haltPC p := by
  have pc := output_loop_pc p ops t 0 (4*banks p) values s hp
  have halt : outPC p (0+4*banks p)=haltPC p := by unfold outPC outputPC haltPC; omega
  exact pc.trans halt

theorem output_lane_steps (p : Shape) (t : Nat) : outputSteps p t 0 (4*banks p)≤64 := by
  have h := output_steps_bound p t 0 (4*banks p)
  rcases banks_cases p with b | b <;> omega

theorem output_lane_run (p : Shape) (ops : Ops α) (t budget : Nat) (values : Nat → α) (s : State α)
    (enough : outputSteps p t 0 (4*banks p)<budget) (setup : SetupIndices p t s)
    (hr : ∀ q, q<4*banks p → s.regs t q=some (values q)) (hp : s.pc t=outputPC p) :
    LarkMFMA.runLane ops (layout p) (geometry p) (program p) t budget s=some (outputLane p ops t values s) := by
  rw [show budget=(budget-outputSteps p t 0 (4*banks p))+outputSteps p t 0 (4*banks p) by omega,
    output_loop_eq p ops t 0 (4*banks p) (budget-outputSteps p t 0 (4*banks p)) values s (by omega) setup
      (fun q _ hq => hr q (by omega)) hp]
  exact run_lane_parked p ops t _ _ .halt (by omega)
    (by simp only [LarkMFMA.parked,show outputLoop p ops t values 0 (4*banks p) s=outputLane p ops t values s from rfl,
      output_lane_pc p ops t values s hp,output_halt_site])

def tailLane (p : Shape) (ops : Ops α) (tile t : Nat) (values : Nat → α) (s : State α) : State α :=
  if tile+1<p.k/32 then kControlState p tile t s
  else outputLane p ops t values (kControlState p tile t s)

theorem tail_lane_pc (p : Shape) (ops : Ops α) (tile t : Nat) (values : Nat → α) (s : State α) :
    (tailLane p ops tile t values s).pc t=if tile+1<p.k/32 then firstBarrier p else haltPC p := by
  unfold tailLane
  split
  · rename_i more
    simpa only [if_pos more] using k_control_pc p tile t s
  · rename_i last
    rw [output_lane_pc p ops t values _ (by rw [k_control_pc,if_neg last])]

theorem tail_lane_frames (p : Shape) (ops : Ops α) (tile t : Nat) (values : Nat → α) (s : State α) :
    (tailLane p ops tile t values s).indices=(kControlState p tile t s).indices ∧
      (tailLane p ops tile t values s).regs=s.regs ∧ (tailLane p ops tile t values s).epochs=s.epochs := by
  unfold tailLane
  split
  · exact ⟨rfl,rfl,rfl⟩
  · exact output_loop_frames p ops t 0 (4*banks p) values _

theorem tail_lane_setup (p : Shape) (ops : Ops α) (tile t : Nat) (values : Nat → α) (s : State α)
    (setup : SetupIndices p t s) : SetupIndices p t (tailLane p ops tile t values s) :=
  setup_of_indices p t (kControlState p tile t s) _ (k_control_setup p tile t s setup)
    (tail_lane_frames p ops tile t values s).1

theorem tail_lane_index (p : Shape) (ops : Ops α) (tile t : Nat) (values : Nat → α) (s : State α) :
    (tailLane p ops tile t values s).indices t 13=some ((tile+1 : Nat) : Int) := by
  rw [(tail_lane_frames p ops tile t values s).1,k_control_index]

theorem tail_lane_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile t : Nat) (values : Nat → α) (s : State α) (reads : Reads p input s) :
    Reads p input (tailLane p ops tile t values s) := by
  unfold tailLane
  split
  · exact reads
  · exact output_loop_reads p ops input t 0 (4*banks p) values _ reads

theorem tail_lane_other_pc (p : Shape) (ops : Ops α) (tile t u : Nat) (values : Nat → α)
    (s : State α) (hu : u≠t) : (tailLane p ops tile t values s).pc u=s.pc u := by
  unfold tailLane
  split
  · exact (k_control_other p tile t u s hu).1
  · exact (output_loop_other_pc p ops t 0 (4*banks p) u values _ hu).trans (k_control_other p tile t u s hu).1

theorem tail_lane_other_indices (p : Shape) (ops : Ops α) (tile t u : Nat) (values : Nat → α)
    (s : State α) (hu : u≠t) : (tailLane p ops tile t values s).indices u=s.indices u := by
  rw [(tail_lane_frames p ops tile t values s).1]
  exact (k_control_other p tile t u s hu).2

theorem tail_lane_run (p : Shape) (ops : Ops α) (tile t : Nat) (values : Nat → α) (s : State α)
    (hk : tile<p.k/32) (hi : s.indices t 13=some (tile : Int)) (hp : s.pc t=kTailPC p)
    (setup : SetupIndices p t s) (hr : ∀ q, q<4*banks p → s.regs t q=some (values q)) :
    LarkMFMA.runLane ops (layout p) (geometry p) (program p) t (fuel p).lane s=
      some (tailLane p ops tile t values s) := by
  by_cases more : tile+1<p.k/32
  · rw [tailLane,if_pos more]
    exact k_control_run_more p ops tile t s more hi hp
  · rw [tailLane,if_neg more]
    change LarkMFMA.runLane ops (layout p) (geometry p) (program p) t 512 s=_
    rw [show (512 : Nat)=509+3 by decide,k_control_eq p ops tile t 509 s hk hi hp]
    exact output_lane_run p ops t 509 values _ (by have h := output_lane_steps p t; omega)
      (k_control_setup p tile t s setup) hr (by rw [k_control_pc,if_neg more])

#print axioms output_lane_pc
#print axioms output_lane_steps
#print axioms output_lane_run
#print axioms tail_lane_pc
#print axioms tail_lane_frames
#print axioms tail_lane_setup
#print axioms tail_lane_index
#print axioms tail_lane_reads
#print axioms tail_lane_other_pc
#print axioms tail_lane_other_indices
#print axioms tail_lane_run
end LarkNativeAwqGemm
