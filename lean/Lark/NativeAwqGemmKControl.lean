import Lark.NativeAwqGemmTailProgram

/-! Actual K increment, back edge and uniform loop test after both matrix
passes. The tail preserves memory, registers, trace and ordering epochs. -/
namespace LarkNativeAwqGemm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option autoImplicit false
variable {α : Type}

def kIncremented (p : Shape) (tile t : Nat) (s : State α) : State α :=
  setIndex s t 13 ((tile+1 : Nat) : Int) (kTailPC p+1)
def kJumped (p : Shape) (tile t : Nat) (s : State α) : State α :=
  advance (kIncremented p tile t s) t (whilePC p)
def kControlState (p : Shape) (tile t : Nat) (s : State α) : State α :=
  advance (kJumped p tile t s) t (if tile+1<p.k/32 then firstBarrier p else outputPC p)

theorem k_total_signed (p : Shape) : p.k/32<2147483648 := by
  have bound := (scalar_parameter_bounds p).2.1
  omega

theorem k_control_eq (p : Shape) (ops : Ops α) (tile t extra : Nat) (s : State α)
    (hk : tile<p.k/32) (hi : s.indices t 13=some (tile : Int)) (hp : s.pc t=kTailPC p) :
    LarkMFMA.runLane ops (layout p) (geometry p) (program p) t (extra+3) s=
      LarkMFMA.runLane ops (layout p) (geometry p) (program p) t extra (kControlState p tile t s) := by
  have bound := k_total_signed p
  have incrementIndex := eval_nat_add (geometry p) t tile 1 s (v 13) (c 1) hi
    (eval_nat_const _ _ _ _ (by decide)) (by omega)
  have incrementStep := execute_index_of ops p t 13 (kTailPC p+1) (.add (v 13) (c 1)) s
    ((tile+1 : Nat) : Int) incrementIndex (by omega)
  have incrementPC : (kIncremented p tile t s).pc t=kTailPC p+1 := by simp [kIncremented,setIndex,advance]
  have jumpedPC : (kJumped p tile t s).pc t=whilePC p := by simp [kJumped,advance]
  have jumpedIndex : (kJumped p tile t s).indices t 13=some ((tile+1 : Nat) : Int) := by
    simp [kJumped,kIncremented,setIndex,advance]
  have branchStep : execute ops (layout p) (geometry p) t
      (.branch (.lt (v 13) (c (p.k/32))) (outputPC p)) (kJumped p tile t s)=some (kControlState p tile t s) := by
    by_cases more : tile+1<p.k/32
    · have pred := eval_int_lt_true (geometry p) t (kJumped p tile t s) (v 13) (c (p.k/32))
        ((tile+1 : Nat) : Int) ((p.k/32 : Nat) : Int) jumpedIndex (eval_nat_const _ _ _ _ bound) (by omega)
      have step := execute_branch_true ops p t (outputPC p) (.lt (v 13) (c (p.k/32))) (kJumped p tile t s) pred
      rw [jumpedPC] at step
      simpa only [kControlState,if_pos more,show whilePC p+1=firstBarrier p by unfold whilePC firstBarrier; omega] using step
    · have pred := eval_int_lt_false (geometry p) t (kJumped p tile t s) (v 13) (c (p.k/32))
        ((tile+1 : Nat) : Int) ((p.k/32 : Nat) : Int) jumpedIndex (eval_nat_const _ _ _ _ bound) (by omega)
      simpa only [kControlState,if_neg more] using
        execute_branch_false ops p t (outputPC p) (.lt (v 13) (c (p.k/32))) (kJumped p tile t s) pred
  rewrite [show extra+3=(extra+2)+1 by omega,
    scalar_step p ops t (kTailPC p) (extra+2) _ s (kIncremented p tile t s) (k_increment_site p) hp incrementStep]
  rewrite [show extra+2=(extra+1)+1 by omega,
    scalar_step p ops t (kTailPC p+1) (extra+1) _ (kIncremented p tile t s) (kJumped p tile t s)
      (k_back_edge_site p) incrementPC (execute_jump ops p t (whilePC p) (kIncremented p tile t s))]
  exact scalar_step p ops t (whilePC p) extra _ (kJumped p tile t s) _ (initial_while_site p) jumpedPC branchStep

theorem k_control_pc (p : Shape) (tile t : Nat) (s : State α) :
    (kControlState p tile t s).pc t=if tile+1<p.k/32 then firstBarrier p else outputPC p := by
  simp [kControlState,advance]

theorem k_control_index (p : Shape) (tile t : Nat) (s : State α) :
    (kControlState p tile t s).indices t 13=some ((tile+1 : Nat) : Int) := by
  simp [kControlState,kJumped,kIncremented,setIndex,advance]

theorem k_control_setup (p : Shape) (tile t : Nat) (s : State α) (h : SetupIndices p t s) :
    SetupIndices p t (kControlState p tile t s) :=
  setup_of_indices p t (kIncremented p tile t s) _
    (setIndex_setup p t 13 (kTailPC p+1) ((tile+1 : Nat) : Int) s h (by decide)) rfl

theorem k_control_frames (p : Shape) (tile t : Nat) (s : State α) :
    (kControlState p tile t s).memory=s.memory ∧ (kControlState p tile t s).regs=s.regs ∧
      (kControlState p tile t s).trace=s.trace ∧ (kControlState p tile t s).epochs=s.epochs := ⟨rfl,rfl,rfl,rfl⟩

theorem k_control_other (p : Shape) (tile t u : Nat) (s : State α) (hu : u≠t) :
    (kControlState p tile t s).pc u=s.pc u ∧ (kControlState p tile t s).indices u=s.indices u := by
  constructor
  · simp [kControlState,kJumped,kIncremented,setIndex,advance,hu]
  · funext r
    simp [kControlState,kJumped,kIncremented,setIndex,advance,hu]

theorem k_control_run_more (p : Shape) (ops : Ops α) (tile t : Nat) (s : State α)
    (more : tile+1<p.k/32) (hi : s.indices t 13=some (tile : Int)) (hp : s.pc t=kTailPC p) :
    LarkMFMA.runLane ops (layout p) (geometry p) (program p) t (fuel p).lane s=some (kControlState p tile t s) := by
  change LarkMFMA.runLane ops (layout p) (geometry p) (program p) t 512 s=_
  rw [show (512 : Nat)=509+3 by decide,k_control_eq p ops tile t 509 s (by omega) hi hp]
  exact run_lane_parked p ops t 509 _ .block (by decide)
    (by simp only [LarkMFMA.parked,k_control_pc,if_pos more,first_barrier_site,blockBarrier,LarkMFMA.scalarCut])

#print axioms k_total_signed
#print axioms k_control_eq
#print axioms k_control_pc
#print axioms k_control_index
#print axioms k_control_setup
#print axioms k_control_frames
#print axioms k_control_other
#print axioms k_control_run_more
end LarkNativeAwqGemm
