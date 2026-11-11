import Lark.NativeSoftmaxSerialLane

/-! Every nonzero thread takes the source's actual skip branch to PC42.
It retains its registers, memory, epochs and trace; only its PC advances. -/
namespace LarkNativeSoftmax
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def serialSkip (t : Nat) (s : State α) : State α := advance s t 42

theorem serial_skip_run (p : Shape) (guarded : Bool) (ops : Ops α)
    (t tid : Nat) (s : State α) (hn : tid ≠ 0) (hp : s.pc t = 33)
    (hi : s.indices t 1 = some (tid : Int)) :
    LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t fuel.lane s =
      some (serialSkip t s) := by
  have pred : evalPredicate (geometry p) t s (.eq (.ivar 1) (.const 0)) = some false := by
    simp [evalPredicate,evalIndex,hi,int32,show (tid : Int) ≠ 0 by omega]
  have he : execute ops (layout p) (geometry p) t (.branch (.eq (.ivar 1) (.const 0)) 42) s =
      some (serialSkip t s) := by simp [execute,pred,serialSkip]
  rewrite [show fuel.lane=4095+1 by decide,
    scalar_step p guarded ops t 33 4095 _ s _ (by cases guarded <;> decide) hp he]
  have parked : LarkCollective.parked (program guarded) (serialSkip t s) t = some .block := by
    simp only [LarkCollective.parked,serialSkip,advance,↓reduceIte,serial_barrier]
    rfl
  simp only [LarkCollective.runLane,parked]

theorem serial_skip_frames (t : Nat) (s : State α) :
    (serialSkip t s).pc t = 42 ∧ (serialSkip t s).indices = s.indices ∧
    (serialSkip t s).regs = s.regs ∧ (serialSkip t s).memory = s.memory ∧
    (serialSkip t s).epochs = s.epochs ∧ (serialSkip t s).trace = s.trace := by
  simp [serialSkip,advance]

theorem serial_skip_other (t u : Nat) (s : State α) (hu : u ≠ t) :
    (serialSkip t s).pc u = s.pc u := by simp [serialSkip,advance,hu]

#print axioms serial_skip_run
#print axioms serial_skip_frames
#print axioms serial_skip_other
end LarkNativeSoftmax
