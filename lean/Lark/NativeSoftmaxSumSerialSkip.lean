import Lark.NativeSoftmaxSumSerialLane

/-! Every nonzero thread takes the source's actual skip branch to PC92.
It retains its registers, memory, epochs and trace; only its PC advances. -/
namespace LarkNativeSoftmax
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def sumSerialSkip (t : Nat) (s : State α) : State α := advance s t 92

theorem sum_serial_skip_run (p : Shape) (guarded : Bool) (ops : Ops α)
    (t tid : Nat) (s : State α) (hn : tid ≠ 0) (hp : s.pc t = 83)
    (hi : s.indices t 1 = some (tid : Int)) :
    LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t fuel.lane s =
      some (sumSerialSkip t s) := by
  have pred : evalPredicate (geometry p) t s (.eq (.ivar 1) (.const 0)) = some false := by
    simp [evalPredicate,evalIndex,hi,int32,show (tid : Int) ≠ 0 by omega]
  have he : execute ops (layout p) (geometry p) t (.branch (.eq (.ivar 1) (.const 0)) 92) s =
      some (sumSerialSkip t s) := by simp [execute,pred,sumSerialSkip]
  rewrite [show fuel.lane=4095+1 by decide,
    scalar_step p guarded ops t 83 4095 _ s _ (by cases guarded <;> decide) hp he]
  have parked : LarkCollective.parked (program guarded) (sumSerialSkip t s) t = some .block := by
    simp only [LarkCollective.parked,sumSerialSkip,advance,↓reduceIte,sum_serial_barrier]
    rfl
  simp only [LarkCollective.runLane,parked]

theorem sum_serial_skip_frames (t : Nat) (s : State α) :
    (sumSerialSkip t s).pc t = 92 ∧ (sumSerialSkip t s).indices = s.indices ∧
    (sumSerialSkip t s).regs = s.regs ∧ (sumSerialSkip t s).memory = s.memory ∧
    (sumSerialSkip t s).epochs = s.epochs ∧ (sumSerialSkip t s).trace = s.trace := by
  simp [sumSerialSkip,advance]

theorem sum_serial_skip_other (t u : Nat) (s : State α) (hu : u ≠ t) :
    (sumSerialSkip t s).pc u = s.pc u := by simp [sumSerialSkip,advance,hu]

#print axioms sum_serial_skip_run
#print axioms sum_serial_skip_frames
#print axioms sum_serial_skip_other
end LarkNativeSoftmax
