import Lark.NativeSoftmaxSumSerialBoundary

/-! Actual thread-zero serial sum: the entry load, all31 components,
false loop exit and final store. The original lane fuel remains4096. -/
namespace LarkNativeSoftmax
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def sumSerialTotal (ops : Ops α) (values : Nat → α) : α := sumSerialFold ops values 1 31 (values 0)

def sumSerialLane (ops : Ops α) (values : Nat → α) (t : Nat) (s : State α) : State α :=
  sumSerialExit t (sumSerialTotal ops values)
    (sumSerialComponents ops values t 1 31 (values 0) (sumSerialBegin values t s))

theorem sum_serial_lane_eq (p : Shape) (guarded : Bool) (ops : Ops α) (values : Nat → α)
    (t extra : Nat) (s : State α) (hp : s.pc t = 83)
    (hi : s.indices t 1 = some 0) (reads : SumSerialReads values t s) :
    LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t (extra+160) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t extra (sumSerialLane ops values t s) := by
  have beginReady := sum_serial_begin_ready ops values t s reads
  have last := sum_serial_components_ready ops values t 1 31 (values 0) (sumSerialBegin values t s) beginReady
  rewrite [show extra+160=((extra+2)+5*31)+3 by omega,
    sum_serial_begin_eq p guarded ops values t ((extra+2)+5*31) s hp hi reads]
  rewrite [sum_serial_components_eq p guarded ops values t 1 31 (extra+2) (values 0) _ (by decide) beginReady]
  exact sum_serial_exit_eq p guarded ops t extra _ _ last.pc last.counter last.accumulator

theorem sum_serial_lane_pc (ops : Ops α) (values : Nat → α) (t : Nat) (s : State α) :
    (sumSerialLane ops values t s).pc t = 92 := (sum_serial_exit_frames t _ _).1

theorem sum_serial_barrier (guarded : Bool) :
    (program guarded)[92]? = some (.scalar (.barrier .block)) := by cases guarded <;> decide

theorem sum_serial_lane_run (p : Shape) (guarded : Bool) (ops : Ops α) (values : Nat → α)
    (t : Nat) (s : State α) (hp : s.pc t = 83) (hi : s.indices t 1 = some 0)
    (reads : SumSerialReads values t s) :
    LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t fuel.lane s =
      some (sumSerialLane ops values t s) := by
  rewrite [show fuel.lane=3936+160 by decide,sum_serial_lane_eq p guarded ops values t 3936 s hp hi reads]
  have parked : LarkCollective.parked (program guarded) (sumSerialLane ops values t s) t = some .block := by
    simp only [LarkCollective.parked,sum_serial_lane_pc,sum_serial_barrier]
    rfl
  simp only [LarkCollective.runLane,parked]

theorem sum_serial_lane_value (ops : Ops α) (values : Nat → α) (t : Nat) (s : State α) :
    (sumSerialLane ops values t s).memory (sumPartialCell t 0) = some (sumSerialTotal ops values) :=
  sum_serial_exit_value t _ _

theorem sum_serial_lane_epochs (ops : Ops α) (values : Nat → α) (t : Nat) (s : State α) :
    (sumSerialLane ops values t s).epochs = s.epochs :=
  (sum_serial_exit_frames t _ _).2.2.2.1.trans
    ((sum_serial_components_frames ops values t 1 31 (values 0) (sumSerialBegin values t s)).2.1.trans
      (sum_serial_begin_frames values t s).2.1)

theorem sum_serial_lane_memory_other (ops : Ops α) (values : Nat → α) (t : Nat) (s : State α)
    (l : Location) (hl : l ≠ sumPartialCell t 0) :
    (sumSerialLane ops values t s).memory l = s.memory l :=
  (sum_serial_exit_memory_other t _ _ l hl).trans
    ((congrFun (sum_serial_components_frames ops values t 1 31 (values 0) (sumSerialBegin values t s)).1 l).trans
      (congrFun (sum_serial_begin_frames values t s).1 l))

theorem sum_serial_lane_trace_length (ops : Ops α) (values : Nat → α) (t : Nat) (s : State α) :
    (sumSerialLane ops values t s).trace.length = s.trace.length+33 := by
  have beginFrame := sum_serial_begin_frames values t s
  have loopFrame := sum_serial_components_frames ops values t 1 31 (values 0) (sumSerialBegin values t s)
  have endFrame := (sum_serial_exit_frames t (sumSerialTotal ops values)
    (sumSerialComponents ops values t 1 31 (values 0) (sumSerialBegin values t s))).2.2.2.2
  exact endFrame.trans (by rewrite [loopFrame.2.2,beginFrame.2.2]; omega)

theorem sum_serial_lane_good (ops : Ops α) (values : Nat → α) (t : Nat) (s : State α)
    (ht : t%1024=0) (he : (s.epochs t).block=3) (good : ∀ a ∈ s.trace, Good a) :
    ∀ a ∈ (sumSerialLane ops values t s).trace, Good a := by
  have beginEpoch : ((sumSerialBegin values t s).epochs t).block=3 :=
    (congrArg (fun epochs => (epochs t).block) (sum_serial_begin_frames values t s).2.1).trans he
  have loopEpoch : ((sumSerialComponents ops values t 1 31 (values 0) (sumSerialBegin values t s)).epochs t).block=3 :=
    (congrArg (fun epochs => (epochs t).block)
      (sum_serial_components_frames ops values t 1 31 (values 0) (sumSerialBegin values t s)).2.1).trans beginEpoch
  exact sum_serial_exit_good t _ _ ht loopEpoch
    (sum_serial_components_good ops values t 1 31 (values 0) (sumSerialBegin values t s) ht beginEpoch
      (sum_serial_begin_good values t s ht he good))

theorem sum_mid_serial_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row : Nat)
    (s : State α) (ready : ExpMidReady p ops input row s) :
    SumSerialReads (expBlockPartial ops input row) (row*1024) s := by
  intro slot hs
  change s.memory ⟨.shared,(row*1024)/1024,1,slot⟩ = _
  rewrite [show row*1024/1024=row by omega]
  exact ready.partials slot hs

theorem sum_serial_mid_lane_run (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) (ready : ExpMidReady p ops input row s) :
    LarkCollective.runLane ops (layout p) (geometry p) (program guarded) (row*1024) fuel.lane s =
      some (sumSerialLane ops (expBlockPartial ops input row) (row*1024) s) := by
  apply sum_serial_lane_run p guarded ops (expBlockPartial ops input row) (row*1024) s
  · simpa only [Nat.add_zero] using ready.pc 0 (by decide)
  · simpa using (ready.indices 0 (by decide)).2.1
  · exact sum_mid_serial_reads p ops input row s ready


theorem sum_serial_mid_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row : Nat)
    (s : State α) (ready : ExpMidReady p ops input row s) :
    ∀ a ∈ (sumSerialLane ops (expBlockPartial ops input row) (row*1024) s).trace, Good a := by
  apply sum_serial_lane_good ops (expBlockPartial ops input row) (row*1024) s (by omega)
  · simpa only [Nat.add_zero] using ready.epoch 0 (by decide)
  · exact ready.good


#print axioms sum_mid_serial_reads
#print axioms sum_serial_mid_lane_run
#print axioms sum_serial_mid_good
#print axioms sum_serial_lane_eq
#print axioms sum_serial_lane_pc
#print axioms sum_serial_barrier
#print axioms sum_serial_lane_run
#print axioms sum_serial_lane_value
#print axioms sum_serial_lane_epochs
#print axioms sum_serial_lane_memory_other
#print axioms sum_serial_lane_trace_length
#print axioms sum_serial_lane_good
end LarkNativeSoftmax
