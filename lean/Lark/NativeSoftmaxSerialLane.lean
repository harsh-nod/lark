import Lark.NativeSoftmaxSerialBoundary

/-! Actual thread-zero serial maximum: the entry load, all31 components,
false loop exit and final store. The original lane fuel remains4096. -/
namespace LarkNativeSoftmax
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def serialMaximum (ops : Ops α) (values : Nat → α) : α := serialFold ops values 1 31 (values 0)

def serialLane (ops : Ops α) (values : Nat → α) (t : Nat) (s : State α) : State α :=
  serialExit t (serialMaximum ops values)
    (serialComponents ops values t 1 31 (values 0) (serialBegin values t s))

theorem serial_lane_eq (p : Shape) (guarded : Bool) (ops : Ops α) (values : Nat → α)
    (t extra : Nat) (s : State α) (hp : s.pc t = 33)
    (hi : s.indices t 1 = some 0) (reads : SerialReads values t s) :
    LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t (extra+160) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t extra (serialLane ops values t s) := by
  have beginReady := serial_begin_ready ops values t s reads
  have last := serial_components_ready ops values t 1 31 (values 0) (serialBegin values t s) beginReady
  rewrite [show extra+160=((extra+2)+5*31)+3 by omega,
    serial_begin_eq p guarded ops values t ((extra+2)+5*31) s hp hi reads]
  rewrite [serial_components_eq p guarded ops values t 1 31 (extra+2) (values 0) _ (by decide) beginReady]
  exact serial_exit_eq p guarded ops t extra _ _ last.pc last.counter last.accumulator

theorem serial_lane_pc (ops : Ops α) (values : Nat → α) (t : Nat) (s : State α) :
    (serialLane ops values t s).pc t = 42 := (serial_exit_frames t _ _).1

theorem serial_barrier (guarded : Bool) :
    (program guarded)[42]? = some (.scalar (.barrier .block)) := by cases guarded <;> decide

theorem serial_lane_run (p : Shape) (guarded : Bool) (ops : Ops α) (values : Nat → α)
    (t : Nat) (s : State α) (hp : s.pc t = 33) (hi : s.indices t 1 = some 0)
    (reads : SerialReads values t s) :
    LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t fuel.lane s =
      some (serialLane ops values t s) := by
  rewrite [show fuel.lane=3936+160 by decide,serial_lane_eq p guarded ops values t 3936 s hp hi reads]
  have parked : LarkCollective.parked (program guarded) (serialLane ops values t s) t = some .block := by
    simp only [LarkCollective.parked,serial_lane_pc,serial_barrier]
    rfl
  simp only [LarkCollective.runLane,parked]

theorem serial_lane_value (ops : Ops α) (values : Nat → α) (t : Nat) (s : State α) :
    (serialLane ops values t s).memory (partialCell t 0) = some (serialMaximum ops values) :=
  serial_exit_value t _ _

theorem serial_lane_epochs (ops : Ops α) (values : Nat → α) (t : Nat) (s : State α) :
    (serialLane ops values t s).epochs = s.epochs :=
  (serial_exit_frames t _ _).2.2.2.1.trans
    ((serial_components_frames ops values t 1 31 (values 0) (serialBegin values t s)).2.1.trans
      (serial_begin_frames values t s).2.1)

theorem serial_lane_memory_other (ops : Ops α) (values : Nat → α) (t : Nat) (s : State α)
    (l : Location) (hl : l ≠ partialCell t 0) :
    (serialLane ops values t s).memory l = s.memory l :=
  (serial_exit_memory_other t _ _ l hl).trans
    ((congrFun (serial_components_frames ops values t 1 31 (values 0) (serialBegin values t s)).1 l).trans
      (congrFun (serial_begin_frames values t s).1 l))

theorem serial_lane_trace_length (ops : Ops α) (values : Nat → α) (t : Nat) (s : State α) :
    (serialLane ops values t s).trace.length = s.trace.length+33 := by
  have beginFrame := serial_begin_frames values t s
  have loopFrame := serial_components_frames ops values t 1 31 (values 0) (serialBegin values t s)
  have endFrame := (serial_exit_frames t (serialMaximum ops values)
    (serialComponents ops values t 1 31 (values 0) (serialBegin values t s))).2.2.2.2
  exact endFrame.trans (by rewrite [loopFrame.2.2,beginFrame.2.2]; omega)

theorem serial_lane_good (ops : Ops α) (values : Nat → α) (t : Nat) (s : State α)
    (ht : t%1024=0) (he : (s.epochs t).block=1) (good : ∀ a ∈ s.trace, Good a) :
    ∀ a ∈ (serialLane ops values t s).trace, Good a := by
  have beginEpoch : ((serialBegin values t s).epochs t).block=1 :=
    (congrArg (fun epochs => (epochs t).block) (serial_begin_frames values t s).2.1).trans he
  have loopEpoch : ((serialComponents ops values t 1 31 (values 0) (serialBegin values t s)).epochs t).block=1 :=
    (congrArg (fun epochs => (epochs t).block)
      (serial_components_frames ops values t 1 31 (values 0) (serialBegin values t s)).2.1).trans beginEpoch
  exact serial_exit_good t _ _ ht loopEpoch
    (serial_components_good ops values t 1 31 (values 0) (serialBegin values t s) ht beginEpoch
      (serial_begin_good values t s ht he good))

theorem mid_serial_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row : Nat)
    (s : State α) (ready : MidReady p ops input row s) :
    SerialReads (blockPartial ops input row) (row*1024) s := by
  intro slot hs
  change s.memory ⟨.shared,(row*1024)/1024,0,slot⟩ = _
  rewrite [show row*1024/1024=row by omega]
  exact ready.partials slot hs

theorem serial_mid_lane_run (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) (ready : MidReady p ops input row s) :
    LarkCollective.runLane ops (layout p) (geometry p) (program guarded) (row*1024) fuel.lane s =
      some (serialLane ops (blockPartial ops input row) (row*1024) s) := by
  apply serial_lane_run p guarded ops (blockPartial ops input row) (row*1024) s
  · simpa only [Nat.add_zero] using ready.pc 0 (by decide)
  · simpa using (ready.indices 0 (by decide)).2.1
  · exact mid_serial_reads p ops input row s ready

theorem initial_serial_lane_run (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row : Nat) (hr : row < p.rows) :
    LarkCollective.runLane ops (layout p) (geometry p) (program guarded) (row*1024) fuel.lane
      (midState p ops input row (initial (layout p) input outside)) =
        some (serialLane ops (blockPartial ops input row) (row*1024)
          (midState p ops input row (initial (layout p) input outside))) :=
  serial_mid_lane_run p guarded ops input row _ (initial_mid_ready p ops input outside row hr)

theorem serial_mid_trace_length (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row : Nat)
    (s : State α) :
    (serialLane ops (blockPartial ops input row) (row*1024) (midState p ops input row s)).trace.length =
      s.trace.length+57409 := by
  have h := serial_lane_trace_length ops (blockPartial ops input row) (row*1024) (midState p ops input row s)
  exact h.trans (by rewrite [mid_trace_length]; omega)

theorem serial_mid_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row : Nat)
    (s : State α) (ready : MidReady p ops input row s) :
    ∀ a ∈ (serialLane ops (blockPartial ops input row) (row*1024) s).trace, Good a := by
  apply serial_lane_good ops (blockPartial ops input row) (row*1024) s (by omega)
  · simpa only [Nat.add_zero] using ready.epoch 0 (by decide)
  · exact ready.good

theorem initial_serial_lane_race_free (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row : Nat) (hr : row < p.rows) :
    raceFree (geometry p) (serialLane ops (blockPartial ops input row) (row*1024)
      (midState p ops input row (initial (layout p) input outside))).trace = true :=
  race_free p _ (serial_mid_good p ops input row _ (initial_mid_ready p ops input outside row hr))

#print axioms mid_serial_reads
#print axioms serial_mid_lane_run
#print axioms initial_serial_lane_run
#print axioms serial_mid_trace_length
#print axioms serial_mid_good
#print axioms initial_serial_lane_race_free
#print axioms serial_lane_eq
#print axioms serial_lane_pc
#print axioms serial_barrier
#print axioms serial_lane_run
#print axioms serial_lane_value
#print axioms serial_lane_epochs
#print axioms serial_lane_memory_other
#print axioms serial_lane_trace_length
#print axioms serial_lane_good
end LarkNativeSoftmax
