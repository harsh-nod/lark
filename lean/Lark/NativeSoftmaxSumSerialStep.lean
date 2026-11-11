import Lark.NativeSoftmaxSumSerialSkip

/-! Per-thread serial-phase step and the frames needed by the actual lane
fold. The leader's old shared reads are required only while it is pending. -/
namespace LarkNativeSoftmax
open LarkNonlinear
open LarkReduction (setIndex setReg)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem sum_serial_begin_other (values : Nat → α) (t u : Nat) (s : State α) (hu : u ≠ t) :
    OtherThread t u s (sumSerialBegin values t s) := by
  simp [OtherThread,sumSerialBegin,setIndex,setReg,record,advance,hu]

theorem sum_serial_component_other (ops : Ops α) (values : Nat → α) (t u slot : Nat)
    (acc : α) (s : State α) (hu : u ≠ t) : OtherThread t u s (sumSerialComponent ops values t slot acc s) := by
  simp [OtherThread,sumSerialComponent,setIndex,setReg,record,advance,hu]

theorem sum_serial_components_other (ops : Ops α) (values : Nat → α) (t u start count : Nat)
    (acc : α) (s : State α) (hu : u ≠ t) : OtherThread t u s (sumSerialComponents ops values t start count acc s) := by
  induction count generalizing start acc s with
  | zero => exact ⟨rfl,rfl,rfl⟩
  | succ count ih =>
    exact other_thread_trans t u _ _ _ (sum_serial_component_other ops values t u start acc s hu)
      (ih (start+1) _ _)

theorem sum_serial_exit_other (t u : Nat) (value : α) (s : State α) (hu : u ≠ t) :
    OtherThread t u s (sumSerialExit t value s) := by
  simp [OtherThread,sumSerialExit,written,record,advance,hu]

theorem sum_serial_lane_other (ops : Ops α) (values : Nat → α) (t u : Nat) (s : State α) (hu : u ≠ t) :
    OtherThread t u s (sumSerialLane ops values t s) :=
  other_thread_trans t u _ _ _ (sum_serial_begin_other values t u s hu)
    (other_thread_trans t u _ _ _ (sum_serial_components_other ops values t u 1 31 (values 0) _ hu)
      (sum_serial_exit_other t u (sumSerialTotal ops values) _ hu))

theorem sum_serial_component_index (ops : Ops α) (values : Nat → α) (t u slot r : Nat)
    (acc : α) (s : State α) (hr : r ≠ 16) :
    (sumSerialComponent ops values t slot acc s).indices u r = s.indices u r := by
  simp [sumSerialComponent,setIndex,setReg,record,advance,hr]

theorem sum_serial_components_index (ops : Ops α) (values : Nat → α) (t u start count r : Nat)
    (acc : α) (s : State α) (hr : r ≠ 16) :
    (sumSerialComponents ops values t start count acc s).indices u r = s.indices u r := by
  induction count generalizing start acc s with
  | zero => rfl
  | succ count ih => exact (ih (start+1) _ _).trans (sum_serial_component_index ops values t u start r acc s hr)

theorem sum_serial_lane_index (ops : Ops α) (values : Nat → α) (t u r : Nat) (s : State α) (hr : r ≠ 16) :
    (sumSerialLane ops values t s).indices u r = s.indices u r := by
  have he := congrArg (fun indices => indices u r)
    (sum_serial_exit_frames t (sumSerialTotal ops values)
      (sumSerialComponents ops values t 1 31 (values 0) (sumSerialBegin values t s))).2.1
  exact he.trans ((sum_serial_components_index ops values t u 1 31 r (values 0) _ hr).trans
    (by simp [sumSerialBegin,setIndex,setReg,record,advance,hr]))

theorem sum_serial_lane_native (ops : Ops α) (values : Nat → α) (t u : Nat) (s : State α)
    (hi : MaxNativeIndices u s) : MaxNativeIndices u (sumSerialLane ops values t s) := by
  exact ⟨(sum_serial_lane_index ops values t u 0 s (by decide)).trans hi.1,
    (sum_serial_lane_index ops values t u 1 s (by decide)).trans hi.2.1,
    (sum_serial_lane_index ops values t u 2 s (by decide)).trans hi.2.2.1,
    (sum_serial_lane_index ops values t u 3 s (by decide)).trans hi.2.2.2⟩

def sumSerialStep (ops : Ops α) (values : Nat → α) (row t : Nat) (s : State α) : State α :=
  if t=row*1024 then sumSerialLane ops values t s else sumSerialSkip t s

theorem sum_serial_step_pc (ops : Ops α) (values : Nat → α) (row t : Nat) (s : State α) :
    (sumSerialStep ops values row t s).pc t = 92 := by
  by_cases h : t=row*1024
  · simpa only [sumSerialStep,h,↓reduceIte] using sum_serial_lane_pc ops values t s
  · simp [sumSerialStep,h,sumSerialSkip,advance]

theorem sum_serial_step_other (ops : Ops α) (values : Nat → α) (row t u : Nat) (s : State α) (hu : u ≠ t) :
    OtherThread t u s (sumSerialStep ops values row t s) := by
  by_cases h : t=row*1024
  · simpa only [sumSerialStep,h,↓reduceIte] using sum_serial_lane_other ops values t u s hu
  · simp [OtherThread,sumSerialStep,h,sumSerialSkip,advance,hu]

theorem sum_serial_step_native (ops : Ops α) (values : Nat → α) (row t u : Nat) (s : State α)
    (hi : MaxNativeIndices u s) : MaxNativeIndices u (sumSerialStep ops values row t s) := by
  by_cases h : t=row*1024
  · simpa only [sumSerialStep,h,↓reduceIte] using sum_serial_lane_native ops values t u s hi
  · simpa only [sumSerialStep,h,↓reduceIte,sumSerialSkip,advance] using hi

theorem sum_serial_step_run (p : Shape) (guarded : Bool) (ops : Ops α) (values : Nat → α)
    (row t : Nat) (s : State α) (hb : t/1024=row) (hp : s.pc t=83) (hi : MaxNativeIndices t s)
    (reads : t=row*1024 → SumSerialReads values t s) :
    LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t fuel.lane s =
      some (sumSerialStep ops values row t s) := by
  by_cases h : t=row*1024
  · rewrite [sumSerialStep,if_pos h]
    apply sum_serial_lane_run p guarded ops values t s hp
    · have hz : t%1024=0 := by omega
      simpa [hz] using hi.2.1
    · exact reads h
  · rewrite [sumSerialStep,if_neg h]
    exact sum_serial_skip_run p guarded ops t (t%1024) s (by omega) hp hi.2.1

theorem sum_serial_step_epochs (ops : Ops α) (values : Nat → α) (row t : Nat) (s : State α) :
    (sumSerialStep ops values row t s).epochs = s.epochs := by
  by_cases h : t=row*1024
  · simpa only [sumSerialStep,h,↓reduceIte] using sum_serial_lane_epochs ops values t s
  · simp [sumSerialStep,h,sumSerialSkip,advance]

theorem sum_serial_step_nonleader_memory (ops : Ops α) (values : Nat → α) (row t : Nat) (s : State α)
    (hn : t ≠ row*1024) : (sumSerialStep ops values row t s).memory = s.memory := by
  simp [sumSerialStep,hn,sumSerialSkip,advance]

theorem sum_serial_step_memory_other (ops : Ops α) (values : Nat → α) (row t : Nat) (s : State α)
    (l : Location) (hl : l ≠ sumPartialCell (row*1024) 0) :
    (sumSerialStep ops values row t s).memory l = s.memory l := by
  by_cases h : t=row*1024
  · subst t
    simpa only [sumSerialStep,↓reduceIte] using sum_serial_lane_memory_other ops values (row*1024) s l hl
  · rewrite [sum_serial_step_nonleader_memory ops values row t s h]
    rfl

theorem sum_serial_step_good (ops : Ops α) (values : Nat → α) (row t : Nat) (s : State α)
    (he : (s.epochs t).block=3) (good : ∀ a ∈ s.trace, Good a) :
    ∀ a ∈ (sumSerialStep ops values row t s).trace, Good a := by
  by_cases h : t=row*1024
  · simpa only [sumSerialStep,h,↓reduceIte] using sum_serial_lane_good ops values t s (by omega) he good
  · simpa only [sumSerialStep,h,↓reduceIte,sumSerialSkip,advance] using good

#print axioms sum_serial_begin_other
#print axioms sum_serial_component_other
#print axioms sum_serial_components_other
#print axioms sum_serial_exit_other
#print axioms sum_serial_lane_other
#print axioms sum_serial_component_index
#print axioms sum_serial_components_index
#print axioms sum_serial_lane_index
#print axioms sum_serial_lane_native
#print axioms sum_serial_step_pc
#print axioms sum_serial_step_other
#print axioms sum_serial_step_native
#print axioms sum_serial_step_run
#print axioms sum_serial_step_epochs
#print axioms sum_serial_step_nonleader_memory
#print axioms sum_serial_step_memory_other
#print axioms sum_serial_step_good
end LarkNativeSoftmax
