import Lark.NativeSoftmaxSerialSkip

/-! Per-thread serial-phase step and the frames needed by the actual lane
fold. The leader's old shared reads are required only while it is pending. -/
namespace LarkNativeSoftmax
open LarkNonlinear
open LarkReduction (setIndex setReg)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem serial_begin_other (values : Nat → α) (t u : Nat) (s : State α) (hu : u ≠ t) :
    OtherThread t u s (serialBegin values t s) := by
  simp [OtherThread,serialBegin,setIndex,setReg,record,advance,hu]

theorem serial_component_other (ops : Ops α) (values : Nat → α) (t u slot : Nat)
    (acc : α) (s : State α) (hu : u ≠ t) : OtherThread t u s (serialComponent ops values t slot acc s) := by
  simp [OtherThread,serialComponent,setIndex,setReg,record,advance,hu]

theorem serial_components_other (ops : Ops α) (values : Nat → α) (t u start count : Nat)
    (acc : α) (s : State α) (hu : u ≠ t) : OtherThread t u s (serialComponents ops values t start count acc s) := by
  induction count generalizing start acc s with
  | zero => exact ⟨rfl,rfl,rfl⟩
  | succ count ih =>
    exact other_thread_trans t u _ _ _ (serial_component_other ops values t u start acc s hu)
      (ih (start+1) _ _)

theorem serial_exit_other (t u : Nat) (value : α) (s : State α) (hu : u ≠ t) :
    OtherThread t u s (serialExit t value s) := by
  simp [OtherThread,serialExit,written,record,advance,hu]

theorem serial_lane_other (ops : Ops α) (values : Nat → α) (t u : Nat) (s : State α) (hu : u ≠ t) :
    OtherThread t u s (serialLane ops values t s) :=
  other_thread_trans t u _ _ _ (serial_begin_other values t u s hu)
    (other_thread_trans t u _ _ _ (serial_components_other ops values t u 1 31 (values 0) _ hu)
      (serial_exit_other t u (serialMaximum ops values) _ hu))

theorem serial_component_index (ops : Ops α) (values : Nat → α) (t u slot r : Nat)
    (acc : α) (s : State α) (hr : r ≠ 8) :
    (serialComponent ops values t slot acc s).indices u r = s.indices u r := by
  simp [serialComponent,setIndex,setReg,record,advance,hr]

theorem serial_components_index (ops : Ops α) (values : Nat → α) (t u start count r : Nat)
    (acc : α) (s : State α) (hr : r ≠ 8) :
    (serialComponents ops values t start count acc s).indices u r = s.indices u r := by
  induction count generalizing start acc s with
  | zero => rfl
  | succ count ih => exact (ih (start+1) _ _).trans (serial_component_index ops values t u start r acc s hr)

theorem serial_lane_index (ops : Ops α) (values : Nat → α) (t u r : Nat) (s : State α) (hr : r ≠ 8) :
    (serialLane ops values t s).indices u r = s.indices u r := by
  have he := congrArg (fun indices => indices u r)
    (serial_exit_frames t (serialMaximum ops values)
      (serialComponents ops values t 1 31 (values 0) (serialBegin values t s))).2.1
  exact he.trans ((serial_components_index ops values t u 1 31 r (values 0) _ hr).trans
    (by simp [serialBegin,setIndex,setReg,record,advance,hr]))

theorem serial_lane_native (ops : Ops α) (values : Nat → α) (t u : Nat) (s : State α)
    (hi : MaxNativeIndices u s) : MaxNativeIndices u (serialLane ops values t s) := by
  exact ⟨(serial_lane_index ops values t u 0 s (by decide)).trans hi.1,
    (serial_lane_index ops values t u 1 s (by decide)).trans hi.2.1,
    (serial_lane_index ops values t u 2 s (by decide)).trans hi.2.2.1,
    (serial_lane_index ops values t u 3 s (by decide)).trans hi.2.2.2⟩

def serialStep (ops : Ops α) (values : Nat → α) (row t : Nat) (s : State α) : State α :=
  if t=row*1024 then serialLane ops values t s else serialSkip t s

theorem serial_step_pc (ops : Ops α) (values : Nat → α) (row t : Nat) (s : State α) :
    (serialStep ops values row t s).pc t = 42 := by
  by_cases h : t=row*1024
  · simpa only [serialStep,h,↓reduceIte] using serial_lane_pc ops values t s
  · simp [serialStep,h,serialSkip,advance]

theorem serial_step_other (ops : Ops α) (values : Nat → α) (row t u : Nat) (s : State α) (hu : u ≠ t) :
    OtherThread t u s (serialStep ops values row t s) := by
  by_cases h : t=row*1024
  · simpa only [serialStep,h,↓reduceIte] using serial_lane_other ops values t u s hu
  · simp [OtherThread,serialStep,h,serialSkip,advance,hu]

theorem serial_step_native (ops : Ops α) (values : Nat → α) (row t u : Nat) (s : State α)
    (hi : MaxNativeIndices u s) : MaxNativeIndices u (serialStep ops values row t s) := by
  by_cases h : t=row*1024
  · simpa only [serialStep,h,↓reduceIte] using serial_lane_native ops values t u s hi
  · simpa only [serialStep,h,↓reduceIte,serialSkip,advance] using hi

theorem serial_step_run (p : Shape) (guarded : Bool) (ops : Ops α) (values : Nat → α)
    (row t : Nat) (s : State α) (hb : t/1024=row) (hp : s.pc t=33) (hi : MaxNativeIndices t s)
    (reads : t=row*1024 → SerialReads values t s) :
    LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t fuel.lane s =
      some (serialStep ops values row t s) := by
  by_cases h : t=row*1024
  · rewrite [serialStep,if_pos h]
    apply serial_lane_run p guarded ops values t s hp
    · have hz : t%1024=0 := by omega
      simpa [hz] using hi.2.1
    · exact reads h
  · rewrite [serialStep,if_neg h]
    exact serial_skip_run p guarded ops t (t%1024) s (by omega) hp hi.2.1

theorem serial_step_epochs (ops : Ops α) (values : Nat → α) (row t : Nat) (s : State α) :
    (serialStep ops values row t s).epochs = s.epochs := by
  by_cases h : t=row*1024
  · simpa only [serialStep,h,↓reduceIte] using serial_lane_epochs ops values t s
  · simp [serialStep,h,serialSkip,advance]

theorem serial_step_nonleader_memory (ops : Ops α) (values : Nat → α) (row t : Nat) (s : State α)
    (hn : t ≠ row*1024) : (serialStep ops values row t s).memory = s.memory := by
  simp [serialStep,hn,serialSkip,advance]

theorem serial_step_memory_other (ops : Ops α) (values : Nat → α) (row t : Nat) (s : State α)
    (l : Location) (hl : l ≠ partialCell (row*1024) 0) :
    (serialStep ops values row t s).memory l = s.memory l := by
  by_cases h : t=row*1024
  · subst t
    simpa only [serialStep,↓reduceIte] using serial_lane_memory_other ops values (row*1024) s l hl
  · rewrite [serial_step_nonleader_memory ops values row t s h]
    rfl

theorem serial_step_good (ops : Ops α) (values : Nat → α) (row t : Nat) (s : State α)
    (he : (s.epochs t).block=1) (good : ∀ a ∈ s.trace, Good a) :
    ∀ a ∈ (serialStep ops values row t s).trace, Good a := by
  by_cases h : t=row*1024
  · simpa only [serialStep,h,↓reduceIte] using serial_lane_good ops values t s (by omega) he good
  · simpa only [serialStep,h,↓reduceIte,serialSkip,advance] using good

#print axioms serial_begin_other
#print axioms serial_component_other
#print axioms serial_components_other
#print axioms serial_exit_other
#print axioms serial_lane_other
#print axioms serial_component_index
#print axioms serial_components_index
#print axioms serial_lane_index
#print axioms serial_lane_native
#print axioms serial_step_pc
#print axioms serial_step_other
#print axioms serial_step_native
#print axioms serial_step_run
#print axioms serial_step_epochs
#print axioms serial_step_nonleader_memory
#print axioms serial_step_memory_other
#print axioms serial_step_good
end LarkNativeSoftmax
