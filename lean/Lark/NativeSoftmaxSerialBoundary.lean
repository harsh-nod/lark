import Lark.NativeSoftmaxSerialComponents

/-! Actual entry load and exit store of the serial32 maximum. The original
source's two tests, both memory effects and source instruction count remain
explicit. The final barrier is reached but has not yet resumed. -/
namespace LarkNativeSoftmax
open LarkNonlinear
open LarkReduction (setIndex setReg execute_index_of predicate_nlt_of)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def serialBegin (values : Nat → α) (t : Nat) (s : State α) : State α :=
  let s := advance s t 34
  let s := setReg (record s t (partialCell t 0) false) t 3 (values 0) 35
  setIndex s t 8 1 36

theorem serial_begin_eq (p : Shape) (guarded : Bool) (ops : Ops α) (values : Nat → α)
    (t extra : Nat) (s : State α) (hp : s.pc t = 33)
    (hi : s.indices t 1 = some 0) (reads : SerialReads values t s) :
    LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t (extra+3) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t extra (serialBegin values t s) := by
  let s1 := advance s t 34
  let s2 := setReg (record s1 t (partialCell t 0) false) t 3 (values 0) 35
  have pred : evalPredicate (geometry p) t s (.eq (.ivar 1) (.const 0)) = some true := by
    simp [evalPredicate,evalIndex,hi,int32]
  have e1 : execute ops (layout p) (geometry p) t (.branch (.eq (.ivar 1) (.const 0)) 42) s = some s1 := by
    simp [execute,pred,hp,s1]
  have load : evalExpr ops (layout p) (geometry p) t (.load .shared 0 (.const 0)) s1 =
      some (values 0,record s1 t (partialCell t 0) false) := by
    have hm := reads 0 (by decide)
    simp only [partialCell] at hm
    simp [evalExpr,evalIndex,int32,location,layout,geometry,partialCell,show s1.memory = s.memory by rfl,hm]
  have e2 : execute ops (layout p) (geometry p) t (.assign 3 (.load .shared 0 (.const 0))) s1 = some s2 := by
    simp only [execute,load,bind,pure,Option.bind]
    have hpc : s1.pc t+1=35 := by simp [s1,advance]
    rewrite [hpc]
    rfl
  have e3 := execute_index_of ops (layout p) (geometry p) t 8 36 (.const 1) s2 1 rfl
    (by simp [s2,setReg,advance])
  change execute _ _ _ _ _ s2 = some (serialBegin values t s) at e3
  rewrite [show extra+3=(extra+2)+1 by omega,
    scalar_step p guarded ops t 33 _ _ s s1 (by cases guarded <;> decide) hp e1]
  rewrite [show extra+2=(extra+1)+1 by omega,
    scalar_step p guarded ops t 34 _ _ s1 s2 (by cases guarded <;> decide) (by simp [s1,advance]) e2]
  rewrite [scalar_step p guarded ops t 35 _ _ s2 _ (by cases guarded <;> decide)
    (by simp [s2,setReg,advance]) e3]
  rfl

theorem serial_begin_frames (values : Nat → α) (t : Nat) (s : State α) :
    (serialBegin values t s).memory = s.memory ∧ (serialBegin values t s).epochs = s.epochs ∧
    (serialBegin values t s).trace.length = s.trace.length+1 := by
  simp [serialBegin,setIndex,setReg,record,advance]

theorem serial_begin_ready (ops : Ops α) (values : Nat → α) (t : Nat) (s : State α)
    (reads : SerialReads values t s) : SerialReady ops values t 1 (values 0) (serialBegin values t s) := by
  exact ⟨by simp [serialBegin,setIndex,advance],by simp [serialBegin,setIndex,advance],
    by simp [serialBegin,setIndex,setReg,advance],by
      intro k hk
      rewrite [(serial_begin_frames values t s).1]
      exact reads k hk⟩

def serialExit (t : Nat) (value : α) (s : State α) : State α :=
  written t 42 (partialCell t 0) value (advance s t 41)

theorem serial_exit_eq (p : Shape) (guarded : Bool) (ops : Ops α) (t extra : Nat)
    (value : α) (s : State α) (hp : s.pc t = 36) (hi : s.indices t 8 = some 32)
    (ha : s.regs t 3 = some value) :
    LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t (extra+2) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t extra (serialExit t value s) := by
  have pred := predicate_nlt_of (geometry p) t s (.ivar 8) (.const 32) 32 32 hi rfl (by omega)
  let s1 := advance s t 41
  have e1 : execute ops (layout p) (geometry p) t (.branch (.lt (.ivar 8) (.const 32)) 41) s = some s1 := by
    simp [execute,pred,s1,hp]
  have e2 : execute ops (layout p) (geometry p) t (.store .shared 0 (.const 0) (.reg 3)) s1 =
      some (serialExit t value s) := by
    simp [execute,evalIndex,int32,location,layout,geometry,partialCell,evalExpr,ha,s1,advance,serialExit,written,record]
  rewrite [show extra+2=(extra+1)+1 by omega,
    scalar_step p guarded ops t 36 _ _ s s1 (by cases guarded <;> decide) hp e1]
  rewrite [scalar_step p guarded ops t 41 _ _ s1 _ (by cases guarded <;> decide) (by simp [s1,advance]) e2]
  rfl

theorem serial_exit_frames (t : Nat) (value : α) (s : State α) :
    (serialExit t value s).pc t = 42 ∧ (serialExit t value s).indices = s.indices ∧
    (serialExit t value s).regs = s.regs ∧ (serialExit t value s).epochs = s.epochs ∧
    (serialExit t value s).trace.length = s.trace.length+1 := by
  simp [serialExit,written,record,advance]

theorem serial_exit_value (t : Nat) (value : α) (s : State α) :
    (serialExit t value s).memory (partialCell t 0) = some value := by
  simp [serialExit,written_memory,advance]

theorem serial_exit_memory_other (t : Nat) (value : α) (s : State α) (l : Location)
    (hl : l ≠ partialCell t 0) : (serialExit t value s).memory l = s.memory l := by
  simp [serialExit,written_memory,hl,advance]

theorem serial_begin_good (values : Nat → α) (t : Nat) (s : State α)
    (ht : t%1024=0) (he : (s.epochs t).block=1) (good : ∀ a ∈ s.trace, Good a) :
    ∀ a ∈ (serialBegin values t s).trace, Good a := by
  intro a ha
  simp only [serialBegin,setIndex,setReg,record,advance,List.mem_cons] at ha
  rcases ha with rfl | ha
  · apply Good.serialAccess rfl rfl (by change 0 < 2; decide) ht
    change (s.epochs t).block=1
    exact he
  · exact good a ha

theorem serial_exit_good (t : Nat) (value : α) (s : State α)
    (ht : t%1024=0) (he : (s.epochs t).block=1) (good : ∀ a ∈ s.trace, Good a) :
    ∀ a ∈ (serialExit t value s).trace, Good a := by
  intro a ha
  simp only [serialExit,written,record,advance,List.mem_cons] at ha
  rcases ha with rfl | ha
  · apply Good.serialAccess rfl rfl (by change 0 < 2; decide) ht
    change (s.epochs t).block=1
    exact he
  · exact good a ha

#print axioms serial_begin_eq
#print axioms serial_begin_frames
#print axioms serial_begin_ready
#print axioms serial_exit_eq
#print axioms serial_exit_frames
#print axioms serial_exit_value
#print axioms serial_exit_memory_other
#print axioms serial_begin_good
#print axioms serial_exit_good
end LarkNativeSoftmax
