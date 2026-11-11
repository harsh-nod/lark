import Lark.NativeSoftmaxSumSerialComponents

/-! Actual entry load and exit store of the serial32 sum. The original
source's two tests, both memory effects and source instruction count remain
explicit. The final barrier is reached but has not yet resumed. -/
namespace LarkNativeSoftmax
open LarkNonlinear
open LarkReduction (setIndex setReg execute_index_of predicate_nlt_of)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def sumSerialBegin (values : Nat → α) (t : Nat) (s : State α) : State α :=
  let s := advance s t 84
  let s := setReg (record s t (sumPartialCell t 0) false) t 10 (values 0) 85
  setIndex s t 16 1 86

theorem sum_serial_begin_eq (p : Shape) (guarded : Bool) (ops : Ops α) (values : Nat → α)
    (t extra : Nat) (s : State α) (hp : s.pc t = 83)
    (hi : s.indices t 1 = some 0) (reads : SumSerialReads values t s) :
    LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t (extra+3) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t extra (sumSerialBegin values t s) := by
  let s1 := advance s t 84
  let s2 := setReg (record s1 t (sumPartialCell t 0) false) t 10 (values 0) 85
  have pred : evalPredicate (geometry p) t s (.eq (.ivar 1) (.const 0)) = some true := by
    simp [evalPredicate,evalIndex,hi,int32]
  have e1 : execute ops (layout p) (geometry p) t (.branch (.eq (.ivar 1) (.const 0)) 92) s = some s1 := by
    simp [execute,pred,hp,s1]
  have load : evalExpr ops (layout p) (geometry p) t (.load .shared 1 (.const 0)) s1 =
      some (values 0,record s1 t (sumPartialCell t 0) false) := by
    have hm := reads 0 (by decide)
    simp only [sumPartialCell] at hm
    simp [evalExpr,evalIndex,int32,location,layout,geometry,sumPartialCell,show s1.memory = s.memory by rfl,hm]
  have e2 : execute ops (layout p) (geometry p) t (.assign 10 (.load .shared 1 (.const 0))) s1 = some s2 := by
    simp only [execute,load,bind,pure,Option.bind]
    have hpc : s1.pc t+1=85 := by simp [s1,advance]
    rewrite [hpc]
    rfl
  have e3 := execute_index_of ops (layout p) (geometry p) t 16 86 (.const 1) s2 1 rfl
    (by simp [s2,setReg,advance])
  change execute _ _ _ _ _ s2 = some (sumSerialBegin values t s) at e3
  rewrite [show extra+3=(extra+2)+1 by omega,
    scalar_step p guarded ops t 83 _ _ s s1 (by cases guarded <;> decide) hp e1]
  rewrite [show extra+2=(extra+1)+1 by omega,
    scalar_step p guarded ops t 84 _ _ s1 s2 (by cases guarded <;> decide) (by simp [s1,advance]) e2]
  rewrite [scalar_step p guarded ops t 85 _ _ s2 _ (by cases guarded <;> decide)
    (by simp [s2,setReg,advance]) e3]
  rfl

theorem sum_serial_begin_frames (values : Nat → α) (t : Nat) (s : State α) :
    (sumSerialBegin values t s).memory = s.memory ∧ (sumSerialBegin values t s).epochs = s.epochs ∧
    (sumSerialBegin values t s).trace.length = s.trace.length+1 := by
  simp [sumSerialBegin,setIndex,setReg,record,advance]

theorem sum_serial_begin_ready (ops : Ops α) (values : Nat → α) (t : Nat) (s : State α)
    (reads : SumSerialReads values t s) : SumSerialReady ops values t 1 (values 0) (sumSerialBegin values t s) := by
  exact ⟨by simp [sumSerialBegin,setIndex,advance],by simp [sumSerialBegin,setIndex,advance],
    by simp [sumSerialBegin,setIndex,setReg,advance],by
      intro k hk
      rewrite [(sum_serial_begin_frames values t s).1]
      exact reads k hk⟩

def sumSerialExit (t : Nat) (value : α) (s : State α) : State α :=
  written t 92 (sumPartialCell t 0) value (advance s t 91)

theorem sum_serial_exit_eq (p : Shape) (guarded : Bool) (ops : Ops α) (t extra : Nat)
    (value : α) (s : State α) (hp : s.pc t = 86) (hi : s.indices t 16 = some 32)
    (ha : s.regs t 10 = some value) :
    LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t (extra+2) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t extra (sumSerialExit t value s) := by
  have pred := predicate_nlt_of (geometry p) t s (.ivar 16) (.const 32) 32 32 hi rfl (by omega)
  let s1 := advance s t 91
  have e1 : execute ops (layout p) (geometry p) t (.branch (.lt (.ivar 16) (.const 32)) 91) s = some s1 := by
    simp [execute,pred,s1,hp]
  have e2 : execute ops (layout p) (geometry p) t (.store .shared 1 (.const 0) (.reg 10)) s1 =
      some (sumSerialExit t value s) := by
    simp [execute,evalIndex,int32,location,layout,geometry,sumPartialCell,evalExpr,ha,s1,advance,sumSerialExit,written,record]
  rewrite [show extra+2=(extra+1)+1 by omega,
    scalar_step p guarded ops t 86 _ _ s s1 (by cases guarded <;> decide) hp e1]
  rewrite [scalar_step p guarded ops t 91 _ _ s1 _ (by cases guarded <;> decide) (by simp [s1,advance]) e2]
  rfl

theorem sum_serial_exit_frames (t : Nat) (value : α) (s : State α) :
    (sumSerialExit t value s).pc t = 92 ∧ (sumSerialExit t value s).indices = s.indices ∧
    (sumSerialExit t value s).regs = s.regs ∧ (sumSerialExit t value s).epochs = s.epochs ∧
    (sumSerialExit t value s).trace.length = s.trace.length+1 := by
  simp [sumSerialExit,written,record,advance]

theorem sum_serial_exit_value (t : Nat) (value : α) (s : State α) :
    (sumSerialExit t value s).memory (sumPartialCell t 0) = some value := by
  simp [sumSerialExit,written_memory,advance]

theorem sum_serial_exit_memory_other (t : Nat) (value : α) (s : State α) (l : Location)
    (hl : l ≠ sumPartialCell t 0) : (sumSerialExit t value s).memory l = s.memory l := by
  simp [sumSerialExit,written_memory,hl,advance]

theorem sum_serial_begin_good (values : Nat → α) (t : Nat) (s : State α)
    (ht : t%1024=0) (he : (s.epochs t).block=3) (good : ∀ a ∈ s.trace, Good a) :
    ∀ a ∈ (sumSerialBegin values t s).trace, Good a := by
  intro a ha
  simp only [sumSerialBegin,setIndex,setReg,record,advance,List.mem_cons] at ha
  rcases ha with rfl | ha
  · apply Good.serialAccess rfl rfl (by change 1 < 2; decide) ht
    change (s.epochs t).block=3
    exact he
  · exact good a ha

theorem sum_serial_exit_good (t : Nat) (value : α) (s : State α)
    (ht : t%1024=0) (he : (s.epochs t).block=3) (good : ∀ a ∈ s.trace, Good a) :
    ∀ a ∈ (sumSerialExit t value s).trace, Good a := by
  intro a ha
  simp only [sumSerialExit,written,record,advance,List.mem_cons] at ha
  rcases ha with rfl | ha
  · apply Good.serialAccess rfl rfl (by change 1 < 2; decide) ht
    change (s.epochs t).block=3
    exact he
  · exact good a ha

#print axioms sum_serial_begin_eq
#print axioms sum_serial_begin_frames
#print axioms sum_serial_begin_ready
#print axioms sum_serial_exit_eq
#print axioms sum_serial_exit_frames
#print axioms sum_serial_exit_value
#print axioms sum_serial_exit_memory_other
#print axioms sum_serial_begin_good
#print axioms sum_serial_exit_good
end LarkNativeSoftmax
