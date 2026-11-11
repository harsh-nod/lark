import Lark.NativeSoftmaxMaxBarrier

/-! Actual scalar serial reduction component at PC36..40. The source order,
shared read, trace and original instruction budget are retained. -/
namespace LarkNativeSoftmax
open LarkNonlinear
open LarkReduction (setIndex setReg execute_index_of execute_pure_of predicate_lt_of)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def SerialReads (values : Nat → α) (t : Nat) (s : State α) : Prop :=
  ∀ slot, slot < 32 → s.memory (partialCell t slot) = some (values slot)

theorem serial_read_location (p : Shape) (t slot : Nat) (hs : slot < 32) :
    location (layout p) (geometry p) t .shared 0 (slot : Int) false = some (partialCell t slot) := by
  simp [location,layout,geometry,partialCell,show ¬ (slot : Int) < 0 by omega,hs]

def serialComponent (ops : Ops α) (values : Nat → α) (t slot : Nat) (acc : α) (s : State α) : State α :=
  let s := advance s t 37
  let s := setReg (record s t (partialCell t slot) false) t 4 (values slot) 38
  let s := setReg s t 3 (ops.max acc (values slot)) 39
  let s := setIndex s t 8 ((slot+1 : Nat) : Int) 40
  advance s t 36

theorem serial_component_eq (p : Shape) (guarded : Bool) (ops : Ops α) (values : Nat → α)
    (t slot extra : Nat) (acc : α) (s : State α) (hs : slot < 32)
    (hp : s.pc t = 36) (hi : s.indices t 8 = some (slot : Int))
    (ha : s.regs t 3 = some acc) (reads : SerialReads values t s) :
    LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t (extra+5) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t extra
        (serialComponent ops values t slot acc s) := by
  let s1 := advance s t 37
  let s2 := setReg (record s1 t (partialCell t slot) false) t 4 (values slot) 38
  let s3 := setReg s2 t 3 (ops.max acc (values slot)) 39
  let s4 := setIndex s3 t 8 ((slot+1 : Nat) : Int) 40
  have pred := predicate_lt_of (geometry p) t s (.ivar 8) (.const 32) (slot : Int) 32 hi rfl (by omega)
  have e1 : execute ops (layout p) (geometry p) t (.branch (.lt (.ivar 8) (.const 32)) 41) s = some s1 := by
    simp [execute,pred,hp,s1]
  have load : evalExpr ops (layout p) (geometry p) t (.load .shared 0 (.ivar 8)) s1 =
      some (values slot,record s1 t (partialCell t slot) false) := by
    simp only [evalExpr,evalIndex,show s1.indices t 8 = some (slot : Int) from hi,
      serial_read_location p t slot hs,show s1.memory (partialCell t slot) = some (values slot) from reads slot hs,
      bind,pure,Option.bind]
  have e2 : execute ops (layout p) (geometry p) t (.assign 4 (.load .shared 0 (.ivar 8))) s1 = some s2 := by
    simp only [execute,load,bind,pure,Option.bind]
    have hpc : s1.pc t+1=38 := by simp [s1,advance]
    rewrite [hpc]
    rfl
  have hacc : s2.regs t 3 = some acc := by simpa [s2,s1,setReg,record,advance] using ha
  have hvalue : s2.regs t 4 = some (values slot) := by simp [s2,setReg,advance]
  have e3 := execute_pure_of ops (layout p) (geometry p) t 3 39 (.bin .max (.reg 3) (.reg 4)) s2
    (ops.max acc (values slot)) (by simp only [evalExpr,applyBinary,hacc,hvalue,bind,pure,Option.bind])
    (by simp [s2,setReg,advance])
  change execute _ _ _ _ _ s2 = some s3 at e3
  have hindex : s3.indices t 8 = some (slot : Int) := hi
  have nextIndex := eval_nat_sum (geometry p) t slot 1 s3 (.ivar 8) (.const 1) hindex rfl (by omega)
  have e4 := execute_index_of ops (layout p) (geometry p) t 8 40 (.add (.ivar 8) (.const 1)) s3 _ nextIndex
    (by simp [s3,setReg,advance])
  change execute _ _ _ _ _ s3 = some s4 at e4
  have e5 : execute ops (layout p) (geometry p) t (.jump 36) s4 =
      some (serialComponent ops values t slot acc s) := rfl
  rewrite [show extra+5=(extra+4)+1 by omega,
    scalar_step p guarded ops t 36 _ _ s s1 (by cases guarded <;> decide) hp e1]
  rewrite [show extra+4=(extra+3)+1 by omega,
    scalar_step p guarded ops t 37 _ _ s1 s2 (by cases guarded <;> decide) (by simp [s1,advance]) e2]
  rewrite [show extra+3=(extra+2)+1 by omega,
    scalar_step p guarded ops t 38 _ _ s2 s3 (by cases guarded <;> decide) (by simp [s2,setReg,advance]) e3]
  rewrite [show extra+2=(extra+1)+1 by omega,
    scalar_step p guarded ops t 39 _ _ s3 s4 (by cases guarded <;> decide) (by simp [s3,setReg,advance]) e4]
  rewrite [scalar_step p guarded ops t 40 _ _ s4 _ (by cases guarded <;> decide)
    (by simp [s4,setIndex,advance]) e5]
  rfl

theorem serial_component_frames (ops : Ops α) (values : Nat → α) (t slot : Nat) (acc : α) (s : State α) :
    (serialComponent ops values t slot acc s).memory = s.memory ∧
    (serialComponent ops values t slot acc s).epochs = s.epochs ∧
    (serialComponent ops values t slot acc s).trace.length = s.trace.length+1 := by
  simp [serialComponent,setIndex,setReg,record,advance]

theorem serial_component_fields (ops : Ops α) (values : Nat → α) (t slot : Nat) (acc : α) (s : State α) :
    (serialComponent ops values t slot acc s).pc t = 36 ∧
    (serialComponent ops values t slot acc s).indices t 8 = some ((slot+1 : Nat) : Int) ∧
    (serialComponent ops values t slot acc s).regs t 3 = some (ops.max acc (values slot)) := by
  simp [serialComponent,setIndex,setReg,record,advance]

theorem serial_component_good (ops : Ops α) (values : Nat → α) (t slot : Nat) (acc : α) (s : State α)
    (ht : t%1024=0) (he : (s.epochs t).block=1) (good : ∀ a ∈ s.trace, Good a) :
    ∀ a ∈ (serialComponent ops values t slot acc s).trace, Good a := by
  intro a ha
  simp only [serialComponent,setIndex,setReg,record,advance,List.mem_cons] at ha
  rcases ha with rfl | ha
  · apply Good.serialAccess rfl rfl (by change 0 < 2; decide)
    · exact ht
    · change (s.epochs t).block = 1
      exact he
  · exact good a ha

structure SerialReady (ops : Ops α) (values : Nat → α) (t slot : Nat) (acc : α) (s : State α) : Prop where
  pc : s.pc t = 36
  counter : s.indices t 8 = some (slot : Int)
  accumulator : s.regs t 3 = some acc
  reads : SerialReads values t s

theorem serial_component_ready (ops : Ops α) (values : Nat → α) (t slot : Nat) (acc : α)
    (s : State α) (ready : SerialReady ops values t slot acc s) :
    SerialReady ops values t (slot+1) (ops.max acc (values slot)) (serialComponent ops values t slot acc s) := by
  have h := serial_component_fields ops values t slot acc s
  exact ⟨h.1,h.2.1,h.2.2,by
    intro k hk
    rewrite [(serial_component_frames ops values t slot acc s).1]
    exact ready.reads k hk⟩

def serialFold (ops : Ops α) (values : Nat → α) (start : Nat) : Nat → α → α
  | 0,acc => acc
  | count+1,acc => serialFold ops values (start+1) count (ops.max acc (values start))

def serialComponents (ops : Ops α) (values : Nat → α) (t start : Nat) : Nat → α → State α → State α
  | 0,_,s => s
  | count+1,acc,s => serialComponents ops values t (start+1) count (ops.max acc (values start))
      (serialComponent ops values t start acc s)

theorem serial_components_eq (p : Shape) (guarded : Bool) (ops : Ops α) (values : Nat → α)
    (t start count extra : Nat) (acc : α) (s : State α) (hn : start+count ≤ 32)
    (ready : SerialReady ops values t start acc s) :
    LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t (extra+5*count) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t extra
        (serialComponents ops values t start count acc s) := by
  induction count generalizing start acc s with
  | zero => rfl
  | succ count ih =>
    rewrite [show extra+5*(count+1)=(extra+5*count)+5 by omega,
      serial_component_eq p guarded ops values t start (extra+5*count) acc s
        (by omega) ready.pc ready.counter ready.accumulator ready.reads]
    exact ih (start+1) _ _ (by omega) (serial_component_ready ops values t start acc s ready)

theorem serial_components_ready (ops : Ops α) (values : Nat → α) (t start count : Nat)
    (acc : α) (s : State α) (ready : SerialReady ops values t start acc s) :
    SerialReady ops values t (start+count) (serialFold ops values start count acc)
      (serialComponents ops values t start count acc s) := by
  induction count generalizing start acc s with
  | zero => simpa only [serialComponents,serialFold,Nat.add_zero] using ready
  | succ count ih =>
    have h := ih (start+1) _ _ (serial_component_ready ops values t start acc s ready)
    simpa only [serialComponents,serialFold,show start+1+count=start+(count+1) by omega] using h

theorem serial_components_frames (ops : Ops α) (values : Nat → α) (t start count : Nat)
    (acc : α) (s : State α) :
    (serialComponents ops values t start count acc s).memory = s.memory ∧
    (serialComponents ops values t start count acc s).epochs = s.epochs ∧
    (serialComponents ops values t start count acc s).trace.length = s.trace.length+count := by
  induction count generalizing start acc s with
  | zero => exact ⟨rfl,rfl,by simp [serialComponents]⟩
  | succ count ih =>
    have head := serial_component_frames ops values t start acc s
    have tail := ih (start+1) (ops.max acc (values start)) (serialComponent ops values t start acc s)
    refine ⟨tail.1.trans head.1,tail.2.1.trans head.2.1,?_⟩
    change (serialComponents ops values t (start+1) count _ _).trace.length = _
    rewrite [tail.2.2,head.2.2]
    omega

theorem serial_components_good (ops : Ops α) (values : Nat → α) (t start count : Nat)
    (acc : α) (s : State α) (ht : t%1024=0) (he : (s.epochs t).block=1)
    (good : ∀ a ∈ s.trace, Good a) :
    ∀ a ∈ (serialComponents ops values t start count acc s).trace, Good a := by
  induction count generalizing start acc s with
  | zero => exact good
  | succ count ih =>
    exact ih (start+1) _ _
      ((congrArg (fun epochs => (epochs t).block) (serial_component_frames ops values t start acc s).2.1).trans he)
      (serial_component_good ops values t start acc s ht he good)

#print axioms serial_component_ready
#print axioms serial_components_eq
#print axioms serial_components_ready
#print axioms serial_components_frames
#print axioms serial_components_good
#print axioms serial_read_location
#print axioms serial_component_eq
#print axioms serial_component_frames
#print axioms serial_component_fields
#print axioms serial_component_good
end LarkNativeSoftmax
