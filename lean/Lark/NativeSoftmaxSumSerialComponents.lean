import Lark.NativeSoftmaxExpCounts

/-! Actual scalar serial reduction component at PC36..90. The source order,
shared read, trace and original instruction budget are retained. -/
namespace LarkNativeSoftmax
open LarkNonlinear
open LarkReduction (setIndex setReg execute_index_of execute_pure_of predicate_lt_of)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def SumSerialReads (values : Nat → α) (t : Nat) (s : State α) : Prop :=
  ∀ slot, slot < 32 → s.memory (sumPartialCell t slot) = some (values slot)

theorem sum_serial_read_location (p : Shape) (t slot : Nat) (hs : slot < 32) :
    location (layout p) (geometry p) t .shared 1 (slot : Int) false = some (sumPartialCell t slot) := by
  simp [location,layout,geometry,sumPartialCell,show ¬ (slot : Int) < 0 by omega,hs]

def sumSerialComponent (ops : Ops α) (values : Nat → α) (t slot : Nat) (acc : α) (s : State α) : State α :=
  let s := advance s t 87
  let s := setReg (record s t (sumPartialCell t slot) false) t 11 (values slot) 88
  let s := setReg s t 10 (ops.add acc (values slot)) 89
  let s := setIndex s t 16 ((slot+1 : Nat) : Int) 90
  advance s t 86

theorem sum_serial_component_eq (p : Shape) (guarded : Bool) (ops : Ops α) (values : Nat → α)
    (t slot extra : Nat) (acc : α) (s : State α) (hs : slot < 32)
    (hp : s.pc t = 86) (hi : s.indices t 16 = some (slot : Int))
    (ha : s.regs t 10 = some acc) (reads : SumSerialReads values t s) :
    LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t (extra+5) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t extra
        (sumSerialComponent ops values t slot acc s) := by
  let s1 := advance s t 87
  let s2 := setReg (record s1 t (sumPartialCell t slot) false) t 11 (values slot) 88
  let s3 := setReg s2 t 10 (ops.add acc (values slot)) 89
  let s4 := setIndex s3 t 16 ((slot+1 : Nat) : Int) 90
  have pred := predicate_lt_of (geometry p) t s (.ivar 16) (.const 32) (slot : Int) 32 hi rfl (by omega)
  have e1 : execute ops (layout p) (geometry p) t (.branch (.lt (.ivar 16) (.const 32)) 91) s = some s1 := by
    simp [execute,pred,hp,s1]
  have load : evalExpr ops (layout p) (geometry p) t (.load .shared 1 (.ivar 16)) s1 =
      some (values slot,record s1 t (sumPartialCell t slot) false) := by
    simp only [evalExpr,evalIndex,show s1.indices t 16 = some (slot : Int) from hi,
      sum_serial_read_location p t slot hs,show s1.memory (sumPartialCell t slot) = some (values slot) from reads slot hs,
      bind,pure,Option.bind]
  have e2 : execute ops (layout p) (geometry p) t (.assign 11 (.load .shared 1 (.ivar 16))) s1 = some s2 := by
    simp only [execute,load,bind,pure,Option.bind]
    have hpc : s1.pc t+1=88 := by simp [s1,advance]
    rewrite [hpc]
    rfl
  have hacc : s2.regs t 10 = some acc := by simpa [s2,s1,setReg,record,advance] using ha
  have hvalue : s2.regs t 11 = some (values slot) := by simp [s2,setReg,advance]
  have e3 := execute_pure_of ops (layout p) (geometry p) t 10 89 (.bin .add (.reg 10) (.reg 11)) s2
    (ops.add acc (values slot)) (by simp only [evalExpr,applyBinary,hacc,hvalue,bind,pure,Option.bind])
    (by simp [s2,setReg,advance])
  change execute _ _ _ _ _ s2 = some s3 at e3
  have hindex : s3.indices t 16 = some (slot : Int) := hi
  have nextIndex := eval_nat_sum (geometry p) t slot 1 s3 (.ivar 16) (.const 1) hindex rfl (by omega)
  have e4 := execute_index_of ops (layout p) (geometry p) t 16 90 (.add (.ivar 16) (.const 1)) s3 _ nextIndex
    (by simp [s3,setReg,advance])
  change execute _ _ _ _ _ s3 = some s4 at e4
  have e5 : execute ops (layout p) (geometry p) t (.jump 86) s4 =
      some (sumSerialComponent ops values t slot acc s) := rfl
  rewrite [show extra+5=(extra+4)+1 by omega,
    scalar_step p guarded ops t 86 _ _ s s1 (by cases guarded <;> decide) hp e1]
  rewrite [show extra+4=(extra+3)+1 by omega,
    scalar_step p guarded ops t 87 _ _ s1 s2 (by cases guarded <;> decide) (by simp [s1,advance]) e2]
  rewrite [show extra+3=(extra+2)+1 by omega,
    scalar_step p guarded ops t 88 _ _ s2 s3 (by cases guarded <;> decide) (by simp [s2,setReg,advance]) e3]
  rewrite [show extra+2=(extra+1)+1 by omega,
    scalar_step p guarded ops t 89 _ _ s3 s4 (by cases guarded <;> decide) (by simp [s3,setReg,advance]) e4]
  rewrite [scalar_step p guarded ops t 90 _ _ s4 _ (by cases guarded <;> decide)
    (by simp [s4,setIndex,advance]) e5]
  rfl

theorem sum_serial_component_frames (ops : Ops α) (values : Nat → α) (t slot : Nat) (acc : α) (s : State α) :
    (sumSerialComponent ops values t slot acc s).memory = s.memory ∧
    (sumSerialComponent ops values t slot acc s).epochs = s.epochs ∧
    (sumSerialComponent ops values t slot acc s).trace.length = s.trace.length+1 := by
  simp [sumSerialComponent,setIndex,setReg,record,advance]

theorem sum_serial_component_fields (ops : Ops α) (values : Nat → α) (t slot : Nat) (acc : α) (s : State α) :
    (sumSerialComponent ops values t slot acc s).pc t = 86 ∧
    (sumSerialComponent ops values t slot acc s).indices t 16 = some ((slot+1 : Nat) : Int) ∧
    (sumSerialComponent ops values t slot acc s).regs t 10 = some (ops.add acc (values slot)) := by
  simp [sumSerialComponent,setIndex,setReg,record,advance]

theorem sum_serial_component_good (ops : Ops α) (values : Nat → α) (t slot : Nat) (acc : α) (s : State α)
    (ht : t%1024=0) (he : (s.epochs t).block=3) (good : ∀ a ∈ s.trace, Good a) :
    ∀ a ∈ (sumSerialComponent ops values t slot acc s).trace, Good a := by
  intro a ha
  simp only [sumSerialComponent,setIndex,setReg,record,advance,List.mem_cons] at ha
  rcases ha with rfl | ha
  · apply Good.serialAccess rfl rfl (by change 1 < 2; decide)
    · exact ht
    · change (s.epochs t).block = 3
      exact he
  · exact good a ha

structure SumSerialReady (ops : Ops α) (values : Nat → α) (t slot : Nat) (acc : α) (s : State α) : Prop where
  pc : s.pc t = 86
  counter : s.indices t 16 = some (slot : Int)
  accumulator : s.regs t 10 = some acc
  reads : SumSerialReads values t s

theorem sum_serial_component_ready (ops : Ops α) (values : Nat → α) (t slot : Nat) (acc : α)
    (s : State α) (ready : SumSerialReady ops values t slot acc s) :
    SumSerialReady ops values t (slot+1) (ops.add acc (values slot)) (sumSerialComponent ops values t slot acc s) := by
  have h := sum_serial_component_fields ops values t slot acc s
  exact ⟨h.1,h.2.1,h.2.2,by
    intro k hk
    rewrite [(sum_serial_component_frames ops values t slot acc s).1]
    exact ready.reads k hk⟩

def sumSerialFold (ops : Ops α) (values : Nat → α) (start : Nat) : Nat → α → α
  | 0,acc => acc
  | count+1,acc => sumSerialFold ops values (start+1) count (ops.add acc (values start))

def sumSerialComponents (ops : Ops α) (values : Nat → α) (t start : Nat) : Nat → α → State α → State α
  | 0,_,s => s
  | count+1,acc,s => sumSerialComponents ops values t (start+1) count (ops.add acc (values start))
      (sumSerialComponent ops values t start acc s)

theorem sum_serial_components_eq (p : Shape) (guarded : Bool) (ops : Ops α) (values : Nat → α)
    (t start count extra : Nat) (acc : α) (s : State α) (hn : start+count ≤ 32)
    (ready : SumSerialReady ops values t start acc s) :
    LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t (extra+5*count) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t extra
        (sumSerialComponents ops values t start count acc s) := by
  induction count generalizing start acc s with
  | zero => rfl
  | succ count ih =>
    rewrite [show extra+5*(count+1)=(extra+5*count)+5 by omega,
      sum_serial_component_eq p guarded ops values t start (extra+5*count) acc s
        (by omega) ready.pc ready.counter ready.accumulator ready.reads]
    exact ih (start+1) _ _ (by omega) (sum_serial_component_ready ops values t start acc s ready)

theorem sum_serial_components_ready (ops : Ops α) (values : Nat → α) (t start count : Nat)
    (acc : α) (s : State α) (ready : SumSerialReady ops values t start acc s) :
    SumSerialReady ops values t (start+count) (sumSerialFold ops values start count acc)
      (sumSerialComponents ops values t start count acc s) := by
  induction count generalizing start acc s with
  | zero => simpa only [sumSerialComponents,sumSerialFold,Nat.add_zero] using ready
  | succ count ih =>
    have h := ih (start+1) _ _ (sum_serial_component_ready ops values t start acc s ready)
    simpa only [sumSerialComponents,sumSerialFold,show start+1+count=start+(count+1) by omega] using h

theorem sum_serial_components_frames (ops : Ops α) (values : Nat → α) (t start count : Nat)
    (acc : α) (s : State α) :
    (sumSerialComponents ops values t start count acc s).memory = s.memory ∧
    (sumSerialComponents ops values t start count acc s).epochs = s.epochs ∧
    (sumSerialComponents ops values t start count acc s).trace.length = s.trace.length+count := by
  induction count generalizing start acc s with
  | zero => exact ⟨rfl,rfl,by simp [sumSerialComponents]⟩
  | succ count ih =>
    have head := sum_serial_component_frames ops values t start acc s
    have tail := ih (start+1) (ops.add acc (values start)) (sumSerialComponent ops values t start acc s)
    refine ⟨tail.1.trans head.1,tail.2.1.trans head.2.1,?_⟩
    change (sumSerialComponents ops values t (start+1) count _ _).trace.length = _
    rewrite [tail.2.2,head.2.2]
    omega

theorem sum_serial_components_good (ops : Ops α) (values : Nat → α) (t start count : Nat)
    (acc : α) (s : State α) (ht : t%1024=0) (he : (s.epochs t).block=3)
    (good : ∀ a ∈ s.trace, Good a) :
    ∀ a ∈ (sumSerialComponents ops values t start count acc s).trace, Good a := by
  induction count generalizing start acc s with
  | zero => exact good
  | succ count ih =>
    exact ih (start+1) _ _
      ((congrArg (fun epochs => (epochs t).block) (sum_serial_component_frames ops values t start acc s).2.1).trans he)
      (sum_serial_component_good ops values t start acc s ht he good)

#print axioms sum_serial_component_ready
#print axioms sum_serial_components_eq
#print axioms sum_serial_components_ready
#print axioms sum_serial_components_frames
#print axioms sum_serial_components_good
#print axioms sum_serial_read_location
#print axioms sum_serial_component_eq
#print axioms sum_serial_component_frames
#print axioms sum_serial_component_fields
#print axioms sum_serial_component_good
end LarkNativeSoftmax
