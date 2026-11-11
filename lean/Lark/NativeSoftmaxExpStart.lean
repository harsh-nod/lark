import Lark.NativeSoftmaxMaximum

/-! Actual entry to the exponentiation/sum pass. Each lane broadcasts the
stored maximum, initializes its scalar sum, and copies its native thread index.
This lemma consumes exactly three source instructions; it does not run the
subsequent input-buffer or exponential loops. -/
namespace LarkNativeSoftmax
open LarkNonlinear
open LarkReduction (setIndex setReg execute_index_of execute_pure_of)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def expStart (ops : Ops α) (offset : α) (t tid : Nat) (s : State α) : State α :=
  let s := setReg (record s t (partialCell t 0) false) t 5 offset 44
  let s := setReg s t 6 (ops.literal 0 1) 45
  setIndex s t 9 (tid : Int) 46

theorem exp_start_eq (p : Shape) (guarded : Bool) (ops : Ops α) (offset : α)
    (t tid extra : Nat) (s : State α) (hp : s.pc t=43)
    (htid : s.indices t 1=some (tid : Int))
    (hm : s.memory (partialCell t 0)=some offset) :
    LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t (extra+3) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t extra (expStart ops offset t tid s) := by
  let s1 := setReg (record s t (partialCell t 0) false) t 5 offset 44
  let s2 := setReg s1 t 6 (ops.literal 0 1) 45
  have load : evalExpr ops (layout p) (geometry p) t (.load .shared 0 (.const 0)) s =
      some (offset,record s t (partialCell t 0) false) := by
    simp only [partialCell] at hm
    simp [evalExpr,evalIndex,int32,location,layout,geometry,partialCell,hm]
  have e1 : execute ops (layout p) (geometry p) t (.assign 5 (.load .shared 0 (.const 0))) s = some s1 := by
    simp only [execute,load,bind,pure,Option.bind]
    rewrite [hp]
    rfl
  have e2 := execute_pure_of ops (layout p) (geometry p) t 6 45 (.lit 0 1) s1 (ops.literal 0 1)
    (by simp [evalExpr]) (by simp [s1,setReg,advance])
  change execute _ _ _ _ _ s1=some s2 at e2
  have e3 := execute_index_of ops (layout p) (geometry p) t 9 46 (.ivar 1) s2 (tid : Int)
    (by simpa [s2,s1,setReg,record,advance,evalIndex] using htid)
    (by simp [s2,setReg,advance])
  change execute _ _ _ _ _ s2=some (expStart ops offset t tid s) at e3
  rewrite [show extra+3=(extra+2)+1 by omega,
    scalar_step p guarded ops t 43 _ _ s s1 (by cases guarded <;> decide) hp e1]
  rewrite [show extra+2=(extra+1)+1 by omega,
    scalar_step p guarded ops t 44 _ _ s1 s2 (by cases guarded <;> decide) (by simp [s1,setReg,advance]) e2]
  rewrite [scalar_step p guarded ops t 45 _ _ s2 _ (by cases guarded <;> decide)
    (by simp [s2,setReg,advance]) e3]
  rfl

theorem exp_start_fields (ops : Ops α) (offset : α) (t tid : Nat) (s : State α) :
    (expStart ops offset t tid s).pc t=46 ∧
    (expStart ops offset t tid s).indices t 9=some (tid : Int) ∧
    (expStart ops offset t tid s).regs t 5=some offset ∧
    (expStart ops offset t tid s).regs t 6=some (ops.literal 0 1) := by
  simp [expStart,setIndex,setReg,record,advance]

theorem exp_start_frames (ops : Ops α) (offset : α) (t tid : Nat) (s : State α) :
    (expStart ops offset t tid s).memory=s.memory ∧
    (expStart ops offset t tid s).epochs=s.epochs ∧
    (expStart ops offset t tid s).trace=
      ⟨t,partialCell t 0,false,s.epochs t⟩::s.trace := by
  simp [expStart,setIndex,setReg,record,advance]

theorem exp_start_index_other (ops : Ops α) (offset : α) (t tid u r : Nat) (s : State α)
    (hr : r ≠ 9) : (expStart ops offset t tid s).indices u r=s.indices u r := by
  simp [expStart,setIndex,setReg,record,advance,hr]

theorem exp_start_other (ops : Ops α) (offset : α) (t tid u : Nat) (s : State α) (hu : u ≠ t) :
    OtherThread t u s (expStart ops offset t tid s) := by
  simp [OtherThread,expStart,setIndex,setReg,record,advance,hu]

theorem exp_start_good (ops : Ops α) (offset : α) (t tid : Nat) (s : State α)
    (he : (s.epochs t).block=2) (good : ∀ a ∈ s.trace, Good a) :
    ∀ a ∈ (expStart ops offset t tid s).trace, Good a := by
  intro a ha
  rewrite [(exp_start_frames ops offset t tid s).2.2] at ha
  rcases List.mem_cons.mp ha with rfl | ha
  · apply Good.broadcastRead rfl rfl (by change 0<2; decide) rfl
    · change (s.epochs t).block=2*0+2
      omega
    · rfl
  · exact good a ha

structure ExpEntry (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (offset : α)
    (row tid t : Nat) (s : State α) : Prop where
  pc : s.pc t=46
  rowIndex : s.indices t 0=some (row : Int)
  tidIndex : s.indices t 1=some (tid : Int)
  baseIndex : s.indices t 9=some ((base tid 0 : Nat) : Int)
  maximum : s.regs t 5=some offset
  accumulator : s.regs t 6=some (ops.literal 0 1)
  reads : Reads p input s
  good : ∀ a ∈ s.trace, Good a

theorem exp_start_ready (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (offset : α)
    (row tid t : Nat) (s : State α) (hrow : s.indices t 0=some (row : Int))
    (htid : s.indices t 1=some (tid : Int)) (reads : Reads p input s)
    (he : (s.epochs t).block=2) (good : ∀ a ∈ s.trace, Good a) :
    ExpEntry p ops input offset row tid t (expStart ops offset t tid s) := by
  obtain ⟨hp,hi,hm,ha⟩ := exp_start_fields ops offset t tid s
  exact {
    pc := hp
    rowIndex := (exp_start_index_other ops offset t tid t 0 s (by decide)).trans hrow
    tidIndex := (exp_start_index_other ops offset t tid t 1 s (by decide)).trans htid
    baseIndex := by simpa only [base,Nat.zero_mul,Nat.add_zero] using hi
    maximum := hm
    accumulator := ha
    reads := by intro i hb; rewrite [(exp_start_frames ops offset t tid s).1]; exact reads i hb
    good := exp_start_good ops offset t tid s he good }

theorem exp_start_maximum_eq (p : Shape) (guarded : Bool) (ops : Ops α)
    (input : Nat → Nat → α) (row tid extra : Nat) (s : State α)
    (ready : MaximumReady p ops input row s) (ht : tid<1024) :
    LarkCollective.runLane ops (layout p) (geometry p) (program guarded) (row*1024+tid) (extra+3) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program guarded) (row*1024+tid) extra
        (expStart ops (rowMaximum ops input row) (row*1024+tid) tid s) := by
  apply exp_start_eq p guarded ops _ _ _ _ s (ready.pc tid ht)
  · simpa only [show (row*1024+tid)%1024=tid by omega] using (ready.indices tid ht).2.1
  · simpa only [partialCell,show (row*1024+tid)/1024=row by omega] using ready.maximum

theorem exp_start_maximum_ready (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid : Nat) (s : State α) (ready : MaximumReady p ops input row s) (ht : tid<1024) :
    ExpEntry p ops input (rowMaximum ops input row) row tid (row*1024+tid)
      (expStart ops (rowMaximum ops input row) (row*1024+tid) tid s) := by
  apply exp_start_ready p ops input _ row tid (row*1024+tid) s
  · simpa only [show (row*1024+tid)/1024=row by omega] using (ready.indices tid ht).1
  · simpa only [show (row*1024+tid)%1024=tid by omega] using (ready.indices tid ht).2.1
  · exact ready.reads
  · exact ready.epoch tid ht
  · exact ready.good

#print axioms exp_start_eq
#print axioms exp_start_fields
#print axioms exp_start_frames
#print axioms exp_start_index_other
#print axioms exp_start_other
#print axioms exp_start_good
#print axioms exp_start_ready
#print axioms exp_start_maximum_eq
#print axioms exp_start_maximum_ready
end LarkNativeSoftmax
