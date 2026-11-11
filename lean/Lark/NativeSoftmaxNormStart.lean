import Lark.NativeSoftmaxExpOutput

/-! Actual normalization entry for both full sources. The shared total is read
at epoch4 and the owned-output data needed by later rounds is retained. This
module executes only PC93 and PC94, stopping at the outer test at PC95. -/
namespace LarkNativeSoftmax
open LarkNonlinear
open LarkReduction (setIndex setReg execute_index_of execute_pure_of)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def NormFuture (ops : Ops α) (input : Nat → Nat → α) (row tid start : Nat) (s : State α) : Prop :=
  ∀ iteration, start≤iteration → iteration<7 → ∀ component, component<8 →
    column tid iteration component<50257 →
    s.memory (globalCell 0 (address row (column tid iteration component)))=
      some (expOutputValue ops input row (column tid iteration component))

def NormPresent (row : Nat) (s : State α) : Prop :=
  ∀ col, col<50257 → ∃ value, s.memory (globalCell 0 (address row col))=some value

structure NormLaneEntry (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row tid : Nat) (s : State α) : Prop where
  valid : row<p.rows
  bound : tid<1024
  pc : s.pc (row*1024+tid)=93
  native : MaxNativeIndices (row*1024+tid) s
  total : s.memory ⟨.shared,row,1,0⟩=some (rowExpSum ops input row)
  epoch : (s.epochs (row*1024+tid)).block=4
  future : NormFuture ops input row tid 0 s
  present : NormPresent row s

structure NormRoundReady (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration : Nat) (s : State α) : Prop where
  valid : row<p.rows
  bound : tid<1024
  pc : s.pc (row*1024+tid)=95
  native : MaxNativeIndices (row*1024+tid) s
  base : s.indices (row*1024+tid) 17=some ((base tid iteration : Nat) : Int)
  denominator : s.regs (row*1024+tid) 12=some (rowExpSum ops input row)
  epoch : (s.epochs (row*1024+tid)).block=4
  future : NormFuture ops input row tid iteration s
  present : NormPresent row s

def normStart (ops : Ops α) (total : α) (t tid : Nat) (s : State α) : State α :=
  let s := setReg (record s t (sumPartialCell t 0) false) t 12 total 94
  setIndex s t 17 (tid : Int) 95

theorem norm_start_eq (p : Shape) (guarded : Bool) (ops : Ops α) (total : α)
    (t tid extra : Nat) (s : State α) (ht : tid<1024) (hp : s.pc t=93)
    (hi : s.indices t 1=some (tid : Int)) (hm : s.memory (sumPartialCell t 0)=some total) :
    LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t (extra+2) s=
      LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t extra (normStart ops total t tid s) := by
  let s1 := setReg (record s t (sumPartialCell t 0) false) t 12 total 94
  have load : evalExpr ops (layout p) (geometry p) t (.load .shared 1 (.const 0)) s=
      some (total,record s t (sumPartialCell t 0) false) := by
    simp only [sumPartialCell] at hm
    simp [evalExpr,evalIndex,int32,location,layout,geometry,sumPartialCell,hm]
  have e1 : execute ops (layout p) (geometry p) t (.assign 12 (.load .shared 1 (.const 0))) s=some s1 := by
    simp only [execute,load,hp,bind,pure,Option.bind]
    rfl
  have ix : evalIndex (geometry p) t s1 (.ivar 1)=some (tid : Int) := by
    simp only [evalIndex,show s1.indices=s.indices by rfl,hi]
  have e2 := execute_index_of ops (layout p) (geometry p) t 17 95 (.ivar 1) s1 (tid : Int) ix
    (by simp [s1,setReg,advance])
  rewrite [show extra+2=(extra+1)+1 by omega,
    scalar_step p guarded ops t 93 _ _ s s1 (by cases guarded <;> decide) hp e1]
  exact scalar_step p guarded ops t 94 _ _ s1 _ (by cases guarded <;> decide) (by simp [s1,setReg,advance]) e2

theorem norm_start_frames (ops : Ops α) (total : α) (t tid : Nat) (s : State α) :
    (normStart ops total t tid s).memory=s.memory ∧ (normStart ops total t tid s).epochs=s.epochs ∧
    (normStart ops total t tid s).trace=⟨t,sumPartialCell t 0,false,s.epochs t⟩::s.trace := by
  simp [normStart,setReg,setIndex,advance,record]

theorem norm_start_fields (ops : Ops α) (total : α) (t tid : Nat) (s : State α) :
    (normStart ops total t tid s).pc t=95 ∧ (normStart ops total t tid s).indices t 17=some (tid : Int) ∧
    (normStart ops total t tid s).regs t 12=some total := by
  simp [normStart,setReg,setIndex,advance,record]

theorem norm_start_native (ops : Ops α) (total : α) (t tid : Nat) (s : State α) (hi : MaxNativeIndices t s) :
    MaxNativeIndices t (normStart ops total t tid s) := by
  simpa only [MaxNativeIndices,normStart,setReg,setIndex,advance,record,↓reduceIte] using hi

theorem norm_future_memory (ops : Ops α) (input : Nat → Nat → α) (row tid iteration : Nat)
    (s next : State α) (hm : next.memory=s.memory) (hf : NormFuture ops input row tid iteration s) :
    NormFuture ops input row tid iteration next := by
  intro i hi hib c hc hcol
  rewrite [hm]
  exact hf i hi hib c hc hcol

theorem norm_present_memory (row : Nat) (s next : State α) (hm : next.memory=s.memory) (hp : NormPresent row s) :
    NormPresent row next := by
  intro col hc
  rewrite [hm]
  exact hp col hc

theorem norm_start_ready (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid : Nat) (s : State α) (entry : NormLaneEntry p ops input row tid s) :
    NormRoundReady p ops input row tid 0 (normStart ops (rowExpSum ops input row) (row*1024+tid) tid s) := by
  have hf := norm_start_frames ops (rowExpSum ops input row) (row*1024+tid) tid s
  have hs := norm_start_fields ops (rowExpSum ops input row) (row*1024+tid) tid s
  exact {
    valid := entry.valid
    bound := entry.bound
    pc := hs.1
    native := norm_start_native ops _ (row*1024+tid) tid s entry.native
    base := by simpa only [base,Nat.zero_mul,Nat.add_zero] using hs.2.1
    denominator := hs.2.2
    epoch := (congrArg (fun epochs => (epochs (row*1024+tid)).block) hf.2.1).trans entry.epoch
    future := norm_future_memory ops input row tid 0 s _ hf.1 entry.future
    present := norm_present_memory row s _ hf.1 entry.present }

theorem norm_start_good (ops : Ops α) (total : α) (t tid : Nat) (s : State α)
    (he : (s.epochs t).block=4) (good : ∀ a ∈ s.trace, Good a) :
    ∀ a ∈ (normStart ops total t tid s).trace, Good a := by
  intro a ha
  rewrite [(norm_start_frames ops total t tid s).2.2] at ha
  rcases List.mem_cons.mp ha with h | h
  · subst a
    apply Good.broadcastRead rfl rfl (by change 1<2; decide) rfl
    · change (s.epochs t).block=4
      exact he
    · rfl
  · exact good a h

theorem norm_entry_of_sum (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid : Nat) (s : State α) (ht : tid<1024) (ready : SumReady p ops input row s)
    (outputs : ExpOutputRow ops input row s) : NormLaneEntry p ops input row tid s := by
  exact {
    valid := ready.valid
    bound := ht
    pc := ready.pc tid ht
    native := ready.indices tid ht
    total := ready.total
    epoch := ready.epoch tid ht
    future := fun _ _ _ _ _ hc => outputs _ hc
    present := fun col hc => ⟨expOutputValue ops input row col,outputs col hc⟩ }

theorem initial_norm_entry (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row tid : Nat) (hr : row<p.rows) (ht : tid<1024) :
    NormLaneEntry p ops input row tid (sumState p ops input row (initial (layout p) input outside)) :=
  norm_entry_of_sum p ops input row tid _ ht (initial_sum_ready p ops input outside row hr)
    (sum_state_outputs p ops input row (initial (layout p) input outside))

#print axioms norm_start_eq
#print axioms norm_start_frames
#print axioms norm_start_fields
#print axioms norm_start_native
#print axioms norm_future_memory
#print axioms norm_present_memory
#print axioms norm_start_ready
#print axioms norm_start_good
#print axioms norm_entry_of_sum
#print axioms initial_norm_entry
end LarkNativeSoftmax
