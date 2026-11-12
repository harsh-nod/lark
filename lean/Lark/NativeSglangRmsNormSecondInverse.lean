import Lark.NativeSglangRmsNormSecondSnapshots

/-! The second reduction's actual final addition, mean/epsilon/rsqrt, and
one distinct shared inverse store per participating lane. Values are kept
lane-specific for arbitrary Ops; no algebraic reassociation is assumed.
-/
namespace LarkNativeSglangRmsNorm
open LarkNonlinear LarkCollective
open LarkReduction (setReg execute_pure_of)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def secondInverseValue (ops : Ops α) (total : α) : α :=
  ops.rsqrt (ops.add (ops.div total (ops.literal 16384 1)) (ops.literal 1 100000))

def inverseTail (ops : Ops α) (t tid : Nat) (a b : α) (s : State α) : State α :=
  let total := ops.add a b
  let mean := ops.div total (ops.literal 16384 1)
  let variance := ops.add mean (ops.literal 1 100000)
  let s := setReg s t 7 total 72
  let s := setReg s t 9 mean 73
  let s := setReg s t 10 variance 74
  let s := setReg s t 11 (ops.rsqrt variance) 75
  partialWrite t 76 tid (ops.rsqrt variance) s

theorem inverse_store_execute (p : Shape) (ops : Ops α) (t tid : Nat) (value : α) (s : State α)
    (ht : tid<32) (hi : s.indices t 1=some (tid : Int))
    (ha : s.regs t 11=some value) (hp : s.pc t=75) :
    execute ops (layout p) (geometry p) t (.store .shared 0 (.ivar 1) (.reg 11)) s=
      some (partialWrite t 76 tid value s) := by
  simp [execute,evalIndex,hi,partial_slot_location p t tid ht,evalExpr,ha,hp,partialWrite,record]

theorem inverse_tail_lane (p : Shape) (ops : Ops α) (t tid extra : Nat) (a b : α) (s : State α)
    (ht : tid<32) (hi : s.indices t 1=some (tid : Int)) (hp : s.pc t=71)
    (ha : s.regs t 7=some a) (hb : s.regs t 8=some b) :
    LarkCollective.runLane ops (layout p) (geometry p) (program true) t (extra+6) s=
      some (inverseTail ops t tid a b s) := by
  let total := ops.add a b
  let mean := ops.div total (ops.literal 16384 1)
  let variance := ops.add mean (ops.literal 1 100000)
  let s1 := setReg s t 7 total 72
  let s2 := setReg s1 t 9 mean 73
  let s3 := setReg s2 t 10 variance 74
  let s4 := setReg s3 t 11 (ops.rsqrt variance) 75
  have h1 := execute_pure_of ops (layout p) (geometry p) t 7 72
    (.bin .add (.reg 7) (.reg 8)) s total (by simp [evalExpr,applyBinary,ha,hb,total]) (by omega)
  have h2 := execute_pure_of ops (layout p) (geometry p) t 9 73
    (.bin .div (.reg 7) (.lit 16384 1)) s1 mean
    (by simp [evalExpr,applyBinary,s1,setReg,advance,mean]) (by simp [s1,setReg,advance])
  have h3 := execute_pure_of ops (layout p) (geometry p) t 10 74
    (.bin .add (.reg 9) (.lit 1 100000)) s2 variance
    (by simp [evalExpr,applyBinary,s2,setReg,advance,variance]) (by simp [s2,setReg,advance])
  have h4 := execute_pure_of ops (layout p) (geometry p) t 11 75
    (.un .rsqrt (.reg 10)) s3 (ops.rsqrt variance)
    (by simp [evalExpr,applyUnary,s3,setReg,advance]) (by simp [s3,setReg,advance])
  have h5 := inverse_store_execute p ops t tid (ops.rsqrt variance) s4 ht hi
    (by simp [s4,setReg,advance]) (by simp [s4,setReg,advance])
  rw [scalar_step p true ops t 71 (extra+5) _ s s1 (by decide) hp h1]
  rw [scalar_step p true ops t 72 (extra+4) _ s1 s2 (by decide) (by simp [s1,setReg,advance]) h2]
  rw [scalar_step p true ops t 73 (extra+3) _ s2 s3 (by decide) (by simp [s2,setReg,advance]) h3]
  rw [scalar_step p true ops t 74 (extra+2) _ s3 s4 (by decide) (by simp [s3,setReg,advance]) h4]
  rw [scalar_step p true ops t 75 (extra+1) _ s4 _ (by decide) (by simp [s4,setReg,advance]) h5]
  have parked : LarkCollective.parked (program true)
      (partialWrite t 76 tid (ops.rsqrt variance) s4) t=some .block := by
    have code : (program true)[76]?=some (.scalar (.barrier .block)) := by decide
    simp only [LarkCollective.parked,partialWrite,advance,↓reduceIte,code,scalarCut]
  rw [LarkCollective.runLane,parked]
  rfl

theorem inverse_tail_fields (ops : Ops α) (t tid : Nat) (a b : α) (s : State α) :
    (inverseTail ops t tid a b s).pc t=76 ∧
    (inverseTail ops t tid a b s).regs t 7=some (ops.add a b) ∧
    (inverseTail ops t tid a b s).regs t 11=some (secondInverseValue ops (ops.add a b)) ∧
    (inverseTail ops t tid a b s).indices=s.indices ∧ (inverseTail ops t tid a b s).epochs=s.epochs := by
  simp [inverseTail,secondInverseValue,partialWrite,setReg,advance,record]

theorem inverse_tail_other (ops : Ops α) (t tid u : Nat) (a b : α) (s : State α) (hu : u≠t) :
    (inverseTail ops t tid a b s).pc u=s.pc u ∧
    (inverseTail ops t tid a b s).regs u=s.regs u := by
  simp [inverseTail,partialWrite,setReg,advance,record,hu]

theorem inverse_tail_memory (ops : Ops α) (t tid : Nat) (a b : α) (s : State α) (l : Location)
    (hl : l≠partialSlot t tid) :
    (inverseTail ops t tid a b s).memory l=s.memory l := by
  simp [inverseTail,partialWrite,setReg,advance,record,hl]

theorem inverse_tail_written_value (ops : Ops α) (t tid : Nat) (a b : α) (s : State α) :
    (inverseTail ops t tid a b s).memory (partialSlot t tid)=some (secondInverseValue ops (ops.add a b)) := by
  simp [inverseTail,secondInverseValue,partialWrite,setReg,advance,record]

theorem inverse_tail_trace (ops : Ops α) (t tid : Nat) (a b : α) (s : State α) :
    (inverseTail ops t tid a b s).trace=⟨t,partialSlot t tid,true,s.epochs t⟩::s.trace := by
  simp [inverseTail,partialWrite,setReg,advance,record]

theorem inverse_tail_good (ops : Ops α) (t : Nat) (a b : α) (s : State α)
    (epoch : (s.epochs t).block=1) (good : ∀ event∈s.trace,Good event) :
    ∀ event∈(inverseTail ops t (t%1024) a b s).trace,Good event := by
  intro event he
  rw [inverse_tail_trace] at he
  rcases List.mem_cons.mp he with rfl | he
  · exact Good.inverseStore rfl rfl rfl rfl epoch rfl
  · exact good event he

#print axioms inverse_store_execute
#print axioms inverse_tail_lane
#print axioms inverse_tail_fields
#print axioms inverse_tail_other
#print axioms inverse_tail_memory
#print axioms inverse_tail_written_value
#print axioms inverse_tail_trace
#print axioms inverse_tail_good
end LarkNativeSglangRmsNorm
