import Lark.NativeSglangRmsNormScaleStore

/-! One actual fourteen-instruction output half2 cycle, including its counted
loop branch, slot calculation and back edge. Execution has no trace-safety
premise; memory values, frames and access classification are proved separately.
-/
namespace LarkNativeSglangRmsNorm
open LarkNonlinear
open LarkReduction (setIndex setReg execute_index_of)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def outputScaled (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component : Nat) (inverse : α) : α :=
  scaleProduct ops (pairLoaded ops input row tid iteration component)
    (scaleWeight ops input tid iteration component) inverse

def scaleStart (iteration pair t : Nat) (s : State α) : State α :=
  setIndex (advance s t 82) t 18 ((iteration*8+pair*2 : Nat) : Int) 83
def scaleEnd (pair t : Nat) (s : State α) : State α :=
  advance (setIndex s t 17 ((pair+1 : Nat) : Int) 94) t 81
def scalePairAfter (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration pair t : Nat) (inverse : α) (s : State α) : State α :=
  scaleEnd pair t (scaleCompute ops t (iteration*8+pair*2)
    (pairLoaded ops input row tid iteration (pair*2))
    (pairLoaded ops input row tid iteration (pair*2+1))
    (scaleWeight ops input tid iteration (pair*2))
    (scaleWeight ops input tid iteration (pair*2+1)) inverse
    (scaleLoads ops input row tid iteration pair t (scaleStart iteration pair t s)))

theorem scale_pair_cycle (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration pair t extra : Nat) (inverse : α) (s : State α)
    (hi : iteration<2) (hc : pair<4) (hp : s.pc t=81)
    (h16 : s.indices t 16=some (iteration : Int)) (h17 : s.indices t 17=some (pair : Int))
    (h12 : s.regs t 12=some inverse)
    (cached : InputPrefix input row tid 16 t s) (weights : WeightPrefix input tid 16 t s) :
    LarkCollective.runLane ops (layout p) (geometry p) (program true) t (extra+14) s=
    LarkCollective.runLane ops (layout p) (geometry p) (program true) t extra
      (scalePairAfter ops input row tid iteration pair t inverse s) := by
  let start := scaleStart iteration pair t s
  let loaded := scaleLoads ops input row tid iteration pair t start
  let computed := scaleCompute ops t (iteration*8+pair*2)
    (pairLoaded ops input row tid iteration (pair*2))
    (pairLoaded ops input row tid iteration (pair*2+1))
    (scaleWeight ops input tid iteration (pair*2))
    (scaleWeight ops input tid iteration (pair*2+1)) inverse loaded
  let incremented := setIndex computed t 17 ((pair+1 : Nat) : Int) 94
  have pred := LarkReduction.predicate_lt_of (geometry p) t s (.ivar 17) (.const 4)
    (pair : Int) 4 h17 rfl (by omega)
  have e1 : execute ops (layout p) (geometry p) t (.branch (.lt (.ivar 17) (.const 4)) 95) s=
      some (advance s t 82) := by simp [execute,pred,hp]
  have hm := eval_nat_mul (geometry p) t iteration 8 (advance s t 82) (.ivar 16) h16 (by decide) (by omega)
  have hc2 := eval_nat_mul (geometry p) t pair 2 (advance s t 82) (.ivar 17) h17 (by decide) (by omega)
  have he := eval_nat_sum (geometry p) t (iteration*8) (pair*2) (advance s t 82) _ _ hm hc2 (by omega)
  have e2 := execute_index_of ops (layout p) (geometry p) t 18 83
    (.add (.mul (.ivar 16) (.const 8)) (.mul (.ivar 17) (.const 2))) (advance s t 82) _ he (by simp [advance])
  have startslot : start.indices t 18=some ((iteration*8+pair*2 : Nat) : Int) := by simp [start,scaleStart,setIndex,advance]
  have loads := scale_loads_eq p ops input row tid iteration pair t (extra+8) start hi hc startslot
    (by simp [start,scaleStart,setIndex,advance]) cached weights
  have hl := scale_loads_fields ops input row tid iteration pair t start
  have compute := scale_compute_eq p ops t (iteration*8+pair*2) (extra+2) _ _ _ _ inverse loaded (by omega)
    startslot hl.1 hl.2.1 hl.2.2.1 hl.2.2.2.1 hl.2.2.2.2.1 (hl.2.2.2.2.2.trans h12)
  have hcomp := scale_compute_fields ops t (iteration*8+pair*2)
    (pairLoaded ops input row tid iteration (pair*2))
    (pairLoaded ops input row tid iteration (pair*2+1))
    (scaleWeight ops input tid iteration (pair*2))
    (scaleWeight ops input tid iteration (pair*2+1)) inverse loaded
  have idx : computed.indices t 17=some (pair : Int) := by
    rw [hcomp.2.2.1,(scale_loads_preserves ops input row tid iteration pair t start).2.1]
    simpa [start,scaleStart,setIndex,advance] using h17
  have plus := eval_nat_sum (geometry p) t pair 1 computed (.ivar 17) (.const 1) idx rfl (by omega)
  have e13 := execute_index_of ops (layout p) (geometry p) t 17 94 (.add (.ivar 17) (.const 1))
    computed _ plus (by have h : computed.pc t=93 := hcomp.1; omega)
  have e14 : execute ops (layout p) (geometry p) t (.jump 81) incremented=
      some (scalePairAfter ops input row tid iteration pair t inverse s) := rfl
  rw [scalar_step p true ops t 81 (extra+13) _ s _ (by decide) hp e1]
  rw [scalar_step p true ops t 82 (extra+12) _ _ start (by decide) (by simp [advance]) e2]
  rw [show extra+12=(extra+8)+4 by omega,loads]
  rw [show extra+8=(extra+2)+6 by omega,compute]
  rw [scalar_step p true ops t 93 (extra+1) _ computed incremented (by decide) hcomp.1 e13]
  rw [scalar_step p true ops t 94 extra _ incremented _ (by decide) (by simp [incremented,setIndex,advance]) e14]

theorem scale_pair_fields (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration pair t : Nat) (inverse : α) (s : State α) :
    (scalePairAfter ops input row tid iteration pair t inverse s).pc t=81 ∧
    (scalePairAfter ops input row tid iteration pair t inverse s).indices t 0=s.indices t 0 ∧
    (scalePairAfter ops input row tid iteration pair t inverse s).indices t 1=s.indices t 1 ∧
    (scalePairAfter ops input row tid iteration pair t inverse s).indices t 16=s.indices t 16 ∧
    (scalePairAfter ops input row tid iteration pair t inverse s).indices t 17=some ((pair+1 : Nat) : Int) ∧
    (scalePairAfter ops input row tid iteration pair t inverse s).regs t 12=s.regs t 12 ∧
    (scalePairAfter ops input row tid iteration pair t inverse s).epochs=s.epochs := by
  simp [scalePairAfter,scaleStart,scaleEnd,scaleCompute,scaleLoads,setReg,setIndex,advance,record,cacheWritten]

theorem scale_pair_memory (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration pair t : Nat) (inverse : α) (s : State α) (l : Location) :
    (scalePairAfter ops input row tid iteration pair t inverse s).memory l=
      if l=privateCell t 2 (iteration*8+pair*2+1) then some (outputScaled ops input row tid iteration (pair*2+1) inverse)
      else if l=privateCell t 2 (iteration*8+pair*2) then some (outputScaled ops input row tid iteration (pair*2) inverse)
      else s.memory l := rfl

theorem scale_pair_written (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration pair t : Nat) (inverse : α) (s : State α) :
    (scalePairAfter ops input row tid iteration pair t inverse s).memory (privateCell t 2 (iteration*8+pair*2))=
      some (outputScaled ops input row tid iteration (pair*2) inverse) ∧
    (scalePairAfter ops input row tid iteration pair t inverse s).memory (privateCell t 2 (iteration*8+pair*2+1))=
      some (outputScaled ops input row tid iteration (pair*2+1) inverse) := by
  simp [scale_pair_memory,privateCell]

theorem scale_pair_other (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration pair t u : Nat) (inverse : α) (s : State α) (hu : u≠t) :
    (scalePairAfter ops input row tid iteration pair t inverse s).pc u=s.pc u ∧
    (scalePairAfter ops input row tid iteration pair t inverse s).indices u=s.indices u ∧
    (scalePairAfter ops input row tid iteration pair t inverse s).regs u=s.regs u := by
  simp [scalePairAfter,scaleStart,scaleEnd,scaleCompute,scaleLoads,setReg,setIndex,advance,record,cacheWritten,hu]

theorem scale_pair_trace (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration pair t : Nat) (inverse : α) (s : State α) :
    let slot := iteration*8+pair*2
    (scalePairAfter ops input row tid iteration pair t inverse s).trace=
      ⟨t,privateCell t 2 (slot+1),true,s.epochs t⟩::⟨t,privateCell t 2 slot,true,s.epochs t⟩::
      ⟨t,privateCell t 1 (slot+1),false,s.epochs t⟩::⟨t,privateCell t 1 slot,false,s.epochs t⟩::
      ⟨t,privateCell t 0 (slot+1),false,s.epochs t⟩::⟨t,privateCell t 0 slot,false,s.epochs t⟩::s.trace := rfl

theorem scale_pair_good (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration pair t : Nat) (inverse : α) (s : State α) (good : ∀ event∈s.trace,Good event) :
    ∀ event∈(scalePairAfter ops input row tid iteration pair t inverse s).trace,Good event := by
  intro event he
  rw [scale_pair_trace] at he
  rcases List.mem_cons.mp he with rfl | he
  · exact Good.localAccess rfl rfl
  rcases List.mem_cons.mp he with rfl | he
  · exact Good.localAccess rfl rfl
  rcases List.mem_cons.mp he with rfl | he
  · exact Good.localAccess rfl rfl
  rcases List.mem_cons.mp he with rfl | he
  · exact Good.localAccess rfl rfl
  rcases List.mem_cons.mp he with rfl | he
  · exact Good.localAccess rfl rfl
  rcases List.mem_cons.mp he with rfl | he
  · exact Good.localAccess rfl rfl
  · exact good event he

#print axioms scale_pair_cycle
#print axioms scale_pair_fields
#print axioms scale_pair_memory
#print axioms scale_pair_written
#print axioms scale_pair_other
#print axioms scale_pair_trace
#print axioms scale_pair_good
end LarkNativeSglangRmsNorm
