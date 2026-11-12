import Lark.NativeSglangRmsNormPairStep

/-! Four actual private half loads for one output pair. The original raw-half
caches and every read event survive. Conversion to the arithmetic domain occurs
exactly at the source's fromHalf instructions.
-/
namespace LarkNativeSglangRmsNorm
open LarkNonlinear
open LarkReduction (setReg)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def scaleWeight (ops : Ops α) (input : Nat → Nat → α) (tid iteration component : Nat) : α :=
  ops.fromHalf (input 2 (column tid iteration component))

theorem cached_weight_at (input : Nat → Nat → α) (tid iteration component t : Nat)
    (s : State α) (hi : iteration<2) (hc : component<8) (cached : WeightPrefix input tid 16 t s) :
    s.memory (privateCell t 1 (iteration*8+component))=some (input 2 (column tid iteration component)) := by
  have hd : (iteration*8+component)/8=iteration := by omega
  have hm : (iteration*8+component)%8=component := by omega
  simpa only [hd,hm] using cached (iteration*8+component) (by omega)

def scaleLoads (ops : Ops α) (input : Nat → Nat → α) (row tid iteration pair t : Nat) (s : State α) : State α :=
  let slot := iteration*8+pair*2
  let s := setReg (record s t (privateCell t 0 slot) false) t 13
    (pairLoaded ops input row tid iteration (pair*2)) 84
  let s := setReg (record s t (privateCell t 0 (slot+1)) false) t 14
    (pairLoaded ops input row tid iteration (pair*2+1)) 85
  let s := setReg (record s t (privateCell t 1 slot) false) t 15
    (scaleWeight ops input tid iteration (pair*2)) 86
  setReg (record s t (privateCell t 1 (slot+1)) false) t 16
    (scaleWeight ops input tid iteration (pair*2+1)) 87

theorem load_private_half_buffer (p : Shape) (ops : Ops α) (t buffer slot : Nat)
    (ix : Index) (s : State α) (value : α) (hb : buffer<3) (hs : slot<16)
    (hi : evalIndex (geometry p) t s ix=some (slot : Int))
    (hm : s.memory (privateCell t buffer slot)=some value) :
    evalExpr ops (layout p) (geometry p) t (.un .fromHalf (.load .local buffer ix)) s=
      some (ops.fromHalf value,record s t (privateCell t buffer slot) false) := by
  change s.memory ⟨.local,t,buffer,slot⟩=some value at hm
  simp only [evalExpr,hi,private_location p t buffer slot false hb hs,privateCell,hm,applyUnary,bind,pure,Option.bind]

theorem scale_loads_eq (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration pair t extra : Nat) (s : State α) (hi : iteration<2) (hp : pair<4)
    (hslot : s.indices t 18=some ((iteration*8+pair*2 : Nat) : Int)) (pc : s.pc t=83)
    (cached : InputPrefix input row tid 16 t s) (weights : WeightPrefix input tid 16 t s) :
    LarkCollective.runLane ops (layout p) (geometry p) (program true) t (extra+4) s=
    LarkCollective.runLane ops (layout p) (geometry p) (program true) t extra
      (scaleLoads ops input row tid iteration pair t s) := by
  let slot := iteration*8+pair*2
  let x := pairLoaded ops input row tid iteration (pair*2)
  let y := pairLoaded ops input row tid iteration (pair*2+1)
  let u := scaleWeight ops input tid iteration (pair*2)
  let v := scaleWeight ops input tid iteration (pair*2+1)
  let s1 := setReg (record s t (privateCell t 0 slot) false) t 13 x 84
  let s2 := setReg (record s1 t (privateCell t 0 (slot+1)) false) t 14 y 85
  let s3 := setReg (record s2 t (privateCell t 1 slot) false) t 15 u 86
  have hm0 := cached_input_at input row tid iteration (pair*2) t s hi (by omega) cached
  have hm1 := cached_input_at input row tid iteration (pair*2+1) t s hi (by omega) cached
  have hw0 := cached_weight_at input tid iteration (pair*2) t s hi (by omega) weights
  have hw1 := cached_weight_at input tid iteration (pair*2+1) t s hi (by omega) weights
  have read0 := load_private_half_buffer p ops t 0 slot (.ivar 18) s _ (by decide) (by omega) hslot hm0
  have e1 : execute ops (layout p) (geometry p) t (.assign 13 (.un .fromHalf (.load .local 0 (.ivar 18)))) s=some s1 := by
    simp only [execute,read0,bind,pure,Option.bind,pc]
    rfl
  have idx1 : s1.indices t 18=some (slot : Int) := hslot
  have plus1 := eval_nat_sum (geometry p) t slot 1 s1 (.ivar 18) (.const 1) idx1 rfl (by omega)
  have read1 := load_private_half_buffer p ops t 0 (slot+1) (.add (.ivar 18) (.const 1)) s1 _
    (by decide) (by omega) plus1 (by simpa only [slot,Nat.add_assoc] using hm1)
  have e2 : execute ops (layout p) (geometry p) t
      (.assign 14 (.un .fromHalf (.load .local 0 (.add (.ivar 18) (.const 1))))) s1=some s2 := by
    have pc1 : s1.pc t+1=85 := by simp [s1,setReg,advance]
    simp only [execute,read1,bind,pure,Option.bind,pc1]
    rfl
  have idx2 : s2.indices t 18=some (slot : Int) := hslot
  have read2 := load_private_half_buffer p ops t 1 slot (.ivar 18) s2 _ (by decide) (by omega) idx2 hw0
  have e3 : execute ops (layout p) (geometry p) t (.assign 15 (.un .fromHalf (.load .local 1 (.ivar 18)))) s2=some s3 := by
    have pc2 : s2.pc t+1=86 := by simp [s2,setReg,advance]
    simp only [execute,read2,bind,pure,Option.bind,pc2]
    rfl
  have idx3 : s3.indices t 18=some (slot : Int) := hslot
  have plus3 := eval_nat_sum (geometry p) t slot 1 s3 (.ivar 18) (.const 1) idx3 rfl (by omega)
  have read3 := load_private_half_buffer p ops t 1 (slot+1) (.add (.ivar 18) (.const 1)) s3 _
    (by decide) (by omega) plus3 (by simpa only [slot,Nat.add_assoc] using hw1)
  have e4 : execute ops (layout p) (geometry p) t
      (.assign 16 (.un .fromHalf (.load .local 1 (.add (.ivar 18) (.const 1))))) s3=
      some (scaleLoads ops input row tid iteration pair t s) := by
    have pc3 : s3.pc t+1=87 := by simp [s3,setReg,advance]
    simp only [execute,read3,bind,pure,Option.bind,pc3]
    rfl
  rw [scalar_step p true ops t 83 (extra+3) _ s s1 (by decide) pc e1]
  rw [scalar_step p true ops t 84 (extra+2) _ s1 s2 (by decide) (by simp [s1,setReg,advance]) e2]
  rw [scalar_step p true ops t 85 (extra+1) _ s2 s3 (by decide) (by simp [s2,setReg,advance]) e3]
  rw [scalar_step p true ops t 86 extra _ s3 _ (by decide) (by simp [s3,setReg,advance]) e4]

theorem scale_loads_fields (ops : Ops α) (input : Nat → Nat → α) (row tid iteration pair t : Nat) (s : State α) :
    (scaleLoads ops input row tid iteration pair t s).pc t=87 ∧
    (scaleLoads ops input row tid iteration pair t s).regs t 13=some (pairLoaded ops input row tid iteration (pair*2)) ∧
    (scaleLoads ops input row tid iteration pair t s).regs t 14=some (pairLoaded ops input row tid iteration (pair*2+1)) ∧
    (scaleLoads ops input row tid iteration pair t s).regs t 15=some (scaleWeight ops input tid iteration (pair*2)) ∧
    (scaleLoads ops input row tid iteration pair t s).regs t 16=some (scaleWeight ops input tid iteration (pair*2+1)) ∧
    (scaleLoads ops input row tid iteration pair t s).regs t 12=s.regs t 12 := by
  simp [scaleLoads,setReg,advance,record]

theorem scale_loads_preserves (ops : Ops α) (input : Nat → Nat → α) (row tid iteration pair t : Nat) (s : State α) :
    (scaleLoads ops input row tid iteration pair t s).memory=s.memory ∧
    (scaleLoads ops input row tid iteration pair t s).indices=s.indices ∧
    (scaleLoads ops input row tid iteration pair t s).epochs=s.epochs := ⟨rfl,rfl,rfl⟩

theorem scale_loads_other (ops : Ops α) (input : Nat → Nat → α) (row tid iteration pair t u : Nat)
    (s : State α) (hu : u≠t) :
    (scaleLoads ops input row tid iteration pair t s).pc u=s.pc u ∧
    (scaleLoads ops input row tid iteration pair t s).regs u=s.regs u := by
  simp [scaleLoads,setReg,advance,record,hu]

theorem scale_loads_trace (ops : Ops α) (input : Nat → Nat → α) (row tid iteration pair t : Nat) (s : State α) :
    let slot := iteration*8+pair*2
    (scaleLoads ops input row tid iteration pair t s).trace=
      ⟨t,privateCell t 1 (slot+1),false,s.epochs t⟩::⟨t,privateCell t 1 slot,false,s.epochs t⟩::
      ⟨t,privateCell t 0 (slot+1),false,s.epochs t⟩::⟨t,privateCell t 0 slot,false,s.epochs t⟩::s.trace := rfl

theorem scale_loads_good (ops : Ops α) (input : Nat → Nat → α) (row tid iteration pair t : Nat) (s : State α)
    (good : ∀ event∈s.trace,Good event) :
    ∀ event∈(scaleLoads ops input row tid iteration pair t s).trace,Good event := by
  intro event he
  rw [scale_loads_trace] at he
  rcases List.mem_cons.mp he with rfl | he
  · exact Good.localAccess rfl rfl
  rcases List.mem_cons.mp he with rfl | he
  · exact Good.localAccess rfl rfl
  rcases List.mem_cons.mp he with rfl | he
  · exact Good.localAccess rfl rfl
  rcases List.mem_cons.mp he with rfl | he
  · exact Good.localAccess rfl rfl
  · exact good event he

#print axioms load_private_half_buffer
#print axioms cached_weight_at
#print axioms scale_loads_eq
#print axioms scale_loads_fields
#print axioms scale_loads_preserves
#print axioms scale_loads_other
#print axioms scale_loads_trace
#print axioms scale_loads_good
end LarkNativeSglangRmsNorm
