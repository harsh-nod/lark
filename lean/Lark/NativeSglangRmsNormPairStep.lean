import Lark.NativeSglangRmsNormPairValue

/-! Ten actual scalar instructions for one cached half2 square pair. -/
namespace LarkNativeSglangRmsNorm
open LarkNonlinear
open LarkReduction (setIndex setReg execute_index_of execute_pure_of)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem eval_pair_slot (p : Shape) (t iteration pair : Nat) (s : State α)
    (hi : iteration < 2) (hc : pair < 4)
    (h13 : s.indices t 13 = some (iteration : Int)) (h14 : s.indices t 14 = some (pair : Int)) :
    evalIndex (geometry p) t s (.add (.mul (.ivar 13) (.const 8)) (.mul (.ivar 14) (.const 2))) =
      some ((iteration * 8 + pair * 2 : Nat) : Int) := by
  have hm := eval_nat_mul (geometry p) t iteration 8 s (.ivar 13) h13 (by decide) (by omega)
  have hp := eval_nat_mul (geometry p) t pair 2 s (.ivar 14) h14 (by decide) (by omega)
  exact eval_nat_sum (geometry p) t (iteration * 8) (pair * 2) s _ _ hm hp (by omega)

theorem load_private_half (p : Shape) (ops : Ops α) (t slot : Nat) (ix : Index)
    (s : State α) (value : α) (hs : slot < 16)
    (hindex : evalIndex (geometry p) t s ix = some (slot : Int))
    (hm : s.memory (privateCell t 0 slot) = some value) :
    evalExpr ops (layout p) (geometry p) t (.un .fromHalf (.load .local 0 ix)) s =
      some (ops.fromHalf value,record s t (privateCell t 0 slot) false) := by
  change s.memory ⟨.local,t,0,slot⟩ = some value at hm
  simp only [evalExpr,hindex,private_location p t 0 slot false (by decide) hs,
    privateCell,hm,applyUnary,bind,pure,Option.bind]

theorem pair_cycle (p : Shape) (repaired : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration pair t extra : Nat) (acc : α) (s : State α)
    (hi : iteration < 2) (hc : pair < 4)
    (h13 : s.indices t 13 = some (iteration : Int)) (h14 : s.indices t 14 = some (pair : Int))
    (ha : s.regs t 0 = some acc) (hp : s.pc t = 32)
    (cached : InputPrefix input row tid 16 t s) :
    LarkCollective.runLane ops (layout p) (geometry p) (program repaired) t (extra + 10) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program repaired) t extra
        (pairAfter ops input row tid iteration pair t acc s) := by
  let slot := iteration * 8 + pair * 2
  let x := pairLoaded ops input row tid iteration (pair * 2)
  let y := pairLoaded ops input row tid iteration (pair * 2 + 1)
  let s1 := advance s t 33
  let s2 := setIndex s1 t 15 (slot : Int) 34
  let s3 := setReg (record s2 t (privateCell t 0 slot) false) t 2 x 35
  let s4 := setReg (record s3 t (privateCell t 0 (slot + 1)) false) t 3 y 36
  let s5 := setReg s4 t 4 (ops.mul x x) 37
  let s6 := setReg s5 t 5 (ops.mul y y) 38
  let s7 := setReg s6 t 6 (pairSquare ops input row tid iteration pair) 39
  let s8 := setReg s7 t 0 (ops.add acc (pairSquare ops input row tid iteration pair)) 40
  let s9 := setIndex s8 t 14 ((pair + 1 : Nat) : Int) 41
  have pred := LarkReduction.predicate_lt_of (geometry p) t s (.ivar 14) (.const 4)
    (pair : Int) 4 h14 rfl (by omega)
  have e1 : execute ops (layout p) (geometry p) t (.branch (.lt (.ivar 14) (.const 4)) 42) s = some s1 := by
    simp only [execute,pred,hp,bind,pure,Option.bind]
    rfl
  have he2 := eval_pair_slot p t iteration pair s1 hi hc h13 h14
  have e2 := execute_index_of ops (layout p) (geometry p) t 15 34
    (.add (.mul (.ivar 13) (.const 8)) (.mul (.ivar 14) (.const 2))) s1 _ he2 (by simp [s1,advance])
  have idx2 : s2.indices t 15 = some (slot : Int) := by simp [s2,setIndex,advance]
  have hm0 := cached_input_at input row tid iteration (pair * 2) t s hi (by omega) cached
  have he3 := load_private_half p ops t slot (.ivar 15) s2
    (input 1 (address row (column tid iteration (pair * 2)))) (by omega) idx2 hm0
  have e3 : execute ops (layout p) (geometry p) t (.assign 2 (.un .fromHalf (.load .local 0 (.ivar 15)))) s2 = some s3 := by
    simp only [execute,he3,bind,pure,Option.bind]
    have hpc : s2.pc t + 1 = 35 := by simp [s2,setIndex,advance]
    rewrite [hpc]
    rfl
  have idx3 : s3.indices t 15 = some (slot : Int) := by simp [s3,s2,setReg,setIndex,record,advance]
  have he4idx := eval_nat_sum (geometry p) t slot 1 s3 (.ivar 15) (.const 1) idx3 rfl (by omega)
  have hm1 := cached_input_at input row tid iteration (pair * 2 + 1) t s hi (by omega) cached
  have he4 := load_private_half p ops t (slot + 1) (.add (.ivar 15) (.const 1)) s3
    (input 1 (address row (column tid iteration (pair * 2 + 1)))) (by omega) he4idx
    (by simpa only [slot,Nat.add_assoc] using hm1)
  have e4 : execute ops (layout p) (geometry p) t
      (.assign 3 (.un .fromHalf (.load .local 0 (.add (.ivar 15) (.const 1))))) s3 = some s4 := by
    simp only [execute,he4,bind,pure,Option.bind]
    have hpc : s3.pc t + 1 = 36 := by simp [s3,setReg,advance]
    rewrite [hpc]
    rfl
  have e5 := execute_pure_of ops (layout p) (geometry p) t 4 37 (.bin .mul (.reg 2) (.reg 2)) s4 (ops.mul x x)
    (by simp [evalExpr,applyBinary,s4,s3,setReg,record,advance]) (by simp [s4,setReg,advance])
  have e6 := execute_pure_of ops (layout p) (geometry p) t 5 38 (.bin .mul (.reg 3) (.reg 3)) s5 (ops.mul y y)
    (by simp [evalExpr,applyBinary,s5,s4,setReg,advance]) (by simp [s5,setReg,advance])
  have e7 := execute_pure_of ops (layout p) (geometry p) t 6 39 (.bin .add (.reg 4) (.reg 5)) s6
    (pairSquare ops input row tid iteration pair)
    (by simp [evalExpr,applyBinary,s6,s5,setReg,advance,pairSquare,x,y]) (by simp [s6,setReg,advance])
  have acc7 : s7.regs t 0 = some acc := by
    simp [s7,s6,s5,s4,s3,s2,s1,setReg,setIndex,record,advance,ha]
  have val7 : s7.regs t 6 = some (pairSquare ops input row tid iteration pair) := by simp [s7,setReg,advance]
  have e8 := execute_pure_of ops (layout p) (geometry p) t 0 40 (.bin .add (.reg 0) (.reg 6)) s7
    (ops.add acc (pairSquare ops input row tid iteration pair))
    (by simp only [evalExpr,applyBinary,acc7,val7,bind,pure,Option.bind]) (by simp [s7,setReg,advance])
  have idx8 : s8.indices t 14 = some (pair : Int) := by
    simp [s8,s7,s6,s5,s4,s3,s2,s1,setReg,setIndex,record,advance,h14]
  have he9 := eval_nat_sum (geometry p) t pair 1 s8 (.ivar 14) (.const 1) idx8 rfl (by omega)
  have e9 := execute_index_of ops (layout p) (geometry p) t 14 41
    (.add (.ivar 14) (.const 1)) s8 _ he9 (by simp [s8,setReg,advance])
  have e10 : execute ops (layout p) (geometry p) t (.jump 32) s9 =
      some (pairAfter ops input row tid iteration pair t acc s) := rfl
  rewrite [scalar_step p repaired ops t 32 _ _ s s1 (by cases repaired <;> decide) hp e1]
  rewrite [scalar_step p repaired ops t 33 _ _ s1 s2 (by cases repaired <;> decide) (by simp [s1,advance]) e2]
  rewrite [scalar_step p repaired ops t 34 _ _ s2 s3 (by cases repaired <;> decide) (by simp [s2,setIndex,advance]) e3]
  rewrite [scalar_step p repaired ops t 35 _ _ s3 s4 (by cases repaired <;> decide) (by simp [s3,setReg,advance]) e4]
  rewrite [scalar_step p repaired ops t 36 _ _ s4 s5 (by cases repaired <;> decide) (by simp [s4,setReg,advance]) e5]
  rewrite [scalar_step p repaired ops t 37 _ _ s5 s6 (by cases repaired <;> decide) (by simp [s5,setReg,advance]) e6]
  rewrite [scalar_step p repaired ops t 38 _ _ s6 s7 (by cases repaired <;> decide) (by simp [s6,setReg,advance]) e7]
  rewrite [scalar_step p repaired ops t 39 _ _ s7 s8 (by cases repaired <;> decide) (by simp [s7,setReg,advance]) e8]
  rewrite [scalar_step p repaired ops t 40 _ _ s8 s9 (by cases repaired <;> decide) (by simp [s8,setReg,advance]) e9]
  rewrite [scalar_step p repaired ops t 41 _ _ s9 _ (by cases repaired <;> decide) (by simp [s9,setIndex,advance]) e10]
  rfl

#print axioms eval_pair_slot
#print axioms load_private_half
#print axioms pair_cycle
end LarkNativeSglangRmsNorm
