import Lark.PairMap

/-! FP32 SiLU(gate)*up with one FP16 store per scalar lane. -/
namespace LarkSwiPointwise
open LarkNonlinear
open LarkReduction (setIndex setReg execute_index_of int32_cast)
set_option maxRecDepth 10000
set_option maxHeartbeats 20000000

def body : Expr := .un .toHalf (.bin .mul
  (.bin .mul (.reg 0) (.bin .div (.lit 1 1)
    (.bin .add (.lit 1 1) (.un .exp (.bin .sub (.lit 0 1) (.reg 0)))))) (.reg 1))
def value (ops : Ops α) (a b : α) : α :=
  ops.toHalf (ops.mul (ops.mul a (ops.div (ops.literal 1 1) (ops.add (ops.literal 1 1)
    (ops.exp (ops.sub (ops.literal 0 1) a))))) b)
def program : List Instr :=
  [.index 0 .bid,.assign 0 (.load .global 0 (.ivar 0)),
   .assign 1 (.load .global 1 (.ivar 0)),.store .global 2 (.ivar 0) body,.halt]
def indexed (t : Nat) (s : State α) : State α := setIndex s t 0 (t : Int) 1
def loaded (input : Nat → Nat → α) (t : Nat) (s : State α) : State α :=
  let s:=setReg (record (indexed t s) t (LarkPairMap.cell 0 t) false) t 0 (input 0 t) 2
  setReg (record s t (LarkPairMap.cell 1 t) false) t 1 (input 1 t) 3
def after (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) : State α :=
  let s:=loaded input t s
  advance {record s t (LarkPairMap.cell 2 t) true with
    memory:=fun l=>if l=LarkPairMap.cell 2 t then some (value ops (input 0 t) (input 1 t)) else s.memory l} t 4

theorem load_eq (ops : Ops α) (n w t b : Nat) (s : State α) (input : Nat → Nat → α)
    (hb : b<2) (ht : t<n) (hi : s.indices t 0=some (t : Int)) (hr : LarkPairMap.Reads n input s) :
    evalExpr ops (LarkPairMap.layout n) (LarkPairMap.geometry n w) t (.load .global b (.ivar 0)) s=
      some (input b t,record s t (LarkPairMap.cell b t) false) := by
  have hl : location (LarkPairMap.layout n) (LarkPairMap.geometry n w) t .global b (t : Int) false=
      some (LarkPairMap.cell b t) := by
    have hneg : ¬(t : Int)<0 := by omega
    rcases (show b=0 ∨ b=1 by omega) with rfl|rfl <;>
      simp [location,LarkPairMap.layout,LarkPairMap.cell,hneg,ht]
  simp only [evalExpr,evalIndex,hi,bind,pure,Option.bind,hl,hr b hb t ht]

theorem assign_of (ops : Ops α) (l : Layout) (g : Geometry) (t r pc : Nat)
    (e : Expr) (s s1 : State α) (x : α) (he : evalExpr ops l g t e s=some (x,s1))
    (hp : s.pc t+1=pc) : execute ops l g t (.assign r e) s=some (setReg s1 t r x pc) := by
  simp only [execute,he,hp,bind,pure,Option.bind];rfl

theorem lane_eq (ops : Ops α) (input : Nat → Nat → α) (n w t : Nat) (s : State α)
    (ht : t<n) (hb : n<2147483648) (hp : s.pc t=0) (hr : LarkPairMap.Reads n input s) :
    runLane ops (LarkPairMap.layout n) (LarkPairMap.geometry n w) program t 5 s=some (after ops input t s) := by
  let s1:=indexed t s
  let s2:=setReg (record s1 t (LarkPairMap.cell 0 t) false) t 0 (input 0 t) 2
  let s3:=loaded input t s
  have h1:=execute_index_of ops (LarkPairMap.layout n) (LarkPairMap.geometry n w) t 0 1 .bid s (t : Int)
    (by simpa [evalIndex,LarkPairMap.geometry,LarkPointwise.geometry] using int32_cast t (by omega)) (by omega)
  change execute _ _ _ _ _ s=some s1 at h1
  have h2:=assign_of ops (LarkPairMap.layout n) (LarkPairMap.geometry n w) t 0 2
    (.load .global 0 (.ivar 0)) s1 _ (input 0 t)
    (load_eq ops n w t 0 s1 input (by decide) ht (by simp [s1,indexed,setIndex,advance]) hr)
    (by simp [s1,indexed,setIndex,advance])
  change execute _ _ _ _ _ s1=some s2 at h2
  have h3:=assign_of ops (LarkPairMap.layout n) (LarkPairMap.geometry n w) t 1 3
    (.load .global 1 (.ivar 0)) s2 _ (input 1 t)
    (load_eq ops n w t 1 s2 input (by decide) ht
      (by simp [s2,setReg,record,advance,s1,indexed,setIndex]) hr)
    (by simp [s2,setReg,advance])
  change execute _ _ _ _ _ s2=some s3 at h3
  have he : evalExpr ops (LarkPairMap.layout n) (LarkPairMap.geometry n w) t body s3=
      some (value ops (input 0 t) (input 1 t),s3) := by
    simp [body,value,evalExpr,s3,loaded,setReg,record,advance,applyBinary,applyUnary]
  have hi : s3.indices t 0=some (t : Int) := by simp [s3,loaded,setReg,record,advance,indexed,setIndex]
  have hl : location (LarkPairMap.layout n) (LarkPairMap.geometry n w) t .global 2 (t : Int) true=
      some (LarkPairMap.cell 2 t) := by
    have hneg : ¬(t : Int)<0 := by omega
    have hrole : (Role.output==Role.input)=false := by decide
    simp [location,LarkPairMap.layout,LarkPairMap.cell,hneg,ht,hrole]
  have h4 : execute ops (LarkPairMap.layout n) (LarkPairMap.geometry n w) t
      (.store .global 2 (.ivar 0) body) s3=some (after ops input t s) := by
    simp only [execute,evalIndex,hi,bind,pure,Option.bind,hl,he]
    have hh : s3.pc t+1=4 := by simp [s3,loaded,setReg,advance]
    rw [hh];rfl
  rw [LarkPointwise.lane_step ops _ _ _ _ _ _ _ _
    (by simp [parked,program,hp]) (by simp [program,hp]) h1]
  rw [LarkPointwise.lane_step ops _ _ _ _ _ _ _ _
    (by simp [parked,program,s1,indexed,setIndex,advance]) (by simp [program,s1,indexed,setIndex,advance]) h2]
  rw [LarkPointwise.lane_step ops _ _ _ _ _ _ _ _
    (by simp [parked,program,s2,setReg,advance]) (by simp [program,s2,setReg,advance]) h3]
  rw [LarkPointwise.lane_step ops _ _ _ _ _ _ _ _
    (by simp [parked,program,s3,loaded,setReg,advance]) (by simp [program,s3,loaded,setReg,advance]) h4]
  simp [runLane,parked,program,after,advance]

theorem after_memory (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) (l : Location) :
    (after ops input t s).memory l=
      if l=LarkPairMap.cell 2 t then some (value ops (input 0 t) (input 1 t)) else s.memory l := by rfl
theorem after_pc (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) (u : Nat) :
    (after ops input t s).pc u=if u=t then 4 else s.pc u := by
  by_cases h : u=t <;> simp [after,loaded,indexed,setIndex,setReg,record,advance,h]
theorem after_owned (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α)
    (h : LarkPairMap.Owned s.trace) : LarkPairMap.Owned (after ops input t s).trace := by
  exact LarkReduction.owned_write _
    (LarkReduction.owned_read _ (LarkReduction.owned_read _ h t 0 t (s.epochs t) (by decide))
      t 1 t (s.epochs t) (by decide)) t (s.epochs t)

def profile (n : Nat) : LarkPairMap.Profile where
  n:=n
  program:=program
  laneFuel:=5
  haltPc:=4
  halt:=rfl
  value:=fun _ ops input t=>value ops (input 0 t) (input 1 t)
  after:=fun _ ops input t s=>after ops input t s
  afterMemory:=fun _ ops input t s l=>after_memory ops input t s l
  afterPc:=fun _ ops input t s u=>after_pc ops input t s u
  afterOwned:=fun _ ops input t s h=>after_owned ops input t s h
  laneEq:=fun _ ops w t s input ht hb hp hr=>lane_eq ops input n w t s ht hb hp hr

#print axioms lane_eq
#print axioms after_owned
end LarkSwiPointwise
