import Lark.FoldPhase

/-! Scalar FP16 RMSNorm, LayerNorm and stable Softmax, by actual-machine induction. -/
namespace LarkNormalization
open LarkNonlinear LarkFoldPhase
open LarkReduction (setIndex setReg int32_cast execute_index_of execute_pure_of)
set_option maxRecDepth 10000
set_option maxHeartbeats 20000000

inductive Kind where
  | rms | layer | softmax
  deriving Repr, DecidableEq

def firstStart (kind : Kind) : Nat := if kind=.softmax then 1 else 0
def secondStart (kind : Kind) (n : Nat) : Nat := if kind=.rms then n else 0
def firstTerm : Kind → Term
  | .rms => .bin .mul .input .input
  | _ => .input
def secondTerm : Kind → Term
  | .layer => .bin .mul (.bin .sub .input .context) (.bin .sub .input .context)
  | .softmax => .un .exp (.bin .sub .input .context)
  | .rms => .input
def firstOp (kind : Kind) : Binary := if kind=.softmax then .max else .add
def mean (n : Nat) : Term := .bin .div .accumulator (.lit (n : Int) 1)
def epilogue (kind : Kind) (n : Nat) : Term :=
  let eps : Term:=.lit 1 100000
  match kind with
  | .rms => .bin .mul .input (.un .rsqrt (.bin .add .context eps))
  | .layer => .bin .mul (.bin .sub .input .context)
      (.un .rsqrt (.bin .add (mean n) eps))
  | .softmax => .bin .div (.un .exp (.bin .sub .input .context)) .accumulator
def seedExpr (kind : Kind) : Expr :=
  if kind=.softmax then .un .fromHalf (.load .global 0 (.const 0)) else .lit 0 1
def middleExpr (kind : Kind) (n : Nat) : Expr :=
  if kind=.softmax then .reg 0 else .bin .div (.reg 0) (.lit (n : Int) 1)
def program (kind : Kind) (n : Nat) : List Instr :=
  [.index 0 .bid, .assign 0 (seedExpr kind), .assign 1 (.lit 0 1), .assign 2 (.lit 0 1),
   .index 1 (.const (firstStart kind : Int)),
   .branch (.lt (.ivar 1) (.const (n : Int))) 10,
   .assign 2 (.un .fromHalf (.load .global 0 (.ivar 1))),
   .assign 0 (.bin (firstOp kind) (.reg 0) (lower (firstTerm kind))),
   .index 1 (.add (.ivar 1) (.const 1)), .jump 5,
   .assign 1 (middleExpr kind n), .assign 0 (.lit 0 1),
   .index 1 (.const (secondStart kind n : Int)),
   .branch (.lt (.ivar 1) (.const (n : Int))) 18,
   .assign 2 (.un .fromHalf (.load .global 0 (.ivar 1))),
   .assign 0 (.bin .add (.reg 0) (lower (secondTerm kind))),
   .index 1 (.add (.ivar 1) (.const 1)), .jump 13,
   .assign 2 (.un .fromHalf (.load .global 0 (.ivar 0))),
   .store .global 1 (.ivar 0) (.un .toHalf (lower (epilogue kind n))), .halt]

def phase1 (kind : Kind) (n : Nat) : Phase :=
  ⟨n,5,10,firstOp kind,firstTerm kind,by cases kind <;> simp [firstTerm,Valid],
   program kind n,rfl,rfl,rfl,rfl,rfl⟩
def phase2 (kind : Kind) (n : Nat) : Phase :=
  ⟨n,13,18,.add,secondTerm kind,by cases kind <;> simp [secondTerm,Valid],
   program kind n,rfl,rfl,rfl,rfl,rfl⟩
def seed (kind : Kind) (ops : Ops α) (input : Nat → Nat → α) : α :=
  if kind=.softmax then ops.fromHalf (input 0 0) else ops.literal 0 1
def context (kind : Kind) (ops : Ops α) (n : Nat) (acc : α) : α :=
  if kind=.softmax then acc else ops.div acc (ops.literal (n : Int) 1)
def firstSum (kind : Kind) (ops : Ops α) (input : Nat → Nat → α) (n : Nat) : α :=
  folded (phase1 kind n) ops input (ops.literal 0 1)
    (firstStart kind) (n-firstStart kind) (seed kind ops input)
def ctx (kind : Kind) (ops : Ops α) (input : Nat → Nat → α) (n : Nat) : α :=
  context kind ops n (firstSum kind ops input n)
def secondSum (kind : Kind) (ops : Ops α) (input : Nat → Nat → α) (n : Nat) : α :=
  folded (phase2 kind n) ops input (ctx kind ops input n)
    (secondStart kind n) (n-secondStart kind n) (ops.literal 0 1)
def result (kind : Kind) (ops : Ops α) (input : Nat → Nat → α) (n t : Nat) : α :=
  ops.toHalf (value ops (ops.fromHalf (input 0 t)) (ctx kind ops input n)
    (secondSum kind ops input n) (epilogue kind n))

def initialized (kind : Kind) (ops : Ops α) (input : Nat → Nat → α) (t : Nat)
    (s : State α) : State α :=
  let s:=setIndex s t 0 (t : Int) 1
  let s:=if kind=.softmax then record s t (LarkUnaryMap.cell 0 0) false else s
  let s:=setReg s t 0 (seed kind ops input) 2
  let s:=setReg s t 1 (ops.literal 0 1) 3
  let s:=setReg s t 2 (ops.literal 0 1) 4
  setIndex s t 1 (firstStart kind : Int) 5
def firstState (kind : Kind) (ops : Ops α) (input : Nat → Nat → α) (n t : Nat)
    (s : State α) : State α :=
  iterate (phase1 kind n) ops input (ops.literal 0 1) t
    (firstStart kind) (n-firstStart kind) (seed kind ops input) (initialized kind ops input t s)
def middle (kind : Kind) (ops : Ops α) (input : Nat → Nat → α) (n t : Nat)
    (s : State α) : State α :=
  let s:=setReg s t 1 (ctx kind ops input n) 11
  let s:=setReg s t 0 (ops.literal 0 1) 12
  setIndex s t 1 (secondStart kind n : Int) 13
def secondState (kind : Kind) (ops : Ops α) (input : Nat → Nat → α) (n t : Nat)
    (s : State α) : State α :=
  iterate (phase2 kind n) ops input (ctx kind ops input n) t
    (secondStart kind n) (n-secondStart kind n) (ops.literal 0 1)
    (middle kind ops input n t (firstState kind ops input n t s))
def after (kind : Kind) (ops : Ops α) (input : Nat → Nat → α) (n t : Nat)
    (s : State α) : State α :=
  let s:=setReg (record (secondState kind ops input n t s) t (LarkUnaryMap.cell 0 t) false)
    t 2 (ops.fromHalf (input 0 t)) 19
  advance {record s t (LarkUnaryMap.cell 1 t) true with
    memory:=fun l=>if l=LarkUnaryMap.cell 1 t then some (result kind ops input n t) else s.memory l}
    t 20
def laneFuel (kind : Kind) (n : Nat) : Nat :=
  5*(n-firstStart kind)+5*(n-secondStart kind n)+13

theorem initialized_eq (kind : Kind) (ops : Ops α) (input : Nat → Nat → α)
    (n w t f : Nat) (s : State α) (hn : 0<n) (ht : t<2147483648)
    (hr : LarkUnaryMap.Reads n input s) (hp : s.pc t=0) :
    runLane ops (LarkUnaryMap.layout n) (LarkUnaryMap.geometry n w) (program kind n) t (f+5) s=
      runLane ops (LarkUnaryMap.layout n) (LarkUnaryMap.geometry n w) (program kind n) t f
        (initialized kind ops input t s) := by
  let s1:=setIndex s t 0 (t : Int) 1
  let loaded:=if kind=.softmax then record s1 t (LarkUnaryMap.cell 0 0) false else s1
  let s2:=setReg loaded t 0 (seed kind ops input) 2
  let s3:=setReg s2 t 1 (ops.literal 0 1) 3
  let s4:=setReg s3 t 2 (ops.literal 0 1) 4
  have h1:=execute_index_of ops (LarkUnaryMap.layout n) (LarkUnaryMap.geometry n w) t 0 1 .bid s
    (t : Int) (by simpa [LarkUnaryMap.geometry,LarkPointwise.geometry,evalIndex] using int32_cast t ht)
    (by omega)
  change execute _ _ _ _ _ s=some s1 at h1
  have hseed : evalExpr ops (LarkUnaryMap.layout n) (LarkUnaryMap.geometry n w) t (seedExpr kind) s1=
      some (seed kind ops input,loaded) := by
    have hr0 : s.memory ⟨.global,0,0,0⟩=some (input 0 0) := hr 0 hn
    cases kind <;> simp [seedExpr,seed,loaded,evalExpr,evalIndex,int32,applyUnary,location,
      LarkUnaryMap.layout,LarkUnaryMap.cell,s1,setIndex,advance,hr0,hn]
  have h2 : execute ops (LarkUnaryMap.layout n) (LarkUnaryMap.geometry n w) t
      (.assign 0 (seedExpr kind)) s1=some s2 := by
    simp only [execute,hseed,bind,pure,Option.bind]
    have hh : s1.pc t+1=2 := by simp [s1,setIndex,advance]
    rw [hh];rfl
  have h3:=execute_pure_of ops (LarkUnaryMap.layout n) (LarkUnaryMap.geometry n w) t 1 3
    (.lit 0 1) s2 (ops.literal 0 1) (by simp [evalExpr]) (by simp [s2,setReg,advance])
  change execute _ _ _ _ _ s2=some s3 at h3
  have h4:=execute_pure_of ops (LarkUnaryMap.layout n) (LarkUnaryMap.geometry n w) t 2 4
    (.lit 0 1) s3 (ops.literal 0 1) (by simp [evalExpr]) (by simp [s3,setReg,advance])
  change execute _ _ _ _ _ s3=some s4 at h4
  have hstart : evalIndex (LarkUnaryMap.geometry n w) t s4 (.const (firstStart kind : Int))=
      some (firstStart kind : Int) := by cases kind <;> rfl
  have h5:=execute_index_of ops (LarkUnaryMap.layout n) (LarkUnaryMap.geometry n w) t 1 5
    (.const (firstStart kind : Int)) s4 (firstStart kind : Int) hstart (by simp [s4,setReg,advance])
  change execute _ _ _ _ _ s4=some (initialized kind ops input t s) at h5
  rw [LarkPointwise.lane_step ops _ _ _ _ _ _ _ _
    (by simp [parked,program,hp]) (by simp [program,hp]) h1]
  rw [LarkPointwise.lane_step ops _ _ _ _ _ _ _ _
    (by simp [parked,program,s1,setIndex,advance]) (by simp [program,s1,setIndex,advance]) h2]
  rw [LarkPointwise.lane_step ops _ _ _ _ _ _ _ _
    (by simp [parked,program,s2,setReg,advance]) (by simp [program,s2,setReg,advance]) h3]
  rw [LarkPointwise.lane_step ops _ _ _ _ _ _ _ _
    (by simp [parked,program,s3,setReg,advance]) (by simp [program,s3,setReg,advance]) h4]
  rw [LarkPointwise.lane_step ops _ _ _ _ _ _ _ _
    (by simp [parked,program,s4,setReg,advance]) (by simp [program,s4,setReg,advance]) h5]

theorem first_memory (kind : Kind) (ops : Ops α) (input : Nat → Nat → α) (n t : Nat)
    (s : State α) : (firstState kind ops input n t s).memory=s.memory := by
  simp only [firstState,iterate_memory]
  cases kind <;> rfl

theorem first_pc (kind : Kind) (ops : Ops α) (input : Nat → Nat → α) (n t u : Nat)
    (s : State α) : (firstState kind ops input n t s).pc u=if u=t then 10 else s.pc u := by
  simp only [firstState,iterate_pc]
  by_cases h : u=t <;> cases kind <;>
    simp [phase1,initialized,setIndex,setReg,record,advance,h]

theorem first_index (kind : Kind) (ops : Ops α) (input : Nat → Nat → α) (n t : Nat)
    (s : State α) : (firstState kind ops input n t s).indices t 0=some (t : Int) := by
  simp only [firstState,iterate_index0]
  cases kind <;> simp [initialized,setIndex,setReg,advance,record]

theorem first_acc (kind : Kind) (ops : Ops α) (input : Nat → Nat → α) (n t : Nat)
    (s : State α) : (firstState kind ops input n t s).regs t 0=some (firstSum kind ops input n) := by
  apply iterate_acc
  cases kind <;> simp [initialized,setIndex,setReg,advance,record]

theorem middle_eq (kind : Kind) (ops : Ops α) (input : Nat → Nat → α)
    (n w t f : Nat) (s : State α) (hb : n<2147483648)
    (hp : s.pc t=10) (ha : s.regs t 0=some (firstSum kind ops input n)) :
    runLane ops (LarkUnaryMap.layout n) (LarkUnaryMap.geometry n w) (program kind n) t (f+3) s=
      runLane ops (LarkUnaryMap.layout n) (LarkUnaryMap.geometry n w) (program kind n) t f
        (middle kind ops input n t s) := by
  let s1:=setReg s t 1 (ctx kind ops input n) 11
  let s2:=setReg s1 t 0 (ops.literal 0 1) 12
  have he : evalExpr ops (LarkUnaryMap.layout n) (LarkUnaryMap.geometry n w) t
      (middleExpr kind n) s=some (ctx kind ops input n,s) := by
    cases kind <;> simp [middleExpr,ctx,context,evalExpr,ha,applyBinary]
  have h1:=execute_pure_of ops (LarkUnaryMap.layout n) (LarkUnaryMap.geometry n w) t 1 11
    (middleExpr kind n) s (ctx kind ops input n) he (by omega)
  change execute _ _ _ _ _ s=some s1 at h1
  have h2:=execute_pure_of ops (LarkUnaryMap.layout n) (LarkUnaryMap.geometry n w) t 0 12
    (.lit 0 1) s1 (ops.literal 0 1) (by simp [evalExpr]) (by simp [s1,setReg,advance])
  change execute _ _ _ _ _ s1=some s2 at h2
  have hs : evalIndex (LarkUnaryMap.geometry n w) t s2 (.const (secondStart kind n : Int))=
      some (secondStart kind n : Int) := by
    exact int32_cast (secondStart kind n) (by cases kind <;> simp [secondStart];exact hb)
  have h3:=execute_index_of ops (LarkUnaryMap.layout n) (LarkUnaryMap.geometry n w) t 1 13
    (.const (secondStart kind n : Int)) s2 (secondStart kind n : Int) hs
    (by simp [s2,setReg,advance])
  rw [LarkPointwise.lane_step ops _ _ _ _ _ _ _ _
    (by simp [parked,program,hp]) (by simp [program,hp]) h1]
  rw [LarkPointwise.lane_step ops _ _ _ _ _ _ _ _
    (by simp [parked,program,s1,setReg,advance]) (by simp [program,s1,setReg,advance]) h2]
  rw [LarkPointwise.lane_step ops _ _ _ _ _ _ _ _
    (by simp [parked,program,s2,setReg,advance]) (by simp [program,s2,setReg,advance]) h3]
  rfl

theorem second_memory (kind : Kind) (ops : Ops α) (input : Nat → Nat → α) (n t : Nat)
    (s : State α) : (secondState kind ops input n t s).memory=s.memory := by
  simp [secondState,iterate_memory,middle,setIndex,setReg,advance,first_memory]

theorem second_pc (kind : Kind) (ops : Ops α) (input : Nat → Nat → α) (n t u : Nat)
    (s : State α) : (secondState kind ops input n t s).pc u=if u=t then 18 else s.pc u := by
  simp only [secondState,iterate_pc]
  by_cases h : u=t <;> simp [phase2,middle,setIndex,setReg,advance,first_pc,h]

theorem second_index (kind : Kind) (ops : Ops α) (input : Nat → Nat → α) (n t : Nat)
    (s : State α) : (secondState kind ops input n t s).indices t 0=some (t : Int) := by
  simp [secondState,iterate_index0,middle,setIndex,setReg,advance,first_index]

theorem second_context (kind : Kind) (ops : Ops α) (input : Nat → Nat → α) (n t : Nat)
    (s : State α) : (secondState kind ops input n t s).regs t 1=some (ctx kind ops input n) := by
  simp [secondState,iterate_context,middle,setIndex,setReg,advance]

theorem second_acc (kind : Kind) (ops : Ops α) (input : Nat → Nat → α) (n t : Nat)
    (s : State α) : (secondState kind ops input n t s).regs t 0=some (secondSum kind ops input n) := by
  apply iterate_acc
  simp [middle,setIndex,setReg,advance]

theorem lane_eq (kind : Kind) (ops : Ops α) (input : Nat → Nat → α)
    (n w t : Nat) (s : State α) (ht : t<n) (hb : n<2147483648)
    (hp : s.pc t=0) (hr : LarkUnaryMap.Reads n input s) :
    runLane ops (LarkUnaryMap.layout n) (LarkUnaryMap.geometry n w) (program kind n) t
      (laneFuel kind n) s=some (after kind ops input n t s) := by
  have hn : 0<n := by omega
  have hf : laneFuel kind n=(5*(n-firstStart kind)+5*(n-secondStart kind n)+8)+5 := by
    unfold laneFuel;omega
  rw [hf,initialized_eq kind ops input n w t _ s hn (by omega) hr hp]
  have hf1 : 5*(n-firstStart kind)+5*(n-secondStart kind n)+8=
      (5*(n-secondStart kind n)+7)+5*(n-firstStart kind)+1 := by omega
  rw [hf1]
  have h1:=LarkFoldPhase.run_eq (phase1 kind n) ops input (ops.literal 0 1) (seed kind ops input)
    w t (n-firstStart kind) (firstStart kind) (5*(n-secondStart kind n)+7)
    (initialized kind ops input t s)
    (by cases kind <;> exact hr)
    (by cases kind <;> simp [initialized,setIndex,setReg,record,advance])
    (by cases kind <;> simp [initialized,setIndex,setReg,record,advance])
    (by cases kind <;> simp [initialized,setIndex,setReg,record,advance])
    (by simp [initialized,setIndex,advance,phase1])
    (by cases kind <;> simp [phase1,firstStart];omega) hb
  change runLane ops (LarkUnaryMap.layout n) (LarkUnaryMap.geometry n w) (program kind n) t _ _=
    runLane ops (LarkUnaryMap.layout n) (LarkUnaryMap.geometry n w) (program kind n) t _
      (firstState kind ops input n t s) at h1
  rw [h1]
  have hfm : 5*(n-secondStart kind n)+7=(5*(n-secondStart kind n)+4)+3 := by omega
  rw [hfm,middle_eq kind ops input n w t _ _ hb (by simp [first_pc]) (first_acc kind ops input n t s)]
  have hf2 : 5*(n-secondStart kind n)+4=3+5*(n-secondStart kind n)+1 := by omega
  rw [hf2]
  have h2:=LarkFoldPhase.run_eq (phase2 kind n) ops input (ctx kind ops input n) (ops.literal 0 1)
    w t (n-secondStart kind n) (secondStart kind n) 3
    (middle kind ops input n t (firstState kind ops input n t s))
    (by simpa [LarkUnaryMap.Reads,middle,setIndex,setReg,advance,first_memory] using hr)
    (by simp [middle,setIndex,advance])
    (by simp [middle,setIndex,setReg,advance])
    (by simp [middle,setIndex,setReg,advance])
    (by simp [middle,setIndex,advance,phase2])
    (by cases kind <;> simp [phase2,secondStart]) hb
  change runLane ops (LarkUnaryMap.layout n) (LarkUnaryMap.geometry n w) (program kind n) t _ _=
    runLane ops (LarkUnaryMap.layout n) (LarkUnaryMap.geometry n w) (program kind n) t _
      (secondState kind ops input n t s) at h2
  rw [h2]
  let s1:=secondState kind ops input n t s
  let s2:=setReg (record s1 t (LarkUnaryMap.cell 0 t) false) t 2 (ops.fromHalf (input 0 t)) 19
  have hm : s1.memory (LarkUnaryMap.cell 0 t)=some (input 0 t) := by rw [second_memory];exact hr t ht
  have hl : location (LarkUnaryMap.layout n) (LarkUnaryMap.geometry n w) t .global 0 (t : Int) false=
      some (LarkUnaryMap.cell 0 t) := by
    have hneg : ¬(t : Int)<0 := by omega
    simp [location,LarkUnaryMap.layout,LarkUnaryMap.cell,hneg,ht]
  have he : evalExpr ops (LarkUnaryMap.layout n) (LarkUnaryMap.geometry n w) t
      (.un .fromHalf (.load .global 0 (.ivar 0))) s1=
      some (ops.fromHalf (input 0 t),record s1 t (LarkUnaryMap.cell 0 t) false) := by
    simp [evalExpr,evalIndex,s1,second_index,hl,hm,applyUnary]
  have he1 : execute ops (LarkUnaryMap.layout n) (LarkUnaryMap.geometry n w) t
      (.assign 2 (.un .fromHalf (.load .global 0 (.ivar 0)))) s1=some s2 := by
    simp only [execute,he,bind,pure,Option.bind]
    have hh : s1.pc t+1=19 := by simp [s1,second_pc]
    rw [hh];rfl
  have hv : Valid (epilogue kind n) := by cases kind <;> simp [epilogue,mean,Valid]
  have hev:=eval_lower ops (LarkUnaryMap.layout n) (LarkUnaryMap.geometry n w) t s2
    (ops.fromHalf (input 0 t)) (ctx kind ops input n) (secondSum kind ops input n) (epilogue kind n) hv
    (by simp [s2,setReg,advance])
    (by simp [s2,setReg,record,advance,s1,second_context])
    (by simp [s2,setReg,record,advance,s1,second_acc])
  have hrole : (Role.output==Role.input)=false := by decide
  have hloc : location (LarkUnaryMap.layout n) (LarkUnaryMap.geometry n w) t .global 1 (t : Int) true=
      some (LarkUnaryMap.cell 1 t) := by
    have hneg : ¬(t : Int)<0 := by omega
    simp [location,LarkUnaryMap.layout,LarkUnaryMap.cell,hneg,ht,hrole]
  have he2 : execute ops (LarkUnaryMap.layout n) (LarkUnaryMap.geometry n w) t
      (.store .global 1 (.ivar 0) (.un .toHalf (lower (epilogue kind n)))) s2=
      some (after kind ops input n t s) := by
    have hi2 : s2.indices t 0=some (t : Int) := by simp [s2,setReg,record,advance,s1,second_index]
    simp only [execute,evalIndex,hi2,bind,pure,Option.bind,hloc]
    simp only [evalExpr,hev,bind,pure,Option.bind,applyUnary]
    have hh : s2.pc t+1=20 := by simp [s2,setReg,advance]
    rw [hh]
    rfl
  rw [LarkPointwise.lane_step ops _ _ _ _ _ _ _ _
    (by simp [parked,program,s1,second_pc]) (by simp [program,s1,second_pc]) he1]
  rw [LarkPointwise.lane_step ops _ _ _ _ _ _ _ _
    (by simp [parked,program,s2,setReg,advance]) (by simp [program,s2,setReg,advance]) he2]
  simp [runLane,parked,program,after,advance]

theorem after_memory (kind : Kind) (ops : Ops α) (input : Nat → Nat → α) (n t : Nat)
    (s : State α) (l : Location) :
    (after kind ops input n t s).memory l=
      if l=LarkUnaryMap.cell 1 t then some (result kind ops input n t) else s.memory l := by
  simp [after,setReg,advance,record,second_memory]

theorem after_pc (kind : Kind) (ops : Ops α) (input : Nat → Nat → α) (n t : Nat)
    (s : State α) (u : Nat) :
    (after kind ops input n t s).pc u=if u=t then 20 else s.pc u := by
  by_cases h : u=t <;> simp [after,setReg,advance,record,second_pc,h]

theorem first_owned (kind : Kind) (ops : Ops α) (input : Nat → Nat → α) (n t : Nat)
    (s : State α) (h : LarkUnaryMap.Owned s.trace) :
    LarkUnaryMap.Owned (firstState kind ops input n t s).trace := by
  apply iterate_owned
  cases kind with
  | rms => exact h
  | layer => exact h
  | softmax => exact owned_read s.trace h t 0 (s.epochs t)

theorem second_owned (kind : Kind) (ops : Ops α) (input : Nat → Nat → α) (n t : Nat)
    (s : State α) (h : LarkUnaryMap.Owned s.trace) :
    LarkUnaryMap.Owned (secondState kind ops input n t s).trace := by
  apply iterate_owned
  exact first_owned kind ops input n t s h

theorem after_owned (kind : Kind) (ops : Ops α) (input : Nat → Nat → α) (n t : Nat)
    (s : State α) (h : LarkUnaryMap.Owned s.trace) :
    LarkUnaryMap.Owned (after kind ops input n t s).trace := by
  have hh:=owned_read _ (second_owned kind ops input n t s h) t t
    ((secondState kind ops input n t s).epochs t)
  intro a ha
  simp only [after,advance,record,setReg,List.mem_cons] at ha
  rcases ha with rfl | ha
  · rfl
  · exact hh a (List.mem_cons.mpr ha)

def profile (kind : Kind) (n : Nat) : LarkUnaryMap.Profile where
  n:=n
  program:=program kind n
  laneFuel:=laneFuel kind n
  haltPc:=20
  halt:=rfl
  value:=fun _ ops input t=>result kind ops input n t
  after:=fun _ ops input t s=>after kind ops input n t s
  afterMemory:=fun _ ops input t s l=>after_memory kind ops input n t s l
  afterPc:=fun _ ops input t s u=>after_pc kind ops input n t s u
  afterOwned:=fun _ ops input t s h=>after_owned kind ops input n t s h
  laneEq:=fun _ ops w t s input ht hb hp hr=>lane_eq kind ops input n w t s ht hb hp hr

theorem correct (kind : Kind) (ops : Ops α) (n w : Nat) (hn : 0<n)
    (hb : n<2147483648) (hw : 0<w) :
    Correct ops (LarkUnaryMap.layout n) (LarkUnaryMap.geometry n w)
      (LarkUnaryMap.fuel (profile kind n)) (program kind n) (LarkUnaryMap.spec (profile kind n) ops) :=
  LarkUnaryMap.correct (profile kind n) ops w hn hb hw

#print axioms lane_eq
#print axioms correct
end LarkNormalization
