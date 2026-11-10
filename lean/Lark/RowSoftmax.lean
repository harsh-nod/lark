import Lark.RowPhase
import Lark.Matrix

/-! Stable row-wise FP32 softmax in the existing machine, one output per lane. -/
namespace LarkRowSoftmax
open LarkNonlinear
open LarkReduction (setIndex setReg int32_cast execute_index_of execute_pure_of)
open LarkFoldPhase (Term lower Valid value eval_lower)
set_option maxRecDepth 10000
set_option maxHeartbeats 20000000

structure Shape where
  rows : Nat
  width : Nat
  rowsPos : 0<rows
  widthPos : 0<width
  bound : rows*width<2147483648
def total (s : Shape) : Nat := s.rows*s.width
def baseIndex (n : Nat) : Index := .mul (.div (.ivar 0) (.const (n : Int))) (.const (n : Int))
def rowIndex (n : Nat) : Index := .add (baseIndex n) (.ivar 1)
def address (n t j : Nat) : Nat := (t/n)*n+j

theorem address_bound (s : Shape) (t j : Nat) (ht : t<total s) (hj : j<s.width) :
    address s.width t j<total s := by
  have hr : t/s.width<s.rows := (Nat.div_lt_iff_lt_mul s.widthPos).mpr ht
  exact LarkReduction.address_bound s.rows s.width (t/s.width) j hr hj

theorem address_eval (s : Shape) (g : Geometry) (t j : Nat) (state : State α)
    (hi : state.indices t 0=some (t : Int)) (hj : state.indices t 1=some (j : Int))
    (ht : t<total s) (hk : j<s.width) :
    evalIndex g t state (rowIndex s.width)=some ((address s.width t j : Nat) : Int) := by
  have hn:=LarkReduction.k_bound s.rows s.width s.rowsPos s.bound
  have hd:=LarkMatrix.eval_div_nat g t state (.ivar 0) (.const (s.width : Int)) t s.width
    hi (int32_cast s.width hn) (by omega)
  have hm : (t/s.width)*s.width<2147483648 := by
    have hle:=Nat.div_mul_le_self t s.width
    have hb : total s<2147483648 := s.bound
    omega
  have he:=LarkMatrix.eval_mul_nat g t state (.div (.ivar 0) (.const (s.width : Int)))
    (.const (s.width : Int)) (t/s.width) s.width hd (int32_cast s.width hn) hm
  exact LarkMatrix.eval_add_nat g t state (baseIndex s.width) (.ivar 1) ((t/s.width)*s.width) j he hj
    (by have h:=address_bound s t j ht hk;have hb : total s<2147483648 := s.bound;unfold address at h;omega)

def expTerm : Term := .un .exp (.bin .sub .input .context)
def endTerm : Term := .bin .div expTerm .accumulator
def program (n : Nat) : List Instr :=
  [.index 0 .bid,.index 1 (.const 0),.assign 0 (.load .global 0 (rowIndex n)),
   .assign 1 (.lit 0 1),.assign 2 (.lit 0 1),.index 1 (.const 1),
   .branch (.lt (.ivar 1) (.const (n : Int))) 11,
   .assign 2 (.load .global 0 (rowIndex n)),.assign 0 (.bin .max (.reg 0) (.reg 2)),
   .index 1 (.add (.ivar 1) (.const 1)),.jump 6,
   .assign 1 (.reg 0),.assign 0 (.lit 0 1),.index 1 (.const 0),
   .branch (.lt (.ivar 1) (.const (n : Int))) 19,
   .assign 2 (.load .global 0 (rowIndex n)),.assign 0 (.bin .add (.reg 0) (lower expTerm)),
   .index 1 (.add (.ivar 1) (.const 1)),.jump 14,
   .assign 2 (.load .global 0 (.ivar 0)),.store .global 1 (.ivar 0) (lower endTerm),.halt]

def phase1 (s : Shape) : LarkRowPhase.Phase where
  total:=total s
  k:=s.width
  address:=address s.width
  inputIndex:=rowIndex s.width
  addressBound:=address_bound s
  addressEval:=fun _ g t j state hi hj ht hk=>address_eval s g t j state hi hj ht hk
  header:=6
  exitPc:=11
  reducer:=.max
  term:=.input
  valid:=by trivial
  program:=program s.width
  atHeader:=rfl
  atLoad:=rfl
  atAcc:=rfl
  atCounter:=rfl
  atJump:=rfl
def phase2 (s : Shape) : LarkRowPhase.Phase where
  total:=total s
  k:=s.width
  address:=address s.width
  inputIndex:=rowIndex s.width
  addressBound:=address_bound s
  addressEval:=fun _ g t j state hi hj ht hk=>address_eval s g t j state hi hj ht hk
  header:=14
  exitPc:=19
  reducer:=.add
  term:=expTerm
  valid:=by trivial
  program:=program s.width
  atHeader:=rfl
  atLoad:=rfl
  atAcc:=rfl
  atCounter:=rfl
  atJump:=rfl

def seed (s : Shape) (input : Nat → Nat → α) (t : Nat) : α := input 0 (address s.width t 0)
def maximum (s : Shape) (ops : Ops α) (input : Nat → Nat → α) (t : Nat) : α :=
  LarkRowPhase.folded (phase1 s) ops input (ops.literal 0 1) t 1 (s.width-1) (seed s input t)
def denominator (s : Shape) (ops : Ops α) (input : Nat → Nat → α) (t : Nat) : α :=
  LarkRowPhase.folded (phase2 s) ops input (maximum s ops input t) t 0 s.width (ops.literal 0 1)
def result (s : Shape) (ops : Ops α) (input : Nat → Nat → α) (t : Nat) : α :=
  ops.div (ops.exp (ops.sub (input 0 t) (maximum s ops input t))) (denominator s ops input t)

def initialized (shape : Shape) (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) : State α :=
  let s:=setIndex s t 0 (t : Int) 1
  let s:=setIndex s t 1 0 2
  let s:=setReg (record s t (LarkUnaryMap.cell 0 (address shape.width t 0)) false) t 0 (seed shape input t) 3
  let s:=setReg s t 1 (ops.literal 0 1) 4
  let s:=setReg s t 2 (ops.literal 0 1) 5
  setIndex s t 1 1 6
def firstState (shape : Shape) (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) : State α :=
  LarkRowPhase.iterate (phase1 shape) ops input (ops.literal 0 1) t 1 (shape.width-1)
    (seed shape input t) (initialized shape ops input t s)
def middle (shape : Shape) (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) : State α :=
  setIndex (setReg (setReg s t 1 (maximum shape ops input t) 12) t 0 (ops.literal 0 1) 13) t 1 0 14
def secondState (shape : Shape) (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) : State α :=
  LarkRowPhase.iterate (phase2 shape) ops input (maximum shape ops input t) t 0 shape.width
    (ops.literal 0 1) (middle shape ops input t (firstState shape ops input t s))
def after (shape : Shape) (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) : State α :=
  let s:=setReg (record (secondState shape ops input t s) t (LarkUnaryMap.cell 0 t) false) t 2 (input 0 t) 20
  advance {record s t (LarkUnaryMap.cell 1 t) true with
    memory:=fun l=>if l=LarkUnaryMap.cell 1 t then some (result shape ops input t) else s.memory l} t 21

theorem assign_of (ops : Ops α) (l : Layout) (g : Geometry) (t r pc : Nat)
    (e : Expr) (s s1 : State α) (x : α) (he : evalExpr ops l g t e s=some (x,s1))
    (hp : s.pc t+1=pc) : execute ops l g t (.assign r e) s=some (setReg s1 t r x pc) := by
  simp only [execute,he,hp,bind,pure,Option.bind];rfl

theorem initialized_eq (shape : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (w t f : Nat) (s : State α) (ht : t<total shape)
    (hr : LarkUnaryMap.Reads (total shape) input s) (hp : s.pc t=0) :
    runLane ops (LarkUnaryMap.layout (total shape)) (LarkUnaryMap.geometry (total shape) w)
      (program shape.width) t (f+6) s=
    runLane ops (LarkUnaryMap.layout (total shape)) (LarkUnaryMap.geometry (total shape) w)
      (program shape.width) t f (initialized shape ops input t s) := by
  let s1:=setIndex s t 0 (t : Int) 1
  let s2:=setIndex s1 t 1 0 2
  let s3:=setReg (record s2 t (LarkUnaryMap.cell 0 (address shape.width t 0)) false) t 0 (seed shape input t) 3
  let s4:=setReg s3 t 1 (ops.literal 0 1) 4
  let s5:=setReg s4 t 2 (ops.literal 0 1) 5
  have hb : t<2147483648 := by have h : total shape<2147483648 := shape.bound;omega
  have h1:=execute_index_of ops (LarkUnaryMap.layout (total shape)) (LarkUnaryMap.geometry (total shape) w)
    t 0 1 .bid s (t : Int)
    (by simpa [evalIndex,LarkUnaryMap.geometry,LarkPointwise.geometry] using int32_cast t hb) (by omega)
  change execute _ _ _ _ _ s=some s1 at h1
  have h2:=execute_index_of ops (LarkUnaryMap.layout (total shape)) (LarkUnaryMap.geometry (total shape) w)
    t 1 2 (.const 0) s1 0 (by rfl) (by simp [s1,setIndex,advance])
  change execute _ _ _ _ _ s1=some s2 at h2
  have he3:=LarkRowPhase.load_eq (phase1 shape) ops w t 0 s2 input hr
    (by simp [s2,s1,setIndex,advance]) (by simp [s2,setIndex,advance]) ht shape.widthPos
  have h3:=assign_of ops (LarkUnaryMap.layout (total shape)) (LarkUnaryMap.geometry (total shape) w)
    t 0 3 (.load .global 0 (rowIndex shape.width)) s2 _ (seed shape input t) he3
    (by simp [s2,setIndex,advance])
  change execute _ _ _ _ _ s2=some s3 at h3
  have h4:=execute_pure_of ops (LarkUnaryMap.layout (total shape)) (LarkUnaryMap.geometry (total shape) w)
    t 1 4 (.lit 0 1) s3 (ops.literal 0 1) (by simp [evalExpr]) (by simp [s3,setReg,advance])
  change execute _ _ _ _ _ s3=some s4 at h4
  have h5:=execute_pure_of ops (LarkUnaryMap.layout (total shape)) (LarkUnaryMap.geometry (total shape) w)
    t 2 5 (.lit 0 1) s4 (ops.literal 0 1) (by simp [evalExpr]) (by simp [s4,setReg,advance])
  change execute _ _ _ _ _ s4=some s5 at h5
  have h6:=execute_index_of ops (LarkUnaryMap.layout (total shape)) (LarkUnaryMap.geometry (total shape) w)
    t 1 6 (.const 1) s5 1 (by rfl) (by simp [s5,setReg,advance])
  change execute _ _ _ _ _ s5=some (initialized shape ops input t s) at h6
  rw [LarkPointwise.lane_step ops _ _ _ _ _ _ _ _
    (by simp [parked,program,hp]) (by simp [program,hp]) h1]
  rw [LarkPointwise.lane_step ops _ _ _ _ _ _ _ _
    (by simp [parked,program,s1,setIndex,advance]) (by simp [program,s1,setIndex,advance]) h2]
  rw [LarkPointwise.lane_step ops _ _ _ _ _ _ _ _
    (by simp [parked,program,s2,setIndex,advance]) (by simp [program,s2,setIndex,advance]) h3]
  rw [LarkPointwise.lane_step ops _ _ _ _ _ _ _ _
    (by simp [parked,program,s3,setReg,advance]) (by simp [program,s3,setReg,advance]) h4]
  rw [LarkPointwise.lane_step ops _ _ _ _ _ _ _ _
    (by simp [parked,program,s4,setReg,advance]) (by simp [program,s4,setReg,advance]) h5]
  rw [LarkPointwise.lane_step ops _ _ _ _ _ _ _ _
    (by simp [parked,program,s5,setReg,advance]) (by simp [program,s5,setReg,advance]) h6]

theorem first_memory (shape : Shape) (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) :
    (firstState shape ops input t s).memory=s.memory := by
  simp [firstState,LarkRowPhase.iterate_memory,initialized,setIndex,setReg,record,advance]
theorem first_pc (shape : Shape) (ops : Ops α) (input : Nat → Nat → α) (t u : Nat) (s : State α) :
    (firstState shape ops input t s).pc u=if u=t then 11 else s.pc u := by
  simp only [firstState,LarkRowPhase.iterate_pc]
  by_cases h : u=t <;> simp [phase1,initialized,setIndex,setReg,record,advance,h]
theorem first_index (shape : Shape) (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) :
    (firstState shape ops input t s).indices t 0=some (t : Int) := by
  simp [firstState,LarkRowPhase.iterate_index0,initialized,setIndex,setReg,record,advance]
theorem first_acc (shape : Shape) (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) :
    (firstState shape ops input t s).regs t 0=some (maximum shape ops input t) := by
  apply LarkRowPhase.iterate_acc
  simp [initialized,setIndex,setReg,record,advance]

theorem middle_eq (shape : Shape) (ops : Ops α) (input : Nat → Nat → α) (w t f : Nat) (s : State α)
    (hp : s.pc t=11) (ha : s.regs t 0=some (maximum shape ops input t)) :
    runLane ops (LarkUnaryMap.layout (total shape)) (LarkUnaryMap.geometry (total shape) w)
      (program shape.width) t (f+3) s=
    runLane ops (LarkUnaryMap.layout (total shape)) (LarkUnaryMap.geometry (total shape) w)
      (program shape.width) t f (middle shape ops input t s) := by
  let s1:=setReg s t 1 (maximum shape ops input t) 12
  let s2:=setReg s1 t 0 (ops.literal 0 1) 13
  have h1:=execute_pure_of ops (LarkUnaryMap.layout (total shape)) (LarkUnaryMap.geometry (total shape) w)
    t 1 12 (.reg 0) s (maximum shape ops input t) (by simp [evalExpr,ha]) (by omega)
  change execute _ _ _ _ _ s=some s1 at h1
  have h2:=execute_pure_of ops (LarkUnaryMap.layout (total shape)) (LarkUnaryMap.geometry (total shape) w)
    t 0 13 (.lit 0 1) s1 (ops.literal 0 1) (by simp [evalExpr]) (by simp [s1,setReg,advance])
  change execute _ _ _ _ _ s1=some s2 at h2
  have h3:=execute_index_of ops (LarkUnaryMap.layout (total shape)) (LarkUnaryMap.geometry (total shape) w)
    t 1 14 (.const 0) s2 0 (by rfl) (by simp [s2,setReg,advance])
  rw [LarkPointwise.lane_step ops _ _ _ _ _ _ _ _
    (by simp [parked,program,hp]) (by simp [program,hp]) h1]
  rw [LarkPointwise.lane_step ops _ _ _ _ _ _ _ _
    (by simp [parked,program,s1,setReg,advance]) (by simp [program,s1,setReg,advance]) h2]
  rw [LarkPointwise.lane_step ops _ _ _ _ _ _ _ _
    (by simp [parked,program,s2,setReg,advance]) (by simp [program,s2,setReg,advance]) h3]
  rfl

theorem second_memory (shape : Shape) (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) :
    (secondState shape ops input t s).memory=s.memory := by
  simp [secondState,LarkRowPhase.iterate_memory,middle,setIndex,setReg,advance,first_memory]
theorem second_pc (shape : Shape) (ops : Ops α) (input : Nat → Nat → α) (t u : Nat) (s : State α) :
    (secondState shape ops input t s).pc u=if u=t then 19 else s.pc u := by
  simp only [secondState,LarkRowPhase.iterate_pc]
  by_cases h : u=t <;> simp [phase2,middle,setIndex,setReg,advance,first_pc,h]
theorem second_index (shape : Shape) (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) :
    (secondState shape ops input t s).indices t 0=some (t : Int) := by
  simp [secondState,LarkRowPhase.iterate_index0,middle,setIndex,setReg,advance,first_index]
theorem second_context (shape : Shape) (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) :
    (secondState shape ops input t s).regs t 1=some (maximum shape ops input t) := by
  simp [secondState,LarkRowPhase.iterate_context,middle,setIndex,setReg,advance]
theorem second_acc (shape : Shape) (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) :
    (secondState shape ops input t s).regs t 0=some (denominator shape ops input t) := by
  apply LarkRowPhase.iterate_acc
  simp [middle,setIndex,setReg,advance]

theorem lane_eq (shape : Shape) (ops : Ops α) (input : Nat → Nat → α) (w t : Nat) (s : State α)
    (ht : t<total shape) (hp : s.pc t=0) (hr : LarkUnaryMap.Reads (total shape) input s) :
    runLane ops (LarkUnaryMap.layout (total shape)) (LarkUnaryMap.geometry (total shape) w)
      (program shape.width) t (10*shape.width+9) s=some (after shape ops input t s) := by
  have hn:=shape.widthPos
  have hb:=LarkReduction.k_bound shape.rows shape.width shape.rowsPos shape.bound
  have hf : 10*shape.width+9=(5*shape.width+7+5*(shape.width-1)+1)+6 := by omega
  rw [hf,initialized_eq shape ops input w t _ s ht hr hp]
  have h1:=LarkRowPhase.run_eq (phase1 shape) ops input (ops.literal 0 1) (seed shape input t)
    w t (shape.width-1) 1 (5*shape.width+7) (initialized shape ops input t s)
    hr (by simp [initialized,setIndex,setReg,record,advance])
    (by simp [initialized,setIndex,advance])
    (by simp [initialized,setIndex,setReg,advance])
    (by simp [initialized,setIndex,setReg,advance])
    (by simp [initialized,setIndex,advance,phase1]) ht (by simp [phase1];omega) hb
  change runLane ops (LarkUnaryMap.layout (total shape)) (LarkUnaryMap.geometry (total shape) w)
    (program shape.width) t _ _=runLane ops (LarkUnaryMap.layout (total shape))
      (LarkUnaryMap.geometry (total shape) w) (program shape.width) t _ (firstState shape ops input t s) at h1
  rw [h1]
  have hfm : 5*shape.width+7=(5*shape.width+4)+3 := by omega
  rw [hfm,middle_eq shape ops input w t _ _ (by simp [first_pc]) (first_acc shape ops input t s)]
  have hf2 : 5*shape.width+4=3+5*shape.width+1 := by omega
  rw [hf2]
  have h2:=LarkRowPhase.run_eq (phase2 shape) ops input (maximum shape ops input t) (ops.literal 0 1)
    w t shape.width 0 3 (middle shape ops input t (firstState shape ops input t s))
    (by simpa [LarkUnaryMap.Reads,middle,setIndex,setReg,advance,first_memory] using hr)
    (by simp [middle,setIndex,setReg,advance,first_index])
    (by simp [middle,setIndex,advance])
    (by simp [middle,setIndex,setReg,advance])
    (by simp [middle,setIndex,setReg,advance])
    (by simp [middle,setIndex,advance,phase2]) ht (by simp [phase2]) hb
  change runLane ops (LarkUnaryMap.layout (total shape)) (LarkUnaryMap.geometry (total shape) w)
    (program shape.width) t _ _=runLane ops (LarkUnaryMap.layout (total shape))
      (LarkUnaryMap.geometry (total shape) w) (program shape.width) t _ (secondState shape ops input t s) at h2
  rw [h2]
  let s1:=secondState shape ops input t s
  let s2:=setReg (record s1 t (LarkUnaryMap.cell 0 t) false) t 2 (input 0 t) 20
  have hm : s1.memory (LarkUnaryMap.cell 0 t)=some (input 0 t) := by rw [second_memory];exact hr t ht
  have hl : location (LarkUnaryMap.layout (total shape)) (LarkUnaryMap.geometry (total shape) w)
      t .global 0 (t : Int) false=some (LarkUnaryMap.cell 0 t) := by
    have hneg : ¬(t : Int)<0 := by omega
    simp [location,LarkUnaryMap.layout,LarkUnaryMap.cell,hneg,ht]
  have he : evalExpr ops (LarkUnaryMap.layout (total shape)) (LarkUnaryMap.geometry (total shape) w)
      t (.load .global 0 (.ivar 0)) s1=some (input 0 t,record s1 t (LarkUnaryMap.cell 0 t) false) := by
    simp [evalExpr,evalIndex,s1,second_index,hl,hm]
  have he1:=assign_of ops (LarkUnaryMap.layout (total shape)) (LarkUnaryMap.geometry (total shape) w)
    t 2 20 (.load .global 0 (.ivar 0)) s1 _ (input 0 t) he (by simp [s1,second_pc])
  change execute _ _ _ _ _ s1=some s2 at he1
  have hev:=eval_lower ops (LarkUnaryMap.layout (total shape)) (LarkUnaryMap.geometry (total shape) w)
    t s2 (input 0 t) (maximum shape ops input t) (denominator shape ops input t) endTerm (by trivial)
    (by simp [s2,setReg,advance])
    (by simp [s2,setReg,record,advance,s1,second_context])
    (by simp [s2,setReg,record,advance,s1,second_acc])
  have hloc : location (LarkUnaryMap.layout (total shape)) (LarkUnaryMap.geometry (total shape) w)
      t .global 1 (t : Int) true=some (LarkUnaryMap.cell 1 t) := by
    have hneg : ¬(t : Int)<0 := by omega
    have hrole : (Role.output==Role.input)=false := by decide
    simp [location,LarkUnaryMap.layout,LarkUnaryMap.cell,hneg,ht,hrole]
  have he2 : execute ops (LarkUnaryMap.layout (total shape)) (LarkUnaryMap.geometry (total shape) w)
      t (.store .global 1 (.ivar 0) (lower endTerm)) s2=some (after shape ops input t s) := by
    have hi2 : s2.indices t 0=some (t : Int) := by simp [s2,setReg,record,advance,s1,second_index]
    simp only [execute,evalIndex,hi2,bind,pure,Option.bind,hloc,hev]
    have hh : s2.pc t+1=21 := by simp [s2,setReg,advance]
    rw [hh];rfl
  rw [LarkPointwise.lane_step ops _ _ _ _ _ _ _ _
    (by simp [parked,program,s1,second_pc]) (by simp [program,s1,second_pc]) he1]
  rw [LarkPointwise.lane_step ops _ _ _ _ _ _ _ _
    (by simp [parked,program,s2,setReg,advance]) (by simp [program,s2,setReg,advance]) he2]
  simp [runLane,parked,program,after,advance]

theorem after_memory (shape : Shape) (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) (l : Location) :
    (after shape ops input t s).memory l=
      if l=LarkUnaryMap.cell 1 t then some (result shape ops input t) else s.memory l := by
  simp [after,setReg,advance,record,second_memory]
theorem after_pc (shape : Shape) (ops : Ops α) (input : Nat → Nat → α) (t u : Nat) (s : State α) :
    (after shape ops input t s).pc u=if u=t then 21 else s.pc u := by
  by_cases h : u=t <;> simp [after,setReg,advance,record,second_pc,h]
theorem first_owned (shape : Shape) (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α)
    (h : LarkUnaryMap.Owned s.trace) : LarkUnaryMap.Owned (firstState shape ops input t s).trace := by
  apply LarkRowPhase.iterate_owned
  exact LarkRowPhase.owned_read s.trace h t (address shape.width t 0) (s.epochs t)
theorem second_owned (shape : Shape) (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α)
    (h : LarkUnaryMap.Owned s.trace) : LarkUnaryMap.Owned (secondState shape ops input t s).trace := by
  apply LarkRowPhase.iterate_owned
  exact first_owned shape ops input t s h
theorem after_owned (shape : Shape) (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α)
    (h : LarkUnaryMap.Owned s.trace) : LarkUnaryMap.Owned (after shape ops input t s).trace := by
  have hh:=LarkRowPhase.owned_read _ (second_owned shape ops input t s h) t t
    ((secondState shape ops input t s).epochs t)
  intro a ha
  simp only [after,advance,record,setReg,List.mem_cons] at ha
  rcases ha with rfl|ha
  · rfl
  · exact hh a (List.mem_cons.mpr ha)

def profile (shape : Shape) : LarkUnaryMap.Profile where
  n:=total shape
  program:=program shape.width
  laneFuel:=10*shape.width+9
  haltPc:=21
  halt:=rfl
  value:=fun _ ops input t=>result shape ops input t
  after:=fun _ ops input t s=>after shape ops input t s
  afterMemory:=fun _ ops input t s l=>after_memory shape ops input t s l
  afterPc:=fun _ ops input t s u=>after_pc shape ops input t u s
  afterOwned:=fun _ ops input t s h=>after_owned shape ops input t s h
  laneEq:=fun _ ops w t s input ht _ hp hr=>lane_eq shape ops input w t s ht hp hr

theorem correct (shape : Shape) (ops : Ops α) (w : Nat) (hw : 0<w) :
    Correct ops (LarkUnaryMap.layout (total shape)) (LarkUnaryMap.geometry (total shape) w)
      (LarkUnaryMap.fuel (profile shape)) (program shape.width) (LarkUnaryMap.spec (profile shape) ops) :=
  LarkUnaryMap.correct (profile shape) ops w (Nat.mul_pos shape.rowsPos shape.widthPos) shape.bound hw

#print axioms address_eval
#print axioms lane_eq
#print axioms correct
end LarkRowSoftmax
