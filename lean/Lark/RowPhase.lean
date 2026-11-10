import Lark.FoldPhase

/-! A checked five-instruction reduction cycle over one read-only FP16 array. -/
namespace LarkRowPhase
open LarkNonlinear LarkReduction
open LarkFoldPhase (Term lower Valid value eval_lower)
set_option maxRecDepth 10000
set_option maxHeartbeats 20000000

structure Phase where
  total : Nat
  k : Nat
  address : Nat → Nat → Nat
  inputIndex : Index
  addressBound : ∀ t j,t<total → j<k → address t j<total
  addressEval : ∀ (α : Type) (g : Geometry) (t j : Nat) (s : State α),
    s.indices t 0=some (t : Int) → s.indices t 1=some (j : Int) →
    t<total → j<k → evalIndex g t s inputIndex=some ((address t j : Nat) : Int)
  header : Nat
  exitPc : Nat
  reducer : Binary
  term : Term
  valid : Valid term
  program : List Instr
  atHeader : program[header]?=some (.branch (.lt (.ivar 1) (.const (k : Int))) exitPc)
  atLoad : program[header+1]?=some (.assign 2 (.load .global 0 inputIndex))
  atAcc : program[header+2]?=some (.assign 0 (.bin reducer (.reg 0) (lower term)))
  atCounter : program[header+3]?=some (.index 1 (.add (.ivar 1) (.const 1)))
  atJump : program[header+4]?=some (.jump header)

def updated (p : Phase) (ops : Ops α) (input : Nat → Nat → α) (ctx acc : α) (t j : Nat) : α :=
  applyBinary ops p.reducer acc (value ops (input 0 (p.address t j)) ctx acc p.term)

def stepState (p : Phase) (ops : Ops α) (input : Nat → Nat → α) (ctx acc : α)
    (t j : Nat) (s : State α) : State α :=
  let s:=advance s t (p.header+1)
  let s:=setReg (record s t (LarkUnaryMap.cell 0 (p.address t j)) false) t 2
    (input 0 (p.address t j)) (p.header+2)
  let s:=setReg s t 0 (updated p ops input ctx acc t j) (p.header+3)
  let s:=setIndex s t 1 ((j+1 : Nat) : Int) (p.header+4)
  advance s t p.header

theorem load_eq (p : Phase) (ops : Ops α) (w t j : Nat) (s : State α) (input : Nat → Nat → α)
    (hr : LarkUnaryMap.Reads p.total input s) (hi : s.indices t 0=some (t : Int))
    (hj : s.indices t 1=some (j : Int)) (ht : t<p.total) (hb : j<p.k) :
    evalExpr ops (LarkUnaryMap.layout p.total) (LarkUnaryMap.geometry p.total w) t
      (.load .global 0 p.inputIndex) s=
      some (input 0 (p.address t j),record s t (LarkUnaryMap.cell 0 (p.address t j)) false) := by
  have hneg : ¬ ((p.address t j : Nat) : Int)<0 := by omega
  have ha:=p.addressBound t j ht hb
  have he:=p.addressEval α (LarkUnaryMap.geometry p.total w) t j s hi hj ht hb
  have hl : location (LarkUnaryMap.layout p.total) (LarkUnaryMap.geometry p.total w) t .global 0
      ((p.address t j : Nat) : Int) false=some (LarkUnaryMap.cell 0 (p.address t j)) := by
    simp [location,LarkUnaryMap.layout,LarkUnaryMap.cell,hneg,ha]
  simp only [evalExpr,he,bind,pure,Option.bind,hl,hr _ ha]

theorem cycle (p : Phase) (ops : Ops α) (w t j f : Nat) (s : State α)
    (input : Nat → Nat → α) (ctx acc : α)
    (hr : LarkUnaryMap.Reads p.total input s) (hi0 : s.indices t 0=some (t : Int)) (hi : s.indices t 1=some (j : Int))
    (hc : s.regs t 1=some ctx) (ha : s.regs t 0=some acc)
    (hp : s.pc t=p.header) (ht : t<p.total) (hj : j<p.k) (hb : p.k<2147483648) :
    runLane ops (LarkUnaryMap.layout p.total) (LarkUnaryMap.geometry p.total w) p.program t (f+5) s=
      runLane ops (LarkUnaryMap.layout p.total) (LarkUnaryMap.geometry p.total w) p.program t f
        (stepState p ops input ctx acc t j s) := by
  let s1:=advance s t (p.header+1)
  let s2:=setReg (record s1 t (LarkUnaryMap.cell 0 (p.address t j)) false) t 2
    (input 0 (p.address t j)) (p.header+2)
  let s3:=setReg s2 t 0 (updated p ops input ctx acc t j) (p.header+3)
  let s4:=setIndex s3 t 1 ((j+1 : Nat) : Int) (p.header+4)
  have hg:=predicate_lt_of (LarkUnaryMap.geometry p.total w) t s (.ivar 1) (.const (p.k : Int))
    (j : Int) (p.k : Int) hi (int32_cast p.k hb) (by omega)
  have h1 : execute ops (LarkUnaryMap.layout p.total) (LarkUnaryMap.geometry p.total w) t
      (.branch (.lt (.ivar 1) (.const (p.k : Int))) p.exitPc) s=some s1 := by
    simp only [execute,hg,bind,pure,Option.bind,hp];rfl
  have he2:=load_eq p ops w t j s1 input hr hi0 hi ht hj
  have h2 : execute ops (LarkUnaryMap.layout p.total) (LarkUnaryMap.geometry p.total w) t
      (.assign 2 (.load .global 0 p.inputIndex)) s1=some s2 := by
    simp only [execute,he2,bind,pure,Option.bind]
    have hh : s1.pc t+1=p.header+2 := by simp [s1,advance]
    rw [hh]
    rfl
  have he3:=eval_bin_of ops (LarkUnaryMap.layout p.total) (LarkUnaryMap.geometry p.total w) t
    p.reducer (.reg 0) (lower p.term) s2 s2 s2 acc
    (value ops (input 0 (p.address t j)) ctx acc p.term)
    (by simp [evalExpr,s2,setReg,record,s1,advance,ha])
    (eval_lower ops _ _ t s2 _ ctx acc p.term p.valid
      (by simp [s2,setReg,advance])
      (by simpa [s2,setReg,record,s1,advance] using hc)
      (by simpa [s2,setReg,record,s1,advance] using ha))
  have h3 : execute ops (LarkUnaryMap.layout p.total) (LarkUnaryMap.geometry p.total w) t
      (.assign 0 (.bin p.reducer (.reg 0) (lower p.term))) s2=some s3 := by
    simp only [execute,he3,bind,pure,Option.bind]
    have hh : s2.pc t+1=p.header+3 := by simp [s2,setReg,advance]
    rw [hh]
    rfl
  have he4:=eval_add_of (LarkUnaryMap.geometry p.total w) t s3 (.ivar 1) (.const 1)
    (j : Int) 1 ((j+1 : Nat) : Int) hi (by rfl)
    (Eq.trans (congrArg int32 (Int.natCast_add j 1).symm) (int32_cast (j+1) (by omega)))
  have h4 : execute ops (LarkUnaryMap.layout p.total) (LarkUnaryMap.geometry p.total w) t
      (.index 1 (.add (.ivar 1) (.const 1))) s3=some s4 := by
    simp only [execute,he4,bind,pure,Option.bind]
    have hh : s3.pc t+1=p.header+4 := by simp [s3,setReg,advance]
    rw [hh]
    rfl
  have h5 : execute ops (LarkUnaryMap.layout p.total) (LarkUnaryMap.geometry p.total w) t
      (.jump p.header) s4=some (stepState p ops input ctx acc t j s) := by rfl
  rw [LarkPointwise.lane_step ops _ _ _ _ _ _ _ _
    (by simp [parked,hp,p.atHeader]) (by simp [hp,p.atHeader]) h1]
  rw [LarkPointwise.lane_step ops _ _ _ _ _ _ _ _
    (by simp [parked,s1,advance,p.atLoad]) (by simp [s1,advance,p.atLoad]) h2]
  rw [LarkPointwise.lane_step ops _ _ _ _ _ _ _ _
    (by simp [parked,s2,setReg,advance,p.atAcc]) (by simp [s2,setReg,advance,p.atAcc]) h3]
  rw [LarkPointwise.lane_step ops _ _ _ _ _ _ _ _
    (by simp [parked,s3,setReg,advance,p.atCounter]) (by simp [s3,setReg,advance,p.atCounter]) h4]
  rw [LarkPointwise.lane_step ops _ _ _ _ _ _ _ _
    (by simp [parked,s4,setIndex,advance,p.atJump]) (by simp [s4,setIndex,advance,p.atJump]) h5]

def iterate (p : Phase) (ops : Ops α) (input : Nat → Nat → α) (ctx : α) (t : Nat) :
    Nat → Nat → α → State α → State α
  | _,0,_,s => advance s t p.exitPc
  | j,r+1,acc,s => iterate p ops input ctx t (j+1) r (updated p ops input ctx acc t j)
      (stepState p ops input ctx acc t j s)

def folded (p : Phase) (ops : Ops α) (input : Nat → Nat → α) (ctx : α) (t : Nat) : Nat → Nat → α → α
  | _,0,acc => acc
  | j,r+1,acc => folded p ops input ctx t (j+1) r (updated p ops input ctx acc t j)

theorem exit (p : Phase) (ops : Ops α) (w t f : Nat) (s : State α)
    (hi : s.indices t 1=some (p.k : Int)) (hp : s.pc t=p.header) (hb : p.k<2147483648) :
    runLane ops (LarkUnaryMap.layout p.total) (LarkUnaryMap.geometry p.total w) p.program t (f+1) s=
      runLane ops (LarkUnaryMap.layout p.total) (LarkUnaryMap.geometry p.total w) p.program t f
        (advance s t p.exitPc) := by
  have hg:=predicate_nlt_of (LarkUnaryMap.geometry p.total w) t s (.ivar 1) (.const (p.k : Int))
    (p.k : Int) (p.k : Int) hi (int32_cast p.k hb) (by omega)
  have he : execute ops (LarkUnaryMap.layout p.total) (LarkUnaryMap.geometry p.total w) t
      (.branch (.lt (.ivar 1) (.const (p.k : Int))) p.exitPc) s=some (advance s t p.exitPc) := by
    simp only [execute,hg,bind,pure,Option.bind];rfl
  exact LarkPointwise.lane_step ops _ _ _ _ _ _ _ _
    (by simp [parked,hp,p.atHeader]) (by simp [hp,p.atHeader]) he

theorem run_eq (p : Phase) (ops : Ops α) (input : Nat → Nat → α) (ctx acc : α)
    (w t r j f : Nat) (s : State α)
    (hr : LarkUnaryMap.Reads p.total input s) (hi0 : s.indices t 0=some (t : Int)) (hi : s.indices t 1=some (j : Int))
    (hc : s.regs t 1=some ctx) (ha : s.regs t 0=some acc) (hp : s.pc t=p.header)
    (ht : t<p.total) (hcount : j+r=p.k) (hb : p.k<2147483648) :
    runLane ops (LarkUnaryMap.layout p.total) (LarkUnaryMap.geometry p.total w) p.program t (f+5*r+1) s=
      runLane ops (LarkUnaryMap.layout p.total) (LarkUnaryMap.geometry p.total w) p.program t f
        (iterate p ops input ctx t j r acc s) := by
  induction r generalizing j acc s with
  | zero =>
    have hj : j=p.k := by omega
    subst j
    simpa [iterate] using exit p ops w t f s hi hp hb
  | succ r ih =>
    have hh : j<p.k := by omega
    have hf : f+5*(r+1)+1=(f+5*r+1)+5 := by omega
    rw [hf,cycle p ops w t j (f+5*r+1) s input ctx acc hr hi0 hi hc ha hp ht hh hb]
    change _=runLane _ _ _ _ _ _ (iterate p ops input ctx t (j+1) r _ _)
    apply ih
    · exact hr
    · simpa [stepState,setIndex,setReg,record,advance] using hi0
    · simp [stepState,setIndex,setReg,record,advance]
    · simpa [stepState,setIndex,setReg,record,advance] using hc
    · simp [stepState,setIndex,setReg,record,advance]
    · simp [stepState,advance]
    · omega

theorem iterate_memory (p : Phase) (ops : Ops α) (input : Nat → Nat → α) (ctx acc : α)
    (t r j : Nat) (s : State α) :
    (iterate p ops input ctx t j r acc s).memory=s.memory := by
  induction r generalizing j acc s with
  | zero => rfl
  | succ r ih => exact ih (updated p ops input ctx acc t j) (j+1) _

theorem iterate_pc (p : Phase) (ops : Ops α) (input : Nat → Nat → α) (ctx acc : α)
    (t r j u : Nat) (s : State α) :
    (iterate p ops input ctx t j r acc s).pc u=if u=t then p.exitPc else s.pc u := by
  induction r generalizing j acc s with
  | zero => rfl
  | succ r ih =>
    simp only [iterate,ih]
    by_cases h : u=t <;> simp [stepState,setIndex,setReg,record,advance,h]

theorem iterate_index0 (p : Phase) (ops : Ops α) (input : Nat → Nat → α) (ctx acc : α)
    (t r j : Nat) (s : State α) :
    (iterate p ops input ctx t j r acc s).indices t 0=s.indices t 0 := by
  induction r generalizing j acc s with
  | zero => rfl
  | succ r ih =>
    simpa [iterate,stepState,setIndex,setReg,record,advance] using
      ih (updated p ops input ctx acc t j) (j+1) (stepState p ops input ctx acc t j s)

theorem iterate_context (p : Phase) (ops : Ops α) (input : Nat → Nat → α) (ctx acc : α)
    (t r j : Nat) (s : State α) :
    (iterate p ops input ctx t j r acc s).regs t 1=s.regs t 1 := by
  induction r generalizing j acc s with
  | zero => rfl
  | succ r ih =>
    simpa [iterate,stepState,setIndex,setReg,record,advance] using
      ih (updated p ops input ctx acc t j) (j+1) (stepState p ops input ctx acc t j s)

theorem iterate_acc (p : Phase) (ops : Ops α) (input : Nat → Nat → α) (ctx acc : α)
    (t r j : Nat) (s : State α) (ha : s.regs t 0=some acc) :
    (iterate p ops input ctx t j r acc s).regs t 0=some (folded p ops input ctx t j r acc) := by
  induction r generalizing j acc s with
  | zero => exact ha
  | succ r ih =>
    change (iterate p ops input ctx t (j+1) r _ _).regs t 0=_
    apply ih
    simp [stepState,setIndex,setReg,advance]

theorem owned_read (tr : List Access) (h : LarkUnaryMap.Owned tr) (t j : Nat) (e : Epoch) :
    LarkUnaryMap.Owned (⟨t,LarkUnaryMap.cell 0 j,false,e⟩::tr) := by
  intro a ha
  simp only [List.mem_cons] at ha
  rcases ha with rfl|ha
  · simp [LarkUnaryMap.cell]
  · exact h a ha

theorem iterate_owned (p : Phase) (ops : Ops α) (input : Nat → Nat → α) (ctx acc : α)
    (t r j : Nat) (s : State α) (h : LarkUnaryMap.Owned s.trace) :
    LarkUnaryMap.Owned (iterate p ops input ctx t j r acc s).trace := by
  induction r generalizing j acc s with
  | zero => exact h
  | succ r ih =>
    apply ih
    exact owned_read s.trace h t (p.address t j) (s.epochs t)

#print axioms cycle
#print axioms run_eq
end LarkRowPhase
