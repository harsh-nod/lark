import Lark.DotMap

/-! Two real launches connected by the actual first launch's output memory. -/
namespace LarkPipeline
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 20000000

structure Chain where
  first : LarkDotMap.Profile
  second : LarkDotMap.Profile
  compatible : second.aSize=first.n

def hidden (c : Chain) (ops : Ops α) (input : Nat → Nat → α) (i : Nat) : α :=
  LarkDotMap.result ops input c.first i
def idealInput (c : Chain) (ops : Ops α) (input : Nat → Nat → α) (b i : Nat) : α :=
  if b=0 then hidden c ops input i else input 2 i
def wiredInput (c : Chain) (ops : Ops α) (input : Nat → Nat → α) (first : State α)
    (b i : Nat) : α :=
  if b=0 then
    if i<c.first.n then (first.memory (LarkDotMap.cell 2 i)).getD (ops.literal 0 1)
    else hidden c ops input i
  else input 2 i
def firstFinal (c : Chain) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) : State α :=
  LarkDotMap.partialState ops input outside c.first c.first.n
def secondFinal (c : Chain) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) : State α :=
  LarkDotMap.partialState ops (idealInput c ops input) outside c.second c.second.n
def spec (c : Chain) (ops : Ops α) (input : Nat → Nat → α) : List α :=
  LarkDotMap.matrixSpec ops c.second (idealInput c ops input)

theorem wired_reads (c : Chain) (ops : Ops α) (input : Nat → Nat → α)
    (first : State α) (i : Nat) (hi : i<c.second.aSize) :
    wiredInput c ops input first 0 i=(first.memory (LarkDotMap.cell 2 i)).getD (ops.literal 0 1) := by
  have hh : i<c.first.n := by rw [←c.compatible];exact hi
  simp [wiredInput,hh]

theorem wired_eq (c : Chain) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) :
    wiredInput c ops input (firstFinal c ops input outside)=idealInput c ops input := by
  funext b i
  by_cases hb : b=0
  · subst b
    by_cases hi : i<c.first.n
    · have hm:=LarkDotMap.partialState_output ops input outside c.first c.first.n i hi
      simp [wiredInput,idealInput,firstFinal,hm,hidden,hi]
    · simp [wiredInput,idealInput,hi]
  · simp [wiredInput,idealInput,hb]

/-- The second launch consumes the first final memory, with the caller supplying
the third read-only input. Every valid intermediate read uses that memory. -/
def RunsWith (c : Chain) (ops : Ops α) (w : Nat) (program1 program2 : List Instr) (input : Nat → Nat → α)
    (start : State α) (outside2 : Location → Option α) (f1 f2 : State α) : Prop :=
  runLaunch ops (LarkDotMap.layout c.first) (LarkDotMap.geometry c.first w)
    (LarkDotMap.fuel c.first) program1 start=some f1 ∧
  raceFree (LarkDotMap.geometry c.first w) f1.trace=true ∧
  extract (LarkDotMap.layout c.first) f1=some (LarkDotMap.matrixSpec ops c.first input) ∧
  (∀ i,i<c.second.aSize → wiredInput c ops input f1 0 i=
    (f1.memory (LarkDotMap.cell 2 i)).getD (ops.literal 0 1)) ∧
  runLaunch ops (LarkDotMap.layout c.second) (LarkDotMap.geometry c.second w)
    (LarkDotMap.fuel c.second) program2
    (initial (LarkDotMap.layout c.second) (wiredInput c ops input f1) outside2)=some f2 ∧
  raceFree (LarkDotMap.geometry c.second w) f2.trace=true ∧
  extract (LarkDotMap.layout c.second) f2=some (spec c ops input)

abbrev Runs (c : Chain) (ops : Ops α) (w : Nat) (input : Nat → Nat → α)
    (start : State α) (outside2 : Location → Option α) (f1 f2 : State α) : Prop :=
  RunsWith c ops w (LarkDotMap.program c.first) (LarkDotMap.program c.second)
    input start outside2 f1 f2

def Correct (c : Chain) (ops : Ops α) (w : Nat) : Prop :=
  ∀ input outside1 outside2, ∃ f1 f2,
    Runs c ops w input (initial (LarkDotMap.layout c.first) input outside1) outside2 f1 f2

theorem correct (c : Chain) (ops : Ops α) (w : Nat)
    (hn1 : 0<c.first.n) (hk1 : 0<c.first.k)
    (hb1 : c.first.n<2147483648 ∧ c.first.k<2147483648)
    (hn2 : 0<c.second.n) (hk2 : 0<c.second.k)
    (hb2 : c.second.n<2147483648 ∧ c.second.k<2147483648) (hw : 0<w) :
    Correct c ops w := by
  intro input outside1 outside2
  refine ⟨firstFinal c ops input outside1,secondFinal c ops input outside2,?_,?_,?_,?_,?_,?_,?_⟩
  · exact LarkDotMap.launch_eq ops input outside1 c.first w hn1 hk1 hb1 hw
  · exact LarkReduction.owned_raceFree (LarkDotMap.geometry c.first w) _
      (LarkDotMap.partialState_owned ops input outside1 c.first c.first.n)
  · have h:=LarkDotMap.extract_eq ops input outside1 c.first
    rw [LarkDotMap.spec_eq_matrixSpec] at h
    exact h
  · exact fun i hi=>wired_reads c ops input _ i hi
  · rw [wired_eq]
    exact LarkDotMap.launch_eq ops (idealInput c ops input) outside2 c.second w hn2 hk2 hb2 hw
  · exact LarkReduction.owned_raceFree (LarkDotMap.geometry c.second w) _
      (LarkDotMap.partialState_owned ops (idealInput c ops input) outside2 c.second c.second.n)
  · have h:=LarkDotMap.extract_eq ops (idealInput c ops input) outside2 c.second
    rw [LarkDotMap.spec_eq_matrixSpec] at h
    exact h

theorem correct_pre (c : Chain) (ops : Ops α) (w : Nat) (h : Correct c ops w)
    (input : Nat → Nat → α) (start : State α) (outside2 : Location → Option α)
    (pre : StdPre (LarkDotMap.layout c.first) input start) :
    ∃ f1 f2,Runs c ops w input start outside2 f1 f2 := by
  obtain ⟨outside1,rfl⟩:=pre
  exact h input outside1 outside2

#print axioms wired_eq
#print axioms correct
#print axioms correct_pre
end LarkPipeline
