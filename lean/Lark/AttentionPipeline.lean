import Lark.AttentionAddress

/-! Dense/grouped scaled dot-product attention with two FP32 intermediates. -/
namespace LarkAttention
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 20000000

def scoreValue (s : Shape) (ops : Ops α) (input : Nat → Nat → α) (i : Nat) : α :=
  LarkDotMap.result ops input (scoreProfile s) i
def softInput (s : Shape) (ops : Ops α) (input : Nat → Nat → α) (_ i : Nat) : α :=
  scoreValue s ops input i
def probability (s : Shape) (ops : Ops α) (input : Nat → Nat → α) (i : Nat) : α :=
  LarkRowSoftmax.result (softmaxShape s) ops (softInput s ops input) i
def valueInput (s : Shape) (ops : Ops α) (input : Nat → Nat → α) (b i : Nat) : α :=
  if b=0 then probability s ops input i else input 2 i
def spec (s : Shape) (ops : Ops α) (input : Nat → Nat → α) : List α :=
  LarkDotMap.matrixSpec ops (valueProfile s) (valueInput s ops input)

def scoreFinal (s : Shape) (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) : State α :=
  LarkDotMap.partialState ops input outside (scoreProfile s) (scores s)
def softFinal (s : Shape) (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) : State α :=
  LarkUnaryMap.partialState (LarkRowSoftmax.profile (softmaxShape s)) ops (softInput s ops input) outside
    (LarkRowSoftmax.total (softmaxShape s))
def finalState (s : Shape) (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) : State α :=
  LarkDotMap.partialState ops (valueInput s ops input) outside (valueProfile s) (qCells s)
def softWired (s : Shape) (ops : Ops α) (input : Nat → Nat → α) (first : State α) (_ i : Nat) : α :=
  if i<scores s then (first.memory (LarkDotMap.cell 2 i)).getD (ops.literal 0 1) else scoreValue s ops input i
def valueWired (s : Shape) (ops : Ops α) (input : Nat → Nat → α) (middle : State α) (b i : Nat) : α :=
  if b=0 then
    if i<scores s then (middle.memory (LarkUnaryMap.cell 1 i)).getD (ops.literal 0 1) else probability s ops input i
  else input 2 i

theorem soft_wired_eq (s : Shape) (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) :
    softWired s ops input (scoreFinal s ops input outside)=softInput s ops input := by
  funext b i
  by_cases hi : i<scores s
  · have hm:=LarkDotMap.partialState_output ops input outside (scoreProfile s) (scores s) i hi
    simp [softWired,softInput,scoreFinal,scoreValue,hi,hm]
  · simp [softWired,softInput,hi]

theorem value_wired_eq (s : Shape) (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) :
    valueWired s ops input (softFinal s ops input outside)=valueInput s ops input := by
  funext b i
  by_cases hb : b=0
  · subst b
    by_cases hi : i<scores s
    · have hn : i<LarkRowSoftmax.total (softmaxShape s) := by rw [softmax_total];exact hi
      have hm:=LarkUnaryMap.partialState_output (LarkRowSoftmax.profile (softmaxShape s)) ops
        (softInput s ops input) outside (LarkRowSoftmax.total (softmaxShape s)) i hn
      simpa [valueWired,valueInput,softFinal,hi,probability,LarkRowSoftmax.profile] using
        congrArg (fun x : Option α=>x.getD (ops.literal 0 1)) hm
    · simp [valueWired,valueInput,hi]
  · simp [valueWired,valueInput,hb]

structure Programs where
  score : List Instr
  softmax : List Instr
  value : List Instr
def programs (s : Shape) : Programs :=
  ⟨LarkDotMap.program (scoreProfile s),LarkRowSoftmax.program s.seq,LarkDotMap.program (valueProfile s)⟩

def RunsWith (s : Shape) (ops : Ops α) (w : Nat) (p : Programs) (input : Nat → Nat → α)
    (start : State α) (os ov : Location → Option α) (fs fp fo : State α) : Prop :=
  runLaunch ops (LarkDotMap.layout (scoreProfile s)) (LarkDotMap.geometry (scoreProfile s) w)
    (LarkDotMap.fuel (scoreProfile s)) p.score start=some fs ∧
  raceFree (LarkDotMap.geometry (scoreProfile s) w) fs.trace=true ∧
  extract (LarkDotMap.layout (scoreProfile s)) fs=some (LarkDotMap.matrixSpec ops (scoreProfile s) input) ∧
  (∀ i,i<LarkRowSoftmax.total (softmaxShape s) →
    softWired s ops input fs 0 i=(fs.memory (LarkDotMap.cell 2 i)).getD (ops.literal 0 1)) ∧
  runLaunch ops (LarkUnaryMap.layout (LarkRowSoftmax.total (softmaxShape s)))
    (LarkUnaryMap.geometry (LarkRowSoftmax.total (softmaxShape s)) w)
    (LarkUnaryMap.fuel (LarkRowSoftmax.profile (softmaxShape s))) p.softmax
    (initial (LarkUnaryMap.layout (LarkRowSoftmax.total (softmaxShape s))) (softWired s ops input fs) os)=some fp ∧
  raceFree (LarkUnaryMap.geometry (LarkRowSoftmax.total (softmaxShape s)) w) fp.trace=true ∧
  extract (LarkUnaryMap.layout (LarkRowSoftmax.total (softmaxShape s))) fp=
    some (LarkUnaryMap.spec (LarkRowSoftmax.profile (softmaxShape s)) ops (softInput s ops input)) ∧
  (∀ i,i<(valueProfile s).aSize →
    valueWired s ops input fp 0 i=(fp.memory (LarkUnaryMap.cell 1 i)).getD (ops.literal 0 1)) ∧
  runLaunch ops (LarkDotMap.layout (valueProfile s)) (LarkDotMap.geometry (valueProfile s) w)
    (LarkDotMap.fuel (valueProfile s)) p.value
    (initial (LarkDotMap.layout (valueProfile s)) (valueWired s ops input fp) ov)=some fo ∧
  raceFree (LarkDotMap.geometry (valueProfile s) w) fo.trace=true ∧
  extract (LarkDotMap.layout (valueProfile s)) fo=some (spec s ops input)

def Correct (s : Shape) (ops : Ops α) (w : Nat) (p : Programs) : Prop :=
  ∀ input oq os ov,∃ fs fp fo,RunsWith s ops w p input
    (initial (LarkDotMap.layout (scoreProfile s)) input oq) os ov fs fp fo

theorem correct (s : Shape) (ops : Ops α) (w : Nat) (hw : 0<w) : Correct s ops w (programs s) := by
  intro input oq os ov
  have hn1 : 0<(scoreProfile s).n := Nat.mul_pos (heads_pos s) (Nat.mul_pos s.seqPos s.seqPos)
  have hk1 : 0<(scoreProfile s).k := s.dimPos
  have hb1 : (scoreProfile s).n<2147483648 ∧ (scoreProfile s).k<2147483648 := ⟨s.scoreBound,dim_bound s⟩
  have hn2 : 0<(valueProfile s).n := Nat.mul_pos (heads_pos s) (row_pos s)
  have hk2 : 0<(valueProfile s).k := s.seqPos
  have hb2 : (valueProfile s).n<2147483648 ∧ (valueProfile s).k<2147483648 := ⟨s.qBound,seq_bound s⟩
  refine ⟨scoreFinal s ops input oq,softFinal s ops input os,finalState s ops input ov,
    ?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact LarkDotMap.launch_eq ops input oq (scoreProfile s) w hn1 hk1 hb1 hw
  · exact LarkReduction.owned_raceFree _ _ (LarkDotMap.partialState_owned ops input oq (scoreProfile s) (scores s))
  · have he:=LarkDotMap.extract_eq ops input oq (scoreProfile s)
    rw [LarkDotMap.spec_eq_matrixSpec] at he
    exact he
  · intro i hi
    rw [softmax_total] at hi
    simp [softWired,hi]
  · rw [soft_wired_eq]
    exact LarkUnaryMap.launch_eq (LarkRowSoftmax.profile (softmaxShape s)) ops (softInput s ops input) os w
      (Nat.mul_pos (softmaxShape s).rowsPos (softmaxShape s).widthPos) (softmaxShape s).bound hw
  · exact LarkUnaryMap.owned_raceFree _ _ (LarkUnaryMap.partialState_owned
      (LarkRowSoftmax.profile (softmaxShape s)) ops (softInput s ops input) os (LarkRowSoftmax.total (softmaxShape s)))
  · exact LarkUnaryMap.extract_eq (LarkRowSoftmax.profile (softmaxShape s)) ops (softInput s ops input) os
  · intro i hi
    change i<scores s at hi
    simp [valueWired,hi]
  · rw [value_wired_eq]
    exact LarkDotMap.launch_eq ops (valueInput s ops input) ov (valueProfile s) w hn2 hk2 hb2 hw
  · exact LarkReduction.owned_raceFree _ _ (LarkDotMap.partialState_owned ops (valueInput s ops input) ov (valueProfile s) (qCells s))
  · have he:=LarkDotMap.extract_eq ops (valueInput s ops input) ov (valueProfile s)
    rw [LarkDotMap.spec_eq_matrixSpec] at he
    exact he

#print axioms soft_wired_eq
#print axioms value_wired_eq
#print axioms correct
end LarkAttention
