import Lark.SwiPointwise
import Lark.FeedForward

/-! Four ordered scalar launches preserving FP32 projections until SiLU*up. -/
namespace LarkSwiGLU
open LarkNonlinear
abbrev Shape := LarkFeedForward.Shape
set_option maxRecDepth 10000
set_option maxHeartbeats 20000000

def projection (s : Shape) : LarkDotMap.Profile :=
  { LarkFeedForward.stage1 s with post:=.input,validPost:=by trivial }
def upInput (input : Nat → Nat → α) (b i : Nat) : α := if b=0 then input 0 i else input 2 i
def gateValue (s : Shape) (ops : Ops α) (input : Nat → Nat → α) (i : Nat) : α :=
  LarkDotMap.result ops input (projection s) i
def upValue (s : Shape) (ops : Ops α) (input : Nat → Nat → α) (i : Nat) : α :=
  LarkDotMap.result ops (upInput input) (projection s) i
def pairInput (s : Shape) (ops : Ops α) (input : Nat → Nat → α) (b i : Nat) : α :=
  if b=0 then gateValue s ops input i else upValue s ops input i
def hiddenValue (s : Shape) (ops : Ops α) (input : Nat → Nat → α) (i : Nat) : α :=
  LarkSwiPointwise.value ops (gateValue s ops input i) (upValue s ops input i)
def downInput (s : Shape) (ops : Ops α) (input : Nat → Nat → α) (b i : Nat) : α :=
  if b=0 then hiddenValue s ops input i else input 3 i

def gateFinal (s : Shape) (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) : State α :=
  LarkDotMap.partialState ops input outside (projection s) (s.m*s.h)
def upFinal (s : Shape) (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) : State α :=
  LarkDotMap.partialState ops (upInput input) outside (projection s) (s.m*s.h)
def hiddenFinal (s : Shape) (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) : State α :=
  LarkPairMap.partialState (LarkSwiPointwise.profile (s.m*s.h)) ops (pairInput s ops input) outside (s.m*s.h)
def finalState (s : Shape) (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) : State α :=
  LarkDotMap.partialState ops (downInput s ops input) outside (LarkFeedForward.stage2 s) (s.m*s.n)
def spec (s : Shape) (ops : Ops α) (input : Nat → Nat → α) : List α :=
  LarkDotMap.matrixSpec ops (LarkFeedForward.stage2 s) (downInput s ops input)

def pairWired (s : Shape) (ops : Ops α) (input : Nat → Nat → α) (gate up : State α) (b i : Nat) : α :=
  if i<s.m*s.h then ((if b=0 then gate else up).memory (LarkDotMap.cell 2 i)).getD (ops.literal 0 1)
  else pairInput s ops input b i
def downWired (s : Shape) (ops : Ops α) (input : Nat → Nat → α) (hidden : State α) (b i : Nat) : α :=
  if b=0 then
    if i<s.m*s.h then (hidden.memory (LarkPairMap.cell 2 i)).getD (ops.literal 0 1)
    else hiddenValue s ops input i
  else input 3 i

theorem pair_wired_eq (s : Shape) (ops : Ops α) (input : Nat → Nat → α) (og ou : Location → Option α) :
    pairWired s ops input (gateFinal s ops input og) (upFinal s ops input ou)=pairInput s ops input := by
  funext b i
  by_cases hi : i<s.m*s.h
  · by_cases hb : b=0
    · subst b
      have hm:=LarkDotMap.partialState_output ops input og (projection s) (s.m*s.h) i hi
      simp [pairWired,pairInput,gateFinal,gateValue,hi,hm]
    · have hm:=LarkDotMap.partialState_output ops (upInput input) ou (projection s) (s.m*s.h) i hi
      simp [pairWired,pairInput,upFinal,upValue,hi,hb,hm]
  · simp [pairWired,hi]

theorem down_wired_eq (s : Shape) (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) :
    downWired s ops input (hiddenFinal s ops input outside)=downInput s ops input := by
  funext b i
  by_cases hb : b=0
  · subst b
    by_cases hi : i<s.m*s.h
    · have hm:=LarkPairMap.partialState_output (LarkSwiPointwise.profile (s.m*s.h)) ops
        (pairInput s ops input) outside (s.m*s.h) i hi
      simpa [downWired,downInput,hiddenFinal,hi,hiddenValue,LarkSwiPointwise.profile,pairInput] using
        congrArg (fun x : Option α=>x.getD (ops.literal 0 1)) hm
    · simp [downWired,downInput,hi]
  · simp [downWired,downInput,hb]

structure Programs where
  gate : List Instr
  up : List Instr
  combine : List Instr
  down : List Instr
def programs (s : Shape) : Programs :=
  ⟨LarkDotMap.program (projection s),LarkDotMap.program (projection s),
   LarkSwiPointwise.program,LarkDotMap.program (LarkFeedForward.stage2 s)⟩

def RunsWith (s : Shape) (ops : Ops α) (w : Nat) (p : Programs) (input : Nat → Nat → α)
    (start : State α) (ou oh oo : Location → Option α) (fg fu fh fo : State α) : Prop :=
  runLaunch ops (LarkDotMap.layout (projection s)) (LarkDotMap.geometry (projection s) w)
    (LarkDotMap.fuel (projection s)) p.gate start=some fg ∧
  raceFree (LarkDotMap.geometry (projection s) w) fg.trace=true ∧
  extract (LarkDotMap.layout (projection s)) fg=some (LarkDotMap.matrixSpec ops (projection s) input) ∧
  runLaunch ops (LarkDotMap.layout (projection s)) (LarkDotMap.geometry (projection s) w)
    (LarkDotMap.fuel (projection s)) p.up (initial (LarkDotMap.layout (projection s)) (upInput input) ou)=some fu ∧
  raceFree (LarkDotMap.geometry (projection s) w) fu.trace=true ∧
  extract (LarkDotMap.layout (projection s)) fu=some (LarkDotMap.matrixSpec ops (projection s) (upInput input)) ∧
  (∀ i,i<s.m*s.h → pairWired s ops input fg fu 0 i=(fg.memory (LarkDotMap.cell 2 i)).getD (ops.literal 0 1) ∧
    pairWired s ops input fg fu 1 i=(fu.memory (LarkDotMap.cell 2 i)).getD (ops.literal 0 1)) ∧
  runLaunch ops (LarkPairMap.layout (s.m*s.h)) (LarkPairMap.geometry (s.m*s.h) w)
    (LarkPairMap.fuel (LarkSwiPointwise.profile (s.m*s.h))) p.combine
    (initial (LarkPairMap.layout (s.m*s.h)) (pairWired s ops input fg fu) oh)=some fh ∧
  raceFree (LarkPairMap.geometry (s.m*s.h) w) fh.trace=true ∧
  extract (LarkPairMap.layout (s.m*s.h)) fh=
    some (LarkPairMap.spec (LarkSwiPointwise.profile (s.m*s.h)) ops (pairInput s ops input)) ∧
  (∀ i,i<s.m*s.h → downWired s ops input fh 0 i=(fh.memory (LarkPairMap.cell 2 i)).getD (ops.literal 0 1)) ∧
  runLaunch ops (LarkDotMap.layout (LarkFeedForward.stage2 s)) (LarkDotMap.geometry (LarkFeedForward.stage2 s) w)
    (LarkDotMap.fuel (LarkFeedForward.stage2 s)) p.down
    (initial (LarkDotMap.layout (LarkFeedForward.stage2 s)) (downWired s ops input fh) oo)=some fo ∧
  raceFree (LarkDotMap.geometry (LarkFeedForward.stage2 s) w) fo.trace=true ∧
  extract (LarkDotMap.layout (LarkFeedForward.stage2 s)) fo=some (spec s ops input)

def Correct (s : Shape) (ops : Ops α) (w : Nat) (p : Programs) : Prop :=
  ∀ input og ou oh oo,∃ fg fu fh fo,
    RunsWith s ops w p input (initial (LarkDotMap.layout (projection s)) input og) ou oh oo fg fu fh fo

theorem correct (s : Shape) (ops : Ops α) (w : Nat) (hw : 0<w) : Correct s ops w (programs s) := by
  intro input og ou oh oo
  have hn : 0<(projection s).n := Nat.mul_pos s.mPos s.hPos
  have hk : 0<(projection s).k := s.kPos
  have hb : (projection s).n<2147483648 ∧ (projection s).k<2147483648 :=
    ⟨s.hiddenBound,LarkReduction.k_bound s.m s.k s.mPos s.xBound⟩
  have hn2 : 0<(LarkFeedForward.stage2 s).n := Nat.mul_pos s.mPos s.nPos
  have hk2 : 0<(LarkFeedForward.stage2 s).k := s.hPos
  have hb2 : (LarkFeedForward.stage2 s).n<2147483648 ∧ (LarkFeedForward.stage2 s).k<2147483648 :=
    ⟨s.outBound,LarkReduction.k_bound s.m s.h s.mPos s.hiddenBound⟩
  refine ⟨gateFinal s ops input og,upFinal s ops input ou,hiddenFinal s ops input oh,
    finalState s ops input oo,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact LarkDotMap.launch_eq ops input og (projection s) w hn hk hb hw
  · exact LarkReduction.owned_raceFree _ _ (LarkDotMap.partialState_owned ops input og (projection s) (s.m*s.h))
  · have he:=LarkDotMap.extract_eq ops input og (projection s)
    rw [LarkDotMap.spec_eq_matrixSpec] at he
    exact he
  · exact LarkDotMap.launch_eq ops (upInput input) ou (projection s) w hn hk hb hw
  · exact LarkReduction.owned_raceFree _ _ (LarkDotMap.partialState_owned ops (upInput input) ou (projection s) (s.m*s.h))
  · have he:=LarkDotMap.extract_eq ops (upInput input) ou (projection s)
    rw [LarkDotMap.spec_eq_matrixSpec] at he
    exact he
  · intro i hi
    simp [pairWired,hi]
  · rw [pair_wired_eq]
    exact LarkPairMap.launch_eq (LarkSwiPointwise.profile (s.m*s.h)) ops (pairInput s ops input) oh w
      (Nat.mul_pos s.mPos s.hPos) s.hiddenBound hw
  · exact LarkReduction.owned_raceFree _ _ (LarkPairMap.partialState_owned
      (LarkSwiPointwise.profile (s.m*s.h)) ops (pairInput s ops input) oh (s.m*s.h))
  · exact LarkPairMap.extract_eq (LarkSwiPointwise.profile (s.m*s.h)) ops (pairInput s ops input) oh
  · intro i hi
    simp [downWired,hi]
  · rw [down_wired_eq]
    exact LarkDotMap.launch_eq ops (downInput s ops input) oo (LarkFeedForward.stage2 s) w hn2 hk2 hb2 hw
  · exact LarkReduction.owned_raceFree _ _ (LarkDotMap.partialState_owned ops (downInput s ops input) oo
      (LarkFeedForward.stage2 s) (s.m*s.n))
  · have he:=LarkDotMap.extract_eq ops (downInput s ops input) oo (LarkFeedForward.stage2 s)
    rw [LarkDotMap.spec_eq_matrixSpec] at he
    exact he

#print axioms pair_wired_eq
#print axioms down_wired_eq
#print axioms correct
end LarkSwiGLU
