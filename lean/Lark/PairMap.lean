import Lark.DotMap

/-! Grid assembly for checked scalar lanes with two read-only arrays and one output. -/
namespace LarkPairMap
open LarkNonlinear
open LarkReduction (owned_raceFree)
set_option maxRecDepth 10000
set_option maxHeartbeats 20000000

def layout (n : Nat) : Layout := ⟨[⟨.input,n⟩,⟨.input,n⟩,⟨.output,n⟩],[],[]⟩
def geometry (n w : Nat) : Geometry := LarkPointwise.geometry n w
def cell (b i : Nat) : Location := ⟨.global,0,b,i⟩
def Reads (n : Nat) (input : Nat → Nat → α) (s : State α) : Prop :=
  ∀ b,b<2 → ∀ i,i<n → s.memory (cell b i)=some (input b i)
def Owned (tr : List Access) : Prop := LarkReduction.Owned tr

structure Profile where
  n : Nat
  program : List Instr
  laneFuel : Nat
  haltPc : Nat
  halt : program[haltPc]?=some .halt
  value : (α : Type) → Ops α → (Nat → Nat → α) → Nat → α
  after : (α : Type) → Ops α → (Nat → Nat → α) → Nat → State α → State α
  afterMemory : ∀ (α : Type) (ops : Ops α) input t s l,
    (after α ops input t s).memory l=
      if l=cell 2 t then some (value α ops input t) else s.memory l
  afterPc : ∀ (α : Type) (ops : Ops α) input t s u,
    (after α ops input t s).pc u=if u=t then haltPc else s.pc u
  afterOwned : ∀ (α : Type) (ops : Ops α) input t s,
    Owned s.trace → Owned (after α ops input t s).trace
  laneEq : ∀ (α : Type) (ops : Ops α) w t s input,
    t<n → n<2147483648 → s.pc t=0 → Reads n input s →
    runLane ops (layout n) (geometry n w) program t laneFuel s=some (after α ops input t s)

def fuel (p : Profile) : Fuel := ⟨p.laneFuel,1,1,1⟩
def partialState (p : Profile) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) : Nat → State α
  | 0 => initial (layout p.n) input outside
  | q+1 => p.after α ops input q (partialState p ops input outside q)

theorem partialState_pc (p : Profile) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (q t : Nat) :
    (partialState p ops input outside q).pc t=if t<q then p.haltPc else 0 := by
  induction q with
  | zero => simp [partialState,initial]
  | succ q ih =>
    simp only [partialState,p.afterPc,ih]
    by_cases h : t=q
    · simp [h]
    · by_cases h' : t<q
      · have hh : t<q+1 := by omega
        simp [h,h',hh]
      · have hh : ¬ t<q+1 := by omega
        simp [h,h',hh]

theorem partialState_reads (p : Profile) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (q : Nat) :
    Reads p.n input (partialState p ops input outside q) := by
  induction q with
  | zero =>
    intro b hb i hi
    rcases (show b=0 ∨ b=1 by omega) with rfl|rfl <;>
      simp [partialState,initial,layout,cell,hi]
  | succ q ih =>
    intro b hb i hi
    have hne : b≠2 := by omega
    simpa [partialState,p.afterMemory,cell,hne] using ih b hb i hi

theorem partialState_output (p : Profile) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (q t : Nat) (ht : t<q) :
    (partialState p ops input outside q).memory (cell 2 t)=some (p.value α ops input t) := by
  induction q with
  | zero => omega
  | succ q ih =>
    simp only [partialState,p.afterMemory,cell,Location.mk.injEq,and_self_left,true_and]
    by_cases h : t=q
    · simp [h]
    · simpa [h,cell] using ih (by omega)

theorem partialState_owned (p : Profile) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (q : Nat) : Owned (partialState p ops input outside q).trace := by
  induction q with
  | zero => simp [Owned,LarkReduction.Owned,partialState,initial]
  | succ q ih => exact p.afterOwned α ops input q _ ih

theorem converged_done (p : Profile) (s : State α) (ts : List Nat)
    (hne : ts≠[]) (hp : ∀t∈ts,s.pc t=p.haltPc) : converged p.program ts s=some .halt := by
  cases ts with
  | nil => contradiction
  | cons t ts =>
    have ht:=hp t (by simp)
    have ha : (t::ts).all (fun u=>s.pc u==s.pc t)=true := by
      apply List.all_eq_true.mpr
      intro u hu
      simp [hp u hu,ht]
    simp only [ht] at ha
    simp only [converged,List.head?_cons,bind,pure,Option.bind,↓reduceIte,parked,ht,p.halt]
    rw [ha]
    rfl

theorem block_eq (p : Profile) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (w t : Nat) (ht : t<p.n)
    (hb : p.n<2147483648) (hw : 0<w) :
    runBlock ops (layout p.n) (geometry p.n w) (fuel p) p.program t (fuel p).block
      (partialState p ops input outside t)=some (partialState p ops input outside (t+1)) := by
  have hl:=p.laneEq α ops w t (partialState p ops input outside t) input ht hb
    (by simp [partialState_pc]) (partialState_reads p ops input outside t)
  change runLane ops (layout p.n) (geometry p.n w) p.program t (fuel p).lane
    (partialState p ops input outside t)=some (partialState p ops input outside (t+1)) at hl
  have hd : (1+w-1)/w=1 := by
    have he : 1+w-1=w := by omega
    rw [he,Nat.div_self (by omega)]
  have hwne : w≠0 := by omega
  have hwarp : warpThreads (geometry p.n w) t 0=[t] := by
    simp [warpThreads,geometry,LarkPointwise.geometry,List.range_succ,hwne]
  have hblock : blockThreads (geometry p.n w) t=[t] := by
    simp [blockThreads,geometry,LarkPointwise.geometry,List.range_succ]
  have hc : converged p.program [t] (partialState p ops input outside (t+1))=some .halt := by
    apply converged_done
    · simp
    · intro u hu
      simp only [List.mem_singleton] at hu
      subst u
      simp [partialState_pc]
  have hr : runWarp ops (layout p.n) (geometry p.n w) (fuel p) p.program [t] (fuel p).warp
      (partialState p ops input outside t)=some (partialState p ops input outside (t+1)) := by
    change runWarp ops (layout p.n) (geometry p.n w) (fuel p) p.program [t] 1 _ = _
    rw [runWarp]
    simp only [List.foldlM_cons,List.foldlM_nil,bind,pure,Option.bind,hl,hc]
    rfl
  have hws : List.range (((geometry p.n w).block+(geometry p.n w).warp-1)/(geometry p.n w).warp)=[0] := by
    simp [geometry,LarkPointwise.geometry,hd,List.range_succ]
  change runBlock ops (layout p.n) (geometry p.n w) (fuel p) p.program t 1 _ = _
  rw [runBlock,hws]
  simp only [List.foldlM_cons,List.foldlM_nil,hwarp,hr,bind,pure,Option.bind,hblock,hc]
  rfl

theorem blocks_eq (p : Profile) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (w q : Nat) (hq : q≤p.n)
    (hb : p.n<2147483648) (hw : 0<w) :
    (List.range q).foldlM (fun s t=>runBlock ops (layout p.n) (geometry p.n w)
      (fuel p) p.program t (fuel p).block s) (initial (layout p.n) input outside)=
      some (partialState p ops input outside q) := by
  induction q with
  | zero => rfl
  | succ q ih =>
    rw [List.range_succ,List.foldlM_append,ih (by omega)]
    simp [block_eq p ops input outside w q (by omega) hb hw]

theorem launch_eq (p : Profile) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (w : Nat) (hn : 0<p.n)
    (hb : p.n<2147483648) (hw : 0<w) :
    runLaunch ops (layout p.n) (geometry p.n w) (fuel p) p.program
      (initial (layout p.n) input outside)=some (partialState p ops input outside p.n) := by
  have hfold:=blocks_eq p ops input outside w p.n (by omega) hb hw
  have hne : List.range p.n≠[] := by
    intro he
    have hh:=congrArg List.length he
    simp at hh
    omega
  have hc:=converged_done p (partialState p ops input outside p.n) (List.range p.n) hne
    (by intro t ht; simp [partialState_pc,List.mem_range.mp ht])
  simp only [runLaunch,geometry,LarkPointwise.geometry,show p.n≠0 by omega,
    show w≠0 by omega,or_false,false_or,reduceCtorEq,↓reduceIte,fuel,runGrid]
  change ((List.range p.n).foldlM (fun s t=>runBlock ops (layout p.n) (geometry p.n w)
    (fuel p) p.program t (fuel p).block s) (initial (layout p.n) input outside)).bind _ = _
  rw [hfold]
  simp only [bind,pure,Option.bind,Nat.mul_one,hc]
  rfl

def spec (p : Profile) (ops : Ops α) (input : Nat → Nat → α) : List α :=
  (List.range p.n).map (p.value α ops input)

theorem extract_eq (p : Profile) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) :
    extract (layout p.n) (partialState p ops input outside p.n)=some (spec p ops input) := by
  simp only [extract,layout,List.zipIdx_cons,List.zipIdx_nil,List.flatMap_cons,
    List.flatMap_nil,List.nil_append]
  simp only [List.map_cons,List.map_nil,show Role.input≠Role.output by decide,
    ↓reduceIte,List.nil_append,List.append_nil]
  change (((List.range p.n).map (fun i=>(2,i))).mapM
    (fun bi=>(partialState p ops input outside p.n).memory (cell bi.1 bi.2)) : Option (List α)) = _
  rw [LarkPointwise.mapM_map]
  exact LarkPointwise.mapM_some (List.range p.n) _ _ (by
    intro i hi
    exact partialState_output p ops input outside p.n i (List.mem_range.mp hi))

theorem correct (p : Profile) (ops : Ops α) (w : Nat) (hn : 0<p.n)
    (hb : p.n<2147483648) (hw : 0<w) :
    Correct ops (layout p.n) (geometry p.n w) (fuel p) p.program (spec p ops) := by
  intro input outside
  refine ⟨partialState p ops input outside p.n,
    launch_eq p ops input outside w hn hb hw,?_,extract_eq p ops input outside⟩
  exact owned_raceFree (geometry p.n w) _ (partialState_owned p ops input outside p.n)

#print axioms correct
end LarkPairMap
