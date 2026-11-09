import Lark.Bias

/-! Interleaved rotary pairs, one output per scalar block, in the unchanged machine. -/
namespace LarkRotary
open LarkNonlinear LarkReduction
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def layout (n : Nat) : Layout :=
  ⟨[⟨.input,2*n⟩,⟨.input,n⟩,⟨.input,n⟩,⟨.output,2*n⟩],[],[]⟩
def geometry (n w : Nat) : Geometry := LarkPointwise.geometry (2*n) w
def fuel : Fuel := ⟨8,1,1,1⟩
def pairIndex : Index := .div (.ivar 0) (.const 2)
def baseIndex : Index := .mul pairIndex (.const 2)
def secondIndex : Index := .add (.ivar 1) (.const 1)
def coeff (b : Nat) : Expr := .un .fromHalf (.load .global b pairIndex)
def body (even : Bool) : Expr :=
  .un .toHalf (.bin (if even then .sub else .add)
    (.bin .mul (.reg 0) (coeff (if even then 1 else 2)))
    (.bin .mul (.reg 1) (coeff (if even then 2 else 1))))
def program : List Instr :=
  [.index 0 .bid, .index 1 baseIndex,
   .assign 0 (.un .fromHalf (.load .global 0 (.ivar 1))),
   .assign 1 (.un .fromHalf (.load .global 0 secondIndex)),
   .branch (.eq (.mod (.ivar 0) (.const 2)) (.const 0)) 7,
   .store .global 3 (.ivar 0) (body true), .jump 8,
   .store .global 3 (.ivar 0) (body false), .halt]

def Reads (n : Nat) (input : Nat → Nat → α) (s : State α) : Prop :=
  (∀ i, i<2*n → s.memory (cell 0 i) = some (input 0 i)) ∧
  (∀ i, i<n → s.memory (cell 1 i) = some (input 1 i)) ∧
  (∀ i, i<n → s.memory (cell 2 i) = some (input 2 i))

def result (ops : Ops α) (input : Nat → Nat → α) (t : Nat) : α :=
  let p := t/2
  let a := ops.fromHalf (input 0 (p*2))
  let b := ops.fromHalf (input 0 (p*2+1))
  let c := ops.fromHalf (input 1 p)
  let d := ops.fromHalf (input 2 p)
  ops.toHalf (if t%2=0 then ops.sub (ops.mul a c) (ops.mul b d)
             else ops.add (ops.mul a d) (ops.mul b c))

def indexed (t : Nat) (s : State α) : State α :=
  setIndex (setIndex s t 0 (t : Int) 1) t 1 (((t/2)*2 : Nat) : Int) 2
def loaded (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) : State α :=
  let s := setReg (record (indexed t s) t (cell 0 ((t/2)*2)) false) t 0
    (ops.fromHalf (input 0 ((t/2)*2))) 3
  setReg (record s t (cell 0 ((t/2)*2+1)) false) t 1
    (ops.fromHalf (input 0 ((t/2)*2+1))) 4
def written (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) : State α :=
  let even := decide (t%2=0)
  let pc := s.pc t+1
  let s := record (record s t (cell (if even then 1 else 2) (t/2)) false)
    t (cell (if even then 2 else 1) (t/2)) false
  advance {record s t (cell 3 t) true with
    memory := fun l => if l=cell 3 t then some (result ops input t) else s.memory l} t pc
def after (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) : State α :=
  let even := decide (t%2=0)
  advance (written ops input t (advance (loaded ops input t s) t (if even then 5 else 7))) t 8

theorem pair_bounds (n t : Nat) (ht : t<2*n) : t/2<n ∧ (t/2)*2+1<2*n := by omega

theorem eval_pair (g : Geometry) (t : Nat) (s : State α)
    (hi : s.indices t 0=some (t : Int)) :
    evalIndex g t s pairIndex = some ((t/2 : Nat) : Int) := by
  exact LarkMatrix.eval_div_nat g t s (.ivar 0) (.const 2) t 2 hi (by rfl) (by decide)

theorem eval_base (g : Geometry) (t : Nat) (s : State α)
    (hi : s.indices t 0=some (t : Int)) (hb : t<2147483648) :
    evalIndex g t s baseIndex = some (((t/2)*2 : Nat) : Int) := by
  exact LarkMatrix.eval_mul_nat g t s pairIndex (.const 2) (t/2) 2
    (eval_pair g t s hi) (by rfl) (by omega)

theorem eval_second (g : Geometry) (t : Nat) (s : State α)
    (hi : s.indices t 1=some (((t/2)*2 : Nat) : Int))
    (hb : (t/2)*2+1<2147483648) :
    evalIndex g t s secondIndex = some (((t/2)*2+1 : Nat) : Int) := by
  exact LarkMatrix.eval_add_nat g t s (.ivar 1) (.const 1) ((t/2)*2) 1 hi (by rfl) hb

theorem load_of (ops : Ops α) (n w t b i : Nat) (ix : Index) (s : State α)
    (input : Nat → Nat → α) (hb : b<3) (hi : i<(if b=0 then 2*n else n))
    (hr : Reads n input s) (he : evalIndex (geometry n w) t s ix=some (i : Int)) :
    evalExpr ops (layout n) (geometry n w) t (.un .fromHalf (.load .global b ix)) s =
      some (ops.fromHalf (input b i), record s t (cell b i) false) := by
  have hm : s.memory (cell b i)=some (input b i) := by
    rcases (show b=0 ∨ b=1 ∨ b=2 by omega) with rfl|rfl|rfl
    · exact hr.1 i hi
    · exact hr.2.1 i hi
    · exact hr.2.2 i hi
  have hl : location (layout n) (geometry n w) t .global b (i : Int) false=some (cell b i) := by
    have hneg : ¬ (i : Int)<0 := by omega
    rcases (show b=0 ∨ b=1 ∨ b=2 by omega) with rfl|rfl|rfl <;>
      simp [location,layout,cell,hneg] at hi ⊢ <;> exact hi
  simp only [evalExpr,he,bind,pure,Option.bind,hl,hm]
  rfl

theorem execute_assign_of (ops : Ops α) (l : Layout) (g : Geometry) (t r pc : Nat)
    (e : Expr) (s s1 : State α) (v : α) (he : evalExpr ops l g t e s=some (v,s1))
    (hp : s.pc t+1=pc) : execute ops l g t (.assign r e) s=some (setReg s1 t r v pc) := by
  simp only [execute,he,hp,bind,pure,Option.bind]
  rfl

theorem header_eq (ops : Ops α) (n w t f : Nat) (s : State α)
    (input : Nat → Nat → α) (hr : Reads n input s) (hp : s.pc t=0)
    (ht : t<2*n) (hb : 2*n<2147483648) :
    runLane ops (layout n) (geometry n w) program t (f+4) s =
      runLane ops (layout n) (geometry n w) program t f (loaded ops input t s) := by
  let s1 := setIndex s t 0 (t : Int) 1
  let s2 := indexed t s
  let s3 := setReg (record s2 t (cell 0 ((t/2)*2)) false) t 0
    (ops.fromHalf (input 0 ((t/2)*2))) 3
  have hbid := bid_index (2*n) w t s (by omega)
  have h1 : execute ops (layout n) (geometry n w) t (.index 0 .bid) s = some s1 :=
    execute_index_of ops _ _ t 0 1 .bid s (t : Int) hbid (by omega)
  have hbase := eval_base (geometry n w) t s1 (by simp [s1,setIndex,advance]) (by omega)
  have h2 : execute ops (layout n) (geometry n w) t (.index 1 baseIndex) s1 = some s2 :=
    execute_index_of ops _ _ t 1 2 baseIndex s1 _ hbase (by simp [s1,setIndex,advance])
  have hbounds := pair_bounds n t ht
  have hx0 := load_of ops n w t 0 ((t/2)*2) (.ivar 1) s2 input (by decide)
    (by simp; omega) hr (by simp [evalIndex,s2,indexed,setIndex,advance])
  have h3 : execute ops (layout n) (geometry n w) t
      (.assign 0 (.un .fromHalf (.load .global 0 (.ivar 1)))) s2 = some s3 := by
    exact execute_assign_of ops _ _ t 0 3 _ s2 _ _ hx0
      (by simp [s2,indexed,setIndex,advance])
  have hsix : evalIndex (geometry n w) t s3 secondIndex =
      some (((t/2)*2+1 : Nat) : Int) :=
    eval_second (geometry n w) t s3
      (by simp [s3,s2,indexed,setReg,setIndex,record,advance]) (by omega)
  have hx1 := load_of ops n w t 0 ((t/2)*2+1) secondIndex s3 input (by decide)
    (by simpa using hbounds.2) hr hsix
  have h4 : execute ops (layout n) (geometry n w) t
      (.assign 1 (.un .fromHalf (.load .global 0 secondIndex))) s3 =
      some (loaded ops input t s) :=
    execute_assign_of ops _ _ t 1 4 _ s3 _ _ hx1 (by simp [s3,setReg,advance])
  rw [LarkPointwise.lane_step ops _ _ _ _ _ _ _ _
    (by simp [parked,program,hp]) (by simp [program,hp]) h1]
  rw [LarkPointwise.lane_step ops _ _ _ _ _ _ _ _
    (by simp [parked,program,s1,setIndex,advance]) (by simp [program,s1,setIndex,advance]) h2]
  rw [LarkPointwise.lane_step ops _ _ _ _ _ _ _ _
    (by simp [parked,program,s2,indexed,setIndex,advance])
    (by simp [program,s2,indexed,setIndex,advance]) h3]
  rw [LarkPointwise.lane_step ops _ _ _ _ _ _ _ _
    (by simp [parked,program,s3,setReg,advance]) (by simp [program,s3,setReg,advance]) h4]

theorem body_eq (ops : Ops α) (n w t : Nat) (s : State α) (input : Nat → Nat → α)
    (hr : Reads n input s) (hi : s.indices t 0=some (t : Int))
    (ha : s.regs t 0=some (ops.fromHalf (input 0 ((t/2)*2))))
    (hb : s.regs t 1=some (ops.fromHalf (input 0 ((t/2)*2+1)))) (ht : t<2*n) :
    evalExpr ops (layout n) (geometry n w) t (body (decide (t%2=0))) s =
      some (result ops input t,
        record (record s t (cell (if t%2=0 then 1 else 2) (t/2)) false)
          t (cell (if t%2=0 then 2 else 1) (t/2)) false) := by
  let first := if t%2=0 then 1 else 2
  let second := if t%2=0 then 2 else 1
  have hfb : first<3 := by unfold first; split <;> decide
  have hsb : second<3 := by unfold second; split <;> decide
  have hfi : t/2<(if first=0 then 2*n else n) := by
    have h0 : first≠0 := by unfold first; split <;> decide
    simp only [h0,↓reduceIte]
    exact (pair_bounds n t ht).1
  have hsi : t/2<(if second=0 then 2*n else n) := by
    have h0 : second≠0 := by unfold second; split <;> decide
    simp only [h0,↓reduceIte]
    exact (pair_bounds n t ht).1
  have hc1 := load_of ops n w t first (t/2) pairIndex s input hfb hfi hr
    (eval_pair (geometry n w) t s hi)
  have hra : evalExpr ops (layout n) (geometry n w) t (.reg 0) s =
      some (ops.fromHalf (input 0 ((t/2)*2)),s) := by simp [evalExpr,ha]
  have hprod1 := eval_bin_of ops (layout n) (geometry n w) t .mul _ _ _ _ _ _ _ hra hc1
  let s1 := record s t (cell first (t/2)) false
  have hc2 := load_of ops n w t second (t/2) pairIndex s1 input hsb hsi hr
    (eval_pair (geometry n w) t s1 hi)
  have hrb : evalExpr ops (layout n) (geometry n w) t (.reg 1) s1 =
      some (ops.fromHalf (input 0 ((t/2)*2+1)),s1) := by simp [evalExpr,s1,record,hb]
  have hprod2 := eval_bin_of ops (layout n) (geometry n w) t .mul _ _ _ _ _ _ _ hrb hc2
  have hsum := eval_bin_of ops (layout n) (geometry n w) t
    (if t%2=0 then .sub else .add) _ _ _ _ _ _ _ hprod1 hprod2
  have hall := LarkBias.eval_un_of ops (layout n) (geometry n w) t .toHalf _ _ _ _ hsum
  by_cases h : t%2=0 <;>
    simpa [body,result,first,second,s1,coeff,h,applyBinary,applyUnary] using hall

theorem store_eq (ops : Ops α) (n w t : Nat) (s : State α) (input : Nat → Nat → α)
    (hr : Reads n input s) (hi : s.indices t 0=some (t : Int))
    (ha : s.regs t 0=some (ops.fromHalf (input 0 ((t/2)*2))))
    (hb : s.regs t 1=some (ops.fromHalf (input 0 ((t/2)*2+1)))) (ht : t<2*n) :
    execute ops (layout n) (geometry n w) t
      (.store .global 3 (.ivar 0) (body (decide (t%2=0)))) s =
        some (written ops input t s) := by
  have he := body_eq ops n w t s input hr hi ha hb ht
  have hneg : ¬ (t : Int)<0 := by omega
  have hrole : (Role.output == Role.input)=false := by decide
  have hl : location (layout n) (geometry n w) t .global 3 (t : Int) true=some (cell 3 t) := by
    simp [location,layout,cell,hneg,ht,hrole]
  simp only [execute,evalIndex,hi,bind,pure,Option.bind,hl,he]
  by_cases h : t%2=0 <;> simp [written,h,record]

theorem lane_eq (ops : Ops α) (n w t : Nat) (s : State α) (input : Nat → Nat → α)
    (hr : Reads n input s) (hp : s.pc t=0) (ht : t<2*n) (hb : 2*n<2147483648) :
    runLane ops (layout n) (geometry n w) program t fuel.lane s =
      some (after ops input t s) := by
  change runLane ops (layout n) (geometry n w) program t (4+4) s = _
  rw [header_eq ops n w t 4 s input hr hp ht hb]
  let x := loaded ops input t s
  let y := advance x t (if t%2=0 then 5 else 7)
  let z := written ops input t y
  have hi : x.indices t 0=some (t : Int) := by
    simp [x,loaded,indexed,setReg,setIndex,advance,record]
  have hmod := LarkMatrix.eval_mod_nat (geometry n w) t x (.ivar 0) (.const 2) t 2 hi
    (by rfl) (by decide)
  have hpred : evalPredicate (geometry n w) t x
      (.eq (.mod (.ivar 0) (.const 2)) (.const 0))=some (decide (t%2=0)) := by
    have heq : ((t%2 : Nat) : Int)=0 ↔ t%2=0 := by omega
    simp only [evalPredicate,hmod,bind,pure,Option.bind]
    change some (decide (((t%2 : Nat) : Int)=0))=some (decide (t%2=0))
    simp only [heq]
  have hbranch : execute ops (layout n) (geometry n w) t
      (.branch (.eq (.mod (.ivar 0) (.const 2)) (.const 0)) 7) x=some y := by
    simp only [execute,hpred,bind,pure,Option.bind]
    by_cases h : t%2=0 <;> simp [y,x,loaded,setReg,advance,h]
  have hstore := store_eq ops n w t y input hr
    (by simpa [y,advance] using hi)
    (by simp [y,x,loaded,indexed,setReg,setIndex,advance,record])
    (by simp [y,x,loaded,indexed,setReg,setIndex,advance,record]) ht
  rw [LarkPointwise.lane_step ops _ _ _ _ _ _ _ _
    (by simp [parked,program,x,loaded,setReg,advance])
    (by simp [program,x,loaded,setReg,advance]) hbranch]
  by_cases h : t%2=0
  · simp only [h,decide_true] at hstore
    rw [LarkPointwise.lane_step ops _ _ _ _ _ _ _ _
      (by simp [parked,program,y,advance,h]) (by simp [program,y,advance,h]) hstore]
    have hjump : execute ops (layout n) (geometry n w) t (.jump 8) z=
        some (after ops input t s) := by
      simp [execute,z,after,y,x,h]
    rw [LarkPointwise.lane_step ops _ _ _ _ _ _ _ _
      (by simp [parked,program,z,written,y,advance,record,h])
      (by simp [program,z,written,y,advance,record,h]) hjump]
    simp [runLane,parked,program,after,advance]
  · simp only [h,decide_false] at hstore
    rw [LarkPointwise.lane_step ops _ _ _ _ _ _ _ _
      (by simp [parked,program,y,advance,h]) (by simp [program,y,advance,h]) hstore]
    have hz : z=after ops input t s := by
      simp [z,after,written,y,x,h,advance,record]
      funext u
      by_cases hu : u=t <;> simp [hu]
    change runLane ops (layout n) (geometry n w) program t 2 z = _
    rw [hz]
    simp [runLane,parked,program,after,advance]

theorem after_memory (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α)
    (l : Location) : (after ops input t s).memory l =
      if l=cell 3 t then some (result ops input t) else s.memory l := by
  simp [after,written,loaded,indexed,setReg,setIndex,advance,record]

theorem after_pc (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α)
    (u : Nat) : (after ops input t s).pc u = if u=t then 8 else s.pc u := by
  by_cases h : u=t <;> simp [after,written,loaded,indexed,setReg,setIndex,advance,record,h]

theorem after_reads (ops : Ops α) (input : Nat → Nat → α) (n t : Nat) (s : State α)
    (hr : Reads n input s) : Reads n input (after ops input t s) := by
  constructor
  · intro i hi
    simpa [after_memory,cell] using hr.1 i hi
  · constructor
    · intro i hi
      simpa [after_memory,cell] using hr.2.1 i hi
    · intro i hi
      simpa [after_memory,cell] using hr.2.2 i hi

theorem after_owned (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α)
    (h : LarkBias.Owned s.trace) : LarkBias.Owned (after ops input t s).trace := by
  intro a ha
  by_cases he : t%2=0 <;>
    simp only [after,written,loaded,indexed,setReg,setIndex,advance,record,he,
      decide_true,decide_false,↓reduceIte,List.mem_cons] at ha <;>
    rcases ha with rfl|rfl|rfl|rfl|rfl|ha
  all_goals first | exact h a ha | simp [cell,LarkBias.cell]

def partialState (ops : Ops α) (n : Nat) (input : Nat → Nat → α)
    (outside : Location → Option α) : Nat → State α
  | 0 => initial (layout n) input outside
  | k+1 => after ops input k (partialState ops n input outside k)

theorem partialState_pc (ops : Ops α) (n : Nat) (input : Nat → Nat → α)
    (outside : Location → Option α) (k t : Nat) :
    (partialState ops n input outside k).pc t=if t<k then 8 else 0 := by
  induction k with
  | zero => simp [partialState,initial]
  | succ k ih =>
    simp only [partialState,after_pc,ih]
    by_cases h : t=k
    · simp [h]
    · by_cases h' : t<k
      · have hh : t<k+1 := by omega
        simp [h,h',hh]
      · have hh : ¬ t<k+1 := by omega
        simp [h,h',hh]

theorem partialState_reads (ops : Ops α) (n : Nat) (input : Nat → Nat → α)
    (outside : Location → Option α) (k : Nat) :
    Reads n input (partialState ops n input outside k) := by
  induction k with
  | zero =>
    constructor
    · intro i hi
      simp [partialState,initial,layout,cell,hi]
    · constructor
      · intro i hi
        simp [partialState,initial,layout,cell,hi]
      · intro i hi
        simp [partialState,initial,layout,cell,hi]
  | succ k ih => exact after_reads ops input n k _ ih

theorem partialState_output (ops : Ops α) (n : Nat) (input : Nat → Nat → α)
    (outside : Location → Option α) (k t : Nat) (ht : t<k) :
    (partialState ops n input outside k).memory (cell 3 t)=some (result ops input t) := by
  induction k with
  | zero => omega
  | succ k ih =>
    simp only [partialState,after_memory,cell,Location.mk.injEq,and_self_left,true_and]
    by_cases h : t=k
    · simp [h]
    · simpa [h,cell] using ih (by omega)

theorem partialState_owned (ops : Ops α) (n : Nat) (input : Nat → Nat → α)
    (outside : Location → Option α) (k : Nat) :
    LarkBias.Owned (partialState ops n input outside k).trace := by
  induction k with
  | zero => simp [LarkBias.Owned,partialState,initial]
  | succ k ih => exact after_owned ops input k _ ih

theorem block_eq (ops : Ops α) (n w t : Nat)
    (input : Nat → Nat → α) (outside : Location → Option α)
    (ht : t < 2*n) (hn : 2*n < 2147483648) (hw : 0 < w) :
    runBlock ops (layout n) (geometry n w) fuel (program) t fuel.block
      (partialState ops n input outside t) =
      some (partialState ops n input outside (t + 1)) := by
  have hl := lane_eq ops n w t (partialState ops n input outside t) input
    (partialState_reads ops n input outside t) (by simp [partialState_pc]) ht hn
  change runLane ops (layout n) (geometry n w) (program) t fuel.lane
    (partialState ops n input outside t) =
    some (partialState ops n input outside (t+1)) at hl
  have hd : (1 + w - 1) / w = 1 := by
    have he : 1 + w - 1 = w := by omega
    rw [he, Nat.div_self (by omega)]
  have hwne : w ≠ 0 := by omega
  have hwarp : warpThreads (geometry n w) t 0 = [t] := by
    simp [warpThreads, geometry,LarkPointwise.geometry, List.range_succ, hwne]
  have hblock : blockThreads (geometry n w) t = [t] := by
    simp [blockThreads, geometry,LarkPointwise.geometry, List.range_succ]
  have hc : converged (program) [t] (partialState ops n input outside (t+1)) =
      some .halt := by simp [converged, partialState_pc, parked, program]
  have hr : runWarp ops (layout n) (geometry n w) fuel (program) [t] fuel.warp
      (partialState ops n input outside t) =
      some (partialState ops n input outside (t+1)) := by
    change runWarp ops (layout n) (geometry n w) fuel (program) [t] 1 _ = _
    rw [runWarp]
    simp only [List.foldlM_cons, List.foldlM_nil, bind, pure, Option.bind, hl, hc]
    rfl
  have hws : List.range (((geometry n w).block + (geometry n w).warp - 1) /
      (geometry n w).warp) = [0] := by
    simp [geometry,LarkPointwise.geometry, hd, List.range_succ]
  change runBlock ops (layout n) (geometry n w) fuel (program) t 1 _ = _
  rw [runBlock, hws]
  simp only [List.foldlM_cons, List.foldlM_nil, hwarp, hr, bind, pure, Option.bind,
    hblock, hc]
  rfl

theorem blocks_eq (ops : Ops α) (n w k : Nat)
    (input : Nat → Nat → α) (outside : Location → Option α)
    (hk : k ≤ 2*n) (hn : 2*n < 2147483648) (hw : 0 < w) :
    (List.range k).foldlM (fun s b =>
      runBlock ops (layout n) (geometry n w) fuel (program) b fuel.block s)
      (initial (layout n) input outside) = some (partialState ops n input outside k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [List.range_succ, List.foldlM_append, ih (by omega)]
      simp [block_eq ops n w k input outside (by omega) hn hw]

def spec (ops : Ops α) (n : Nat) (input : Nat → Nat → α) : List α :=
  (List.range (2*n)).map (fun t => result ops input t)

theorem partialState_extract (ops : Ops α) (n : Nat) (input : Nat → Nat → α)
    (outside : Location → Option α) :
    extract (layout n) (partialState ops n input outside (2*n))=some (spec ops n input) := by
  simp only [extract,layout,List.zipIdx_cons,List.zipIdx_nil,List.flatMap_cons,
    List.flatMap_nil,List.nil_append]
  simp only [List.map_cons,List.map_nil,show Role.input≠Role.output by decide,
    ↓reduceIte,List.nil_append,List.append_nil]
  change (((List.range (2*n)).map (fun i => (3,i))).mapM
    (fun bi => (partialState ops n input outside (2*n)).memory (cell bi.1 bi.2)) : Option (List α)) = _
  rw [LarkPointwise.mapM_map]
  exact LarkPointwise.mapM_some (List.range (2*n)) _ _ (by
    intro i hi
    exact partialState_output ops n input outside (2*n) i (List.mem_range.mp hi))

theorem converged_done (s : State α) (ts : List Nat)
    (hne : ts ≠ []) (hp : ∀ t ∈ ts, s.pc t = 8) :
    converged (program) ts s = some .halt := by
  cases ts with
  | nil => contradiction
  | cons t ts =>
      have ht := hp t (by simp)
      have ha : (t :: ts).all (fun u => s.pc u == s.pc t) = true := by
        apply List.all_eq_true.mpr
        intro u hu
        simp [hp u hu, ht]
      simp only [ht] at ha
      simp only [converged, List.head?_cons, bind, pure, Option.bind,
        ↓reduceIte, parked, ht, program]
      rw [ha]
      rfl

theorem launch_eq (ops : Ops α) (n w : Nat)
    (input : Nat → Nat → α) (outside : Location → Option α)
    (hn : 0 < n) (hb : 2*n < 2147483648) (hw : 0 < w) :
    runLaunch ops (layout n) (geometry n w) fuel (program)
      (initial (layout n) input outside) = some (partialState ops n input outside (2*n)) := by
  have hfold := blocks_eq ops n w (2*n) input outside (by omega) hb hw
  have hne : List.range (2*n) ≠ [] := by
    intro he
    have hh := congrArg List.length he
    simp at hh
    omega
  have hc := converged_done (partialState ops n input outside (2*n)) (List.range (2*n)) hne
    (by intro t ht; simp [partialState_pc, List.mem_range.mp ht])
  simp only [runLaunch, geometry,LarkPointwise.geometry, show 2*n ≠ 0 by omega, show w ≠ 0 by omega,
    or_false, false_or, reduceCtorEq, ↓reduceIte, fuel, runGrid]
  change ((List.range (2*n)).foldlM (fun s b =>
    runBlock ops (layout n) (geometry n w) fuel (program) b fuel.block s)
      (initial (layout n) input outside)).bind _ = _
  rw [hfold]
  simp only [bind, pure, Option.bind]
  simp only [Nat.mul_one, hc]
  rfl

/-- Full machine completion, race freedom, and all output cells, by induction. -/
theorem correct (ops : Ops α) (n w : Nat)
    (hn : 0 < n) (hb : 2*n < 2147483648) (hw : 0 < w) :
    Correct ops (layout n) (geometry n w) fuel (program) (spec ops n) := by
  intro input outside
  refine ⟨partialState ops n input outside (2*n),
    launch_eq ops n w input outside hn hb hw, ?_,
    partialState_extract ops n input outside⟩
  exact LarkBias.owned_raceFree (geometry n w) _ (partialState_owned ops n input outside (2*n))

#print axioms header_eq
#print axioms body_eq
#print axioms store_eq
#print axioms lane_eq
#print axioms partialState_owned
#print axioms correct
end LarkRotary
