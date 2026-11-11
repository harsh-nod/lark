import Lark.Nonlinear

/-!
An induction-based proof for a deliberately narrow pointwise launch profile.
The conclusion uses the existing Nonlinear.runLaunch and Correct definitions.
One thread per block, one input/output cell per block, no synchronization.
No floating-point laws or unproved refinement axioms are used.
-/
namespace LarkPointwise
open LarkNonlinear
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

inductive Scalar where
  | input
  | lit : Int → Nat → Scalar
  | bin : Binary → Scalar → Scalar → Scalar
  | un : Unary → Scalar → Scalar
  deriving Repr

def lower : Scalar → Expr
  | .input => .reg 0
  | .lit n d => .lit n d
  | .bin op a b => .bin op (lower a) (lower b)
  | .un op a => .un op (lower a)

def Valid : Scalar → Prop
  | .input => True
  | .lit _ d => d ≠ 0
  | .bin _ a b => Valid a ∧ Valid b
  | .un _ a => Valid a

def value (ops : Ops α) (x : α) : Scalar → α
  | .input => x
  | .lit n d => ops.literal n d
  | .bin op a b => applyBinary ops op (value ops x a) (value ops x b)
  | .un op a => applyUnary ops op (value ops x a)

theorem eval_lower (ops : Ops α) (layout : Layout) (g : Geometry) (t : Nat)
    (s : State α) (x : α) (e : Scalar) (hv : Valid e) (hx : s.regs t 0 = some x) :
    evalExpr ops layout g t (lower e) s = some (value ops x e, s) := by
  induction e with
  | input => simp [lower, value, evalExpr, hx]
  | lit n d => simp [lower, value, evalExpr, Valid] at hv ⊢; exact hv
  | bin op a b ha hb =>
      simp only [Valid] at hv
      simp [lower, value, evalExpr, ha hv.1, hb hv.2]
  | un op a ha => simp [lower, value, evalExpr, ha hv]

def layout (n : Nat) : Layout := ⟨[⟨.input, n⟩, ⟨.output, n⟩], [], []⟩
def geometry (n w : Nat) : Geometry := ⟨n, 1, w⟩
def fuel : Fuel := ⟨4, 1, 1, 1⟩
def program (e : Scalar) : List Instr :=
  [.index 0 .bid,
   .assign 0 (.un .fromHalf (.load .global 0 (.ivar 0))),
   .store .global 1 (.ivar 0) (.un .toHalf (lower e)), .halt]

def inputCell (i : Nat) : Location := ⟨.global, 0, 0, i⟩
def outputCell (i : Nat) : Location := ⟨.global, 0, 1, i⟩
def result (ops : Ops α) (e : Scalar) (x : α) : α :=
  ops.toHalf (value ops (ops.fromHalf x) e)

def indexed (t : Nat) (s : State α) : State α :=
  advance { s with indices := fun u r =>
    if u = t ∧ r = 0 then some (Int.ofNat t) else s.indices u r } t 1

def loaded (ops : Ops α) (t : Nat) (x : α) (s : State α) : State α :=
  advance { record (indexed t s) t (inputCell t) false with
    regs := fun u r => if u = t ∧ r = 0 then some (ops.fromHalf x) else s.regs u r } t 2

def after (ops : Ops α) (e : Scalar) (t : Nat) (x : α) (s : State α) : State α :=
  advance { record (loaded ops t x s) t (outputCell t) true with
    memory := fun l => if l = outputCell t then some (result ops e x) else s.memory l } t 3

theorem lane_step (ops : Ops α) (l : Layout) (g : Geometry) (p : List Instr)
    (t k : Nat) (s s' : State α) (i : Instr)
    (hp : parked p s t = none) (hi : p[s.pc t]? = some i)
    (he : execute ops l g t i s = some s') :
    runLane ops l g p t (k + 1) s = runLane ops l g p t k s' := by
  rw [runLane, hp]
  change (p[s.pc t]?).bind (fun ins => (execute ops l g t ins s).bind
    (fun next => runLane ops l g p t k next)) = _
  rw [hi, Option.some_bind, he, Option.some_bind]

theorem lane_eq (ops : Ops α) (e : Scalar) (n w t : Nat) (s : State α) (x : α)
    (hv : Valid e) (ht : t < n) (hb : t < 2147483648)
    (hp : s.pc t = 0) (hx : s.memory (inputCell t) = some x) :
    runLane ops (layout n) (geometry n w) (program e) t fuel.lane s =
      some (after ops e t x s) := by
  have hnonneg : (0 : Int) ≤ (t : Int) := by omega
  have hbound : (t : Int) < 2147483648 := by omega
  have hnotneg : ¬ (t : Int) < 0 := by omega
  have hrole : (Role.output == Role.input) = false := by decide
  simp only [inputCell] at hx
  have h1 : execute ops (layout n) (geometry n w) t (.index 0 .bid) s =
      some (indexed t s) := by
    simp [execute, evalIndex, geometry, int32, hnonneg, hbound, hp, advance, indexed]
  have hi : evalIndex (geometry n w) t (indexed t s) (.ivar 0) = some (t : Int) := by
    simp [evalIndex, indexed, advance]
  have hloc : location (layout n) (geometry n w) t .global 0 (t : Int) false =
      some (inputCell t) := by simp [location, layout, hnotneg, ht, inputCell]
  have hread : evalExpr ops (layout n) (geometry n w) t
      (.un .fromHalf (.load .global 0 (.ivar 0))) (indexed t s) =
      some (ops.fromHalf x, record (indexed t s) t (inputCell t) false) := by
    simp only [evalExpr, hi, bind, pure, Option.bind, hloc]
    simp [indexed, advance, hx, inputCell, applyUnary]
  have h2 : execute ops (layout n) (geometry n w) t
      (.assign 0 (.un .fromHalf (.load .global 0 (.ivar 0)))) (indexed t s) =
      some (loaded ops t x s) := by
    simp only [execute, hread, bind, pure, Option.bind]
    simp [loaded, indexed, advance, record]
  have h3 : execute ops (layout n) (geometry n w) t
      (.store .global 1 (.ivar 0) (.un .toHalf (lower e))) (loaded ops t x s) =
      some (after ops e t x s) := by
    have hl := eval_lower ops (layout n) (geometry n w) t
      (loaded ops t x s) (ops.fromHalf x) e hv (by simp [loaded, advance])
    have hix : evalIndex (geometry n w) t (loaded ops t x s) (.ivar 0) =
        some (t : Int) := by simp [evalIndex, loaded, indexed, advance, record]
    have hlo : location (layout n) (geometry n w) t .global 1 (t : Int) true =
        some (outputCell t) := by
      simp [location, layout, hnotneg, ht, hrole, outputCell]
    simp only [execute, hix, bind, pure, Option.bind, hlo, evalExpr, hl]
    simp [after, loaded, indexed, advance, record, result, applyUnary]
  change runLane ops (layout n) (geometry n w) (program e) t (3 + 1) s = _
  rw [lane_step ops _ _ _ _ _ _ _ _ (by simp [parked, program, hp])
    (by simp [program, hp]) h1]
  rw [lane_step ops _ _ _ _ _ _ _ _ (by simp [parked, program, indexed, advance])
    (by simp [program, indexed, advance]) h2]
  rw [lane_step ops _ _ _ _ _ _ _ _ (by simp [parked, program, loaded, advance])
    (by simp [program, loaded, advance]) h3]
  simp [runLane, parked, program, after, advance]

def partialState (ops : Ops α) (e : Scalar) (n : Nat) (input : Nat → Nat → α)
    (outside : Location → Option α) : Nat → State α
  | 0 => initial (layout n) input outside
  | k + 1 => after ops e k (input 0 k) (partialState ops e n input outside k)

theorem partialState_pc (ops : Ops α) (e : Scalar) (n : Nat) (input : Nat → Nat → α)
    (outside : Location → Option α) (k t : Nat) :
    (partialState ops e n input outside k).pc t = if t < k then 3 else 0 := by
  induction k with
  | zero => simp [partialState, initial]
  | succ k ih =>
      simp only [partialState, after, loaded, indexed, advance, record, ih]
      by_cases h : t = k
      · simp [h]
      · by_cases h' : t < k
        · have hh : t < k+1 := by omega
          simp [h, h', hh]
        · have hh : ¬ t < k+1 := by omega
          simp [h, h', hh]

theorem partialState_input (ops : Ops α) (e : Scalar) (n : Nat) (input : Nat → Nat → α)
    (outside : Location → Option α) (k t : Nat) (ht : t < n) :
    (partialState ops e n input outside k).memory (inputCell t) = some (input 0 t) := by
  induction k with
  | zero => simp [partialState, initial, layout, inputCell, ht]
  | succ k ih => simpa [partialState, after, advance, record, loaded, indexed, inputCell, outputCell] using ih

theorem partialState_output (ops : Ops α) (e : Scalar) (n : Nat) (input : Nat → Nat → α)
    (outside : Location → Option α) (k t : Nat) (ht : t < k) :
    (partialState ops e n input outside k).memory (outputCell t) =
      some (result ops e (input 0 t)) := by
  induction k with
  | zero => omega
  | succ k ih =>
      simp only [partialState, after, advance, outputCell, Location.mk.injEq, and_self_left, true_and]
      by_cases h : t = k
      · simp [h]
      · simpa [h, outputCell] using ih (by omega)

theorem block_eq (ops : Ops α) (e : Scalar) (n w t : Nat)
    (input : Nat → Nat → α) (outside : Location → Option α)
    (hv : Valid e) (ht : t < n) (hn : n ≤ 2147483648) (hw : 0 < w) :
    runBlock ops (layout n) (geometry n w) fuel (program e) t fuel.block
      (partialState ops e n input outside t) =
      some (partialState ops e n input outside (t + 1)) := by
  have hl := lane_eq ops e n w t (partialState ops e n input outside t)
    (input 0 t) hv ht (by omega)
    (by simp [partialState_pc]) (partialState_input ops e n input outside t t ht)
  change runLane ops (layout n) (geometry n w) (program e) t fuel.lane
    (partialState ops e n input outside t) =
    some (partialState ops e n input outside (t+1)) at hl
  have hd : (1 + w - 1) / w = 1 := by
    have he : 1 + w - 1 = w := by omega
    rw [he, Nat.div_self (by omega)]
  have hwne : w ≠ 0 := by omega
  have hwarp : warpThreads (geometry n w) t 0 = [t] := by
    simp [warpThreads, geometry, List.range_succ, hwne]
  have hblock : blockThreads (geometry n w) t = [t] := by
    simp [blockThreads, geometry, List.range_succ]
  have hc : converged (program e) [t] (partialState ops e n input outside (t+1)) =
      some .halt := by simp [converged, partialState_pc, parked, program]
  have hr : runWarp ops (layout n) (geometry n w) fuel (program e) [t] fuel.warp
      (partialState ops e n input outside t) =
      some (partialState ops e n input outside (t+1)) := by
    change runWarp ops (layout n) (geometry n w) fuel (program e) [t] 1 _ = _
    rw [runWarp]
    simp only [List.foldlM_cons, List.foldlM_nil, bind, pure, Option.bind, hl, hc]
    rfl
  have hws : List.range (((geometry n w).block + (geometry n w).warp - 1) /
      (geometry n w).warp) = [0] := by
    simp [geometry, hd, List.range_succ]
  change runBlock ops (layout n) (geometry n w) fuel (program e) t 1 _ = _
  rw [runBlock, hws]
  simp only [List.foldlM_cons, List.foldlM_nil, hwarp, hr, bind, pure, Option.bind,
    hblock, hc]
  rfl

theorem blocks_eq (ops : Ops α) (e : Scalar) (n w k : Nat)
    (input : Nat → Nat → α) (outside : Location → Option α)
    (hv : Valid e) (hk : k ≤ n) (hn : n ≤ 2147483648) (hw : 0 < w) :
    (List.range k).foldlM (fun s b =>
      runBlock ops (layout n) (geometry n w) fuel (program e) b fuel.block s)
      (initial (layout n) input outside) = some (partialState ops e n input outside k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [List.range_succ, List.foldlM_append, ih (by omega)]
      simp [block_eq ops e n w k input outside hv (by omega) hn hw]

def Owned (trace : List Access) : Prop :=
  ∀ a ∈ trace, a.location = if a.write then outputCell a.thread else inputCell a.thread

theorem partialState_owned (ops : Ops α) (e : Scalar) (n : Nat)
    (input : Nat → Nat → α) (outside : Location → Option α) (k : Nat) :
    Owned (partialState ops e n input outside k).trace := by
  induction k with
  | zero => simp [Owned, partialState, initial]
  | succ k ih =>
      intro a ha
      simp only [partialState, after, loaded, indexed, record, advance, List.mem_cons] at ha
      rcases ha with rfl | rfl | ha
      · rfl
      · rfl
      · exact ih a ha

theorem owned_raceFree (g : Geometry) (trace : List Access) (h : Owned trace) :
    raceFree g trace = true := by
  apply List.all_eq_true.mpr
  intro a ha
  apply List.all_eq_true.mpr
  intro b hb
  have ha' := h a ha
  have hb' := h b hb
  by_cases he : a.thread = b.thread
  · simp [conflict, he]
  · cases haw : a.write <;> cases hbw : b.write <;>
      simp [haw, hbw] at ha' hb' <;>
      simp [conflict, sameLocation, ha', hb', haw, hbw, outputCell, inputCell, he,
        show (a.thread == b.thread) = false by simp [he]]

theorem mapM_some (xs : List Nat) (f : Nat → Option α) (g : Nat → α)
    (h : ∀ i ∈ xs, f i = some (g i)) : xs.mapM f = some (xs.map g) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      simp only [List.mapM_cons, h a (by simp), Option.some_bind,
        ih (by intro i hi; exact h i (by simp [hi])), List.map_cons]
      rfl

theorem mapM_map (f : ι → κ) (g : κ → Option α) (xs : List ι) :
    (xs.map f).mapM g = xs.mapM (fun x => g (f x)) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [List.mapM_cons, ih, bind, pure, Option.bind]

def spec (ops : Ops α) (e : Scalar) (n : Nat) (input : Nat → Nat → α) : List α :=
  (List.range n).map (fun i => result ops e (input 0 i))

theorem partialState_extract (ops : Ops α) (e : Scalar) (n : Nat)
    (input : Nat → Nat → α) (outside : Location → Option α) :
    extract (layout n) (partialState ops e n input outside n) = some (spec ops e n input) := by
  simp only [extract, layout, List.zipIdx_cons, List.zipIdx_nil, List.flatMap_cons,
    List.flatMap_nil, List.nil_append]
  simp only [List.map_cons, List.map_nil, show Role.input ≠ Role.output by decide,
    ↓reduceIte, List.nil_append, List.append_nil]
  change (((List.range n).map (fun i => (1, i))).mapM
    (fun bi => (partialState ops e n input outside n).memory
      ⟨.global, 0, bi.1, bi.2⟩) : Option (List α)) = _
  rw [mapM_map]
  exact mapM_some (List.range n) _ _ (by
    intro i hi
    exact partialState_output ops e n input outside n i (List.mem_range.mp hi))

theorem converged_done (e : Scalar) (s : State α) (ts : List Nat)
    (hne : ts ≠ []) (hp : ∀ t ∈ ts, s.pc t = 3) :
    converged (program e) ts s = some .halt := by
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

theorem launch_eq (ops : Ops α) (e : Scalar) (n w : Nat)
    (input : Nat → Nat → α) (outside : Location → Option α)
    (hv : Valid e) (hn : 0 < n) (hb : n ≤ 2147483648) (hw : 0 < w) :
    runLaunch ops (layout n) (geometry n w) fuel (program e)
      (initial (layout n) input outside) = some (partialState ops e n input outside n) := by
  have hfold := blocks_eq ops e n w n input outside hv (by omega) hb hw
  have hne : List.range n ≠ [] := by
    intro he
    have hh := congrArg List.length he
    simp at hh
    omega
  have hc := converged_done e (partialState ops e n input outside n) (List.range n) hne
    (by intro t ht; simp [partialState_pc, List.mem_range.mp ht])
  simp only [runLaunch, geometry, show n ≠ 0 by omega, show w ≠ 0 by omega,
    or_false, false_or, reduceCtorEq, ↓reduceIte, fuel, runGrid]
  change ((List.range n).foldlM (fun s b =>
    runBlock ops (layout n) (geometry n w) fuel (program e) b fuel.block s)
      (initial (layout n) input outside)).bind _ = _
  rw [hfold]
  simp only [bind, pure, Option.bind]
  simp only [Nat.mul_one, hc]
  rfl

/-- Full machine completion, race freedom, and all output cells, by induction. -/
theorem correct (ops : Ops α) (e : Scalar) (n w : Nat)
    (hv : Valid e) (hn : 0 < n) (hb : n ≤ 2147483648) (hw : 0 < w) :
    Correct ops (layout n) (geometry n w) fuel (program e) (spec ops e n) := by
  intro input outside
  refine ⟨partialState ops e n input outside n,
    launch_eq ops e n w input outside hv hn hb hw, ?_,
    partialState_extract ops e n input outside⟩
  exact owned_raceFree (geometry n w) _ (partialState_owned ops e n input outside n)

#print axioms correct

end LarkPointwise
