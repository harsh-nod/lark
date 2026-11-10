import Lark.Collective

/-! A reusable three-phase proof for single-wave register-transport kernels. -/
namespace LarkCollective.Transfer
open LarkNonlinear
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def layout : Layout := ⟨[⟨.input, 64⟩, ⟨.output, 64⟩], [], []⟩
def geometry : Geometry := ⟨1, 64, 64⟩
def fuel : Fuel := ⟨32, 8, 8, 8⟩
def program (kind : ShuffleKind) (dest : Nat) (selector : Index) (width : Nat) : List Instr :=
  [.scalar (.index 0 .tid),
   .scalar (.assign 0 (.load .global 0 (.ivar 0))),
   .shuffle kind dest 0 selector width,
   .scalar (.store .global 1 (.ivar 0) (.reg dest)), .scalar .halt]
def inputCell (t : Nat) : Location := ⟨.global, 0, 0, t⟩
def outputCell (t : Nat) : Location := ⟨.global, 0, 1, t⟩

def indexed (t : Nat) (s : State α) : State α :=
  advance { s with indices := fun u r =>
    if u = t ∧ r = 0 then some (Int.ofNat t) else s.indices u r } t 1

def loaded (t : Nat) (value : α) (s : State α) : State α :=
  advance { record (indexed t s) t (inputCell t) false with
    regs := fun u r => if u = t ∧ r = 0 then some value else s.regs u r } t 2

def loadPartial (input : Nat → Nat → α) (outside : Location → Option α) : Nat → State α
  | 0 => initial layout input outside
  | k + 1 => loaded k (input 0 k) (loadPartial input outside k)

theorem load_pc (input : Nat → Nat → α) (outside : Location → Option α) (k t : Nat) :
    (loadPartial input outside k).pc t = if t < k then 2 else 0 := by
  induction k with
  | zero => simp [loadPartial, initial]
  | succ k ih =>
      simp only [loadPartial, loaded, indexed, advance, record, ih]
      by_cases he : t = k
      · simp [he]
      · by_cases ht : t < k
        · have hh : t < k+1 := by omega
          simp [he, ht, hh]
        · have hh : ¬ t < k+1 := by omega
          simp [he, ht, hh]

theorem load_indices (input : Nat → Nat → α) (outside : Location → Option α)
    (k t r : Nat) :
    (loadPartial input outside k).indices t r =
      if t < k ∧ r = 0 then some (Int.ofNat t) else none := by
  induction k with
  | zero => simp [loadPartial, initial]
  | succ k ih =>
      simp only [loadPartial, loaded, indexed, advance, record, ih]
      by_cases he : t = k
      · simp [he]
      · by_cases ht : t < k
        · have hh : t < k+1 := by omega
          simp [he, ht, hh]
        · have hh : ¬ t < k+1 := by omega
          simp [he, ht, hh]

theorem load_regs (input : Nat → Nat → α) (outside : Location → Option α)
    (k t r : Nat) :
    (loadPartial input outside k).regs t r =
      if t < k ∧ r = 0 then some (input 0 t) else none := by
  induction k with
  | zero => simp [loadPartial, initial]
  | succ k ih =>
      simp only [loadPartial, loaded, indexed, advance, record, ih]
      by_cases he : t = k
      · simp [he]
      · by_cases ht : t < k
        · have hh : t < k+1 := by omega
          simp [he, ht, hh]
        · have hh : ¬ t < k+1 := by omega
          simp [he, ht, hh]

theorem load_memory (input : Nat → Nat → α) (outside : Location → Option α) (k : Nat) :
    (loadPartial input outside k).memory = (initial layout input outside).memory := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [loadPartial, loaded, indexed, advance, record] using ih

theorem load_owned (input : Nat → Nat → α) (outside : Location → Option α) (k : Nat) :
    Owned (loadPartial input outside k).trace := by
  induction k with
  | zero => simp [Owned, loadPartial, initial]
  | succ k ih =>
      intro a ha
      simp only [loadPartial, loaded, indexed, advance, record, List.mem_cons] at ha
      rcases ha with rfl | ha
      · rfl
      · exact ih a ha

theorem lane_step (ops : Ops α) (p : List Instr) (t k : Nat)
    (s next : State α) (instruction : LarkNonlinear.Instr)
    (hp : parked p s t = none) (hi : p[s.pc t]? = some (.scalar instruction))
    (he : execute ops layout geometry t instruction s = some next) :
    runLane ops layout geometry p t (k+1) s = runLane ops layout geometry p t k next := by
  rw [runLane, hp]
  simp only [hi, bind, pure, Option.bind, he]

theorem load_lane (ops : Ops α) (kind : ShuffleKind) (dest : Nat)
    (selector : Index) (width t : Nat) (s : State α) (value : α)
    (ht : t < 64) (hp : s.pc t = 0) (hx : s.memory (inputCell t) = some value) :
    runLane ops layout geometry (program kind dest selector width) t fuel.lane s =
      some (loaded t value s) := by
  have hn : (0 : Int) ≤ (t : Int) := by omega
  have hb : (t : Int) < 2147483648 := by omega
  have hnot : ¬ (t : Int) < 0 := by omega
  simp only [inputCell] at hx
  have h1 : execute ops layout geometry t (.index 0 .tid) s = some (indexed t s) := by
    simp [execute, evalIndex, geometry, Nat.mod_eq_of_lt ht, int32, hn, hb, hp, indexed, advance]
  have hix : evalIndex geometry t (indexed t s) (.ivar 0) = some (t : Int) := by
    simp [evalIndex, indexed, advance]
  have hloc : location layout geometry t .global 0 (t : Int) false = some (inputCell t) := by
    simp [location, layout, inputCell, hnot, ht]
  have h2 : execute ops layout geometry t (.assign 0 (.load .global 0 (.ivar 0))) (indexed t s) =
      some (loaded t value s) := by
    simp only [execute, evalExpr, hix, bind, pure, Option.bind, hloc]
    simp [loaded, indexed, advance, record, hx, inputCell]
  change runLane ops layout geometry (program kind dest selector width) t (31+1) s = _
  rw [lane_step ops _ _ _ _ _ _ (by simp [parked, program, hp])
    (by simp [program, hp]) h1]
  rw [lane_step ops _ _ _ _ _ _ (by simp [parked, program, indexed, advance])
    (by simp [program, indexed, advance]) h2]
  simp [runLane, parked, program, loaded, advance]

theorem load_fold (ops : Ops α) (kind : ShuffleKind) (dest : Nat)
    (selector : Index) (width : Nat) (input : Nat → Nat → α)
    (outside : Location → Option α) (k : Nat) (hk : k ≤ 64) :
    (List.range k).foldlM (fun s t => runLane ops layout geometry
      (program kind dest selector width) t fuel.lane s) (initial layout input outside) =
      some (loadPartial input outside k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [List.range_succ, List.foldlM_append, ih (by omega)]
      simp only [List.foldlM_cons, List.foldlM_nil, bind, pure, Option.bind]
      have hx : (loadPartial input outside k).memory (inputCell k) = some (input 0 k) := by
        rw [load_memory]
        simp [initial, layout, inputCell, show k < 64 by omega]
      rw [load_lane ops kind dest selector width k _ _ (by omega)
        (by simp [load_pc]) hx]
      rfl

def indexState (t : Nat) : State Unit where
  pc := fun _ => 0
  indices := fun _ r => if r = 0 then some (Int.ofNat t) else none
  regs := fun _ _ => none
  memory := fun _ => none
  epochs := fun _ => {}
  trace := []

def selection (kind : ShuffleKind) (selector : Index) (width t : Nat) : Option Nat := do
  let argument ← evalIndex geometry t (indexState t) selector
  if argument < 0 then none else sourceLane kind width t argument.toNat

def Valid (kind : ShuffleKind) (selector : Index) (width : Nat) (chosen : Nat → Nat) : Prop :=
  ∀ t : Fin 64, selection kind selector width t = some (chosen t) ∧ chosen t < 64

theorem evalIndex_congr (g : Geometry) (t : Nat) (s : State α) (other : State β)
    (index : Index) (h : s.indices t = other.indices t) :
    evalIndex g t s index = evalIndex g t other index := by
  induction index <;> simp [evalIndex, h, *]

theorem loaded_eval (input : Nat → Nat → α) (outside : Location → Option α)
    (t : Nat) (ht : t < 64) (selector : Index) :
    evalIndex geometry t (loadPartial input outside 64) selector =
    evalIndex geometry t (indexState t) selector := by
  apply evalIndex_congr
  funext r
  simp [load_indices, indexState, ht]

theorem mapM_some (xs : List Nat) (f : Nat → Option α) (value : Nat → α)
    (h : ∀ t ∈ xs, f t = some (value t)) :
    xs.mapM f = some (xs.map value) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      simp only [List.mapM_cons, h a (by simp), Option.some_bind,
        ih (by intro t ht; exact h t (by simp [ht])), List.map_cons]
      rfl

theorem shuffle_values (kind : ShuffleKind) (dest : Nat) (selector : Index)
    (width : Nat) (chosen : Nat → Nat) (hv : Valid kind selector width chosen)
    (input : Nat → Nat → α) (outside : Location → Option α) :
    shuffleValues geometry (program kind dest selector width) (List.range 64)
      (loadPartial input outside 64) =
      some (dest, (List.range 64).map (fun t => (t, input 0 (chosen t)))) := by
  unfold shuffleValues
  rw [if_neg (by decide)]
  have hhead : (List.range 64).head? = some 0 := by decide
  rw [hhead]
  have hpc : (loadPartial input outside 64).pc 0 = 2 := by simp [load_pc]
  simp only [bind, pure, Option.bind, hpc, program,
    List.getElem?_cons_zero, List.getElem?_cons_succ]
  have hm := mapM_some (List.range 64)
    (fun t => do
      let arg ← evalIndex geometry t (loadPartial input outside 64) selector
      if arg < 0 then none else do
        let lane := (t % geometry.block) % 64
        let selected ← sourceLane kind width lane arg.toNat
        let owner := (t / geometry.block) * geometry.block + ((t % geometry.block) / 64) * 64
        let source := owner + selected
        if !((List.range 64).contains source) then none else do
          let value ← (loadPartial input outside 64).regs source 0
          pure (t, value))
    (fun t => (t, input 0 (chosen t))) (by
      intro t hmem
      have ht : t < 64 := List.mem_range.mp hmem
      have hc := hv ⟨t, ht⟩
      change selection kind selector width t = some (chosen t) ∧ chosen t < 64 at hc
      have heval := loaded_eval input outside t ht selector
      dsimp only
      unfold selection at hc
      cases ha : evalIndex geometry t (indexState t) selector with
      | none => simp [ha] at hc
      | some argument =>
          by_cases hn : argument < 0
          · simp [ha, hn] at hc
          · simp only [ha, bind, pure, Option.bind, hn, ↓reduceIte] at hc
            rw [heval, ha]
            simp only [bind, pure, Option.bind, hn, ↓reduceIte, geometry,
              Nat.mod_eq_of_lt ht, Nat.div_eq_of_lt ht, Nat.zero_mul, Nat.zero_add]
            rw [hc.1]
            simp [load_regs, hc.2, List.contains_iff_mem, List.mem_range])
  have heq := congrArg (fun values : Option (List (Nat × α)) =>
    values.bind (fun vs => some (dest, vs))) hm
  simpa only [bind, pure, Option.bind] using heq

def shuffled (dest : Nat) (chosen : Nat → Nat) (input : Nat → Nat → α)
    (outside : Location → Option α) : State α :=
  shuffleUpdates dest ((List.range 64).map (fun t => (t, input 0 (chosen t))))
    (loadPartial input outside 64)

theorem shuffle_eq (kind : ShuffleKind) (dest : Nat) (selector : Index)
    (width : Nat) (chosen : Nat → Nat) (hv : Valid kind selector width chosen)
    (input : Nat → Nat → α) (outside : Location → Option α) :
    runShuffle geometry (program kind dest selector width) (List.range 64)
      (loadPartial input outside 64) = some (shuffled dest chosen input outside) := by
  simp only [runShuffle, shuffle_values kind dest selector width chosen hv,
    bind, pure, Option.bind, shuffled]

theorem lookup_map (xs : List Nat) (value : Nat → α) (t : Nat) (ht : t ∈ xs) :
    List.lookup t (xs.map (fun u => (u, value u))) = some (value t) := by
  induction xs with
  | nil => simp at ht
  | cons a xs ih =>
      by_cases he : t = a
      · subst t; simp
      · have hm : t ∈ xs := by simpa [he] using ht
        have hb : (t == a) = false := by simp [he]
        simpa only [List.map_cons, List.lookup_cons, hb] using ih hm

theorem any_map_range (n t : Nat) (value : Nat → α) :
    ((List.range n).map (fun u => (u, value u))).any (fun pair => pair.1 == t) =
      decide (t < n) := by
  apply Bool.eq_iff_iff.mpr
  simp [List.any_eq_true]

theorem shuffled_pc (dest : Nat) (chosen : Nat → Nat) (input : Nat → Nat → α)
    (outside : Location → Option α) (t : Nat) :
    (shuffled dest chosen input outside).pc t = if t < 64 then 3 else 0 := by
  by_cases ht : t < 64 <;>
    simp [shuffled, shuffleUpdates, any_map_range, load_pc, ht]

theorem shuffled_indices (dest : Nat) (chosen : Nat → Nat) (input : Nat → Nat → α)
    (outside : Location → Option α) (t : Nat) (ht : t < 64) :
    (shuffled dest chosen input outside).indices t 0 = some (t : Int) := by
  simp [shuffled, shuffleUpdates, load_indices, ht]

theorem shuffled_regs (dest : Nat) (chosen : Nat → Nat) (input : Nat → Nat → α)
    (outside : Location → Option α) (t : Nat) (ht : t < 64) :
    (shuffled dest chosen input outside).regs t dest = some (input 0 (chosen t)) := by
  simp only [shuffled, shuffleUpdates, ↓reduceIte]
  rw [lookup_map _ _ t (List.mem_range.mpr ht)]

def stored (t : Nat) (value : α) (s : State α) : State α :=
  advance { record s t (outputCell t) true with
    memory := fun l => if l = outputCell t then some value else s.memory l } t 4

def storePartial (dest : Nat) (chosen : Nat → Nat) (input : Nat → Nat → α)
    (outside : Location → Option α) : Nat → State α
  | 0 => shuffled dest chosen input outside
  | k+1 => stored k (input 0 (chosen k)) (storePartial dest chosen input outside k)

theorem store_pc (dest : Nat) (chosen : Nat → Nat) (input : Nat → Nat → α)
    (outside : Location → Option α) (k t : Nat) :
    (storePartial dest chosen input outside k).pc t =
      if t < k then 4 else if t < 64 then 3 else 0 := by
  induction k with
  | zero => simp [storePartial, shuffled_pc]
  | succ k ih =>
      simp only [storePartial, stored, advance, record, ih]
      by_cases he : t = k
      · simp [he]
      · by_cases ht : t < k
        · have hh : t < k+1 := by omega
          simp [he, ht, hh]
        · have hh : ¬ t < k+1 := by omega
          simp [he, ht, hh]

theorem store_indices (dest : Nat) (chosen : Nat → Nat) (input : Nat → Nat → α)
    (outside : Location → Option α) (k t : Nat) (ht : t < 64) :
    (storePartial dest chosen input outside k).indices t 0 = some (t : Int) := by
  induction k with
  | zero => exact shuffled_indices dest chosen input outside t ht
  | succ k ih => simpa only [storePartial, stored, advance, record] using ih

theorem store_regs (dest : Nat) (chosen : Nat → Nat) (input : Nat → Nat → α)
    (outside : Location → Option α) (k t : Nat) (ht : t < 64) :
    (storePartial dest chosen input outside k).regs t dest = some (input 0 (chosen t)) := by
  induction k with
  | zero => exact shuffled_regs dest chosen input outside t ht
  | succ k ih => simpa only [storePartial, stored, advance, record] using ih

theorem store_output (dest : Nat) (chosen : Nat → Nat) (input : Nat → Nat → α)
    (outside : Location → Option α) (k t : Nat) (ht : t < k) :
    (storePartial dest chosen input outside k).memory (outputCell t) = some (input 0 (chosen t)) := by
  induction k with
  | zero => omega
  | succ k ih =>
      simp only [storePartial, stored, advance, record]
      by_cases he : t = k
      · simp [he]
      · have hn : outputCell t ≠ outputCell k := by
          intro hh
          have hh' := congrArg Location.offset hh
          exact he hh'
        rw [if_neg hn]
        exact ih (by omega)

theorem store_owned (dest : Nat) (chosen : Nat → Nat) (input : Nat → Nat → α)
    (outside : Location → Option α) (k : Nat) :
    Owned (storePartial dest chosen input outside k).trace := by
  induction k with
  | zero => exact load_owned input outside 64
  | succ k ih =>
      intro a ha
      simp only [storePartial, stored, advance, record, List.mem_cons] at ha
      rcases ha with rfl | ha
      · rfl
      · exact ih a ha

theorem store_lane (ops : Ops α) (kind : ShuffleKind) (dest : Nat)
    (selector : Index) (width t : Nat) (s : State α) (value : α)
    (ht : t < 64) (hp : s.pc t = 3) (hix : s.indices t 0 = some (t : Int))
    (hreg : s.regs t dest = some value) :
    runLane ops layout geometry (program kind dest selector width) t fuel.lane s =
      some (stored t value s) := by
  have hnot : ¬ (t : Int) < 0 := by omega
  have hrole : (Role.output == Role.input) = false := by decide
  have hloc : location layout geometry t .global 1 (t : Int) true = some (outputCell t) := by
    simp [location, layout, outputCell, hnot, ht, hrole]
  have he : execute ops layout geometry t (.store .global 1 (.ivar 0) (.reg dest)) s =
      some (stored t value s) := by
    simp only [execute, evalIndex, hix, bind, pure, Option.bind, hloc, evalExpr, hreg]
    simp [stored, advance, record, hp]
  change runLane ops layout geometry (program kind dest selector width) t (31+1) s = _
  rw [lane_step ops _ _ _ _ _ _ (by simp [parked, program, hp])
    (by simp [program, hp]) he]
  simp [runLane, parked, program, stored, advance]

theorem store_fold (ops : Ops α) (kind : ShuffleKind) (dest : Nat)
    (selector : Index) (width : Nat) (chosen : Nat → Nat)
    (input : Nat → Nat → α) (outside : Location → Option α) (k : Nat) (hk : k ≤ 64) :
    (List.range k).foldlM (fun s t => runLane ops layout geometry
      (program kind dest selector width) t fuel.lane s) (shuffled dest chosen input outside) =
      some (storePartial dest chosen input outside k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [List.range_succ, List.foldlM_append, ih (by omega)]
      simp only [List.foldlM_cons, List.foldlM_nil, bind, pure, Option.bind]
      rw [store_lane ops kind dest selector width k _ _ (by omega)
        (by simp [store_pc, show k < 64 by omega])
        (store_indices dest chosen input outside k k (by omega))
        (store_regs dest chosen input outside k k (by omega))]
      rfl

theorem converged_load (kind : ShuffleKind) (dest : Nat) (selector : Index)
    (width : Nat) (input : Nat → Nat → α) (outside : Location → Option α) :
    converged (program kind dest selector width) (List.range 64) (loadPartial input outside 64) =
      some .shuffle := by
  have hhead : (List.range 64).head? = some 0 := by decide
  have ha : (List.range 64).all (fun t => (loadPartial input outside 64).pc t ==
      (loadPartial input outside 64).pc 0) = true := by
    apply List.all_eq_true.mpr
    intro t ht
    simp [load_pc, List.mem_range.mp ht]
  simp only [converged, hhead, bind, pure, Option.bind, ha, ↓reduceIte]
  simp [parked, load_pc, program]

theorem converged_store (kind : ShuffleKind) (dest : Nat) (selector : Index)
    (width : Nat) (chosen : Nat → Nat) (input : Nat → Nat → α)
    (outside : Location → Option α) :
    converged (program kind dest selector width) (List.range 64)
      (storePartial dest chosen input outside 64) = some .halt := by
  have hhead : (List.range 64).head? = some 0 := by decide
  have ha : (List.range 64).all (fun t => (storePartial dest chosen input outside 64).pc t ==
      (storePartial dest chosen input outside 64).pc 0) = true := by
    apply List.all_eq_true.mpr
    intro t ht
    simp [store_pc, List.mem_range.mp ht]
  simp only [converged, hhead, bind, pure, Option.bind, ha, ↓reduceIte]
  simp [parked, store_pc, program]

theorem warp_eq (ops : Ops α) (kind : ShuffleKind) (dest : Nat)
    (selector : Index) (width : Nat) (chosen : Nat → Nat)
    (hv : Valid kind selector width chosen)
    (input : Nat → Nat → α) (outside : Location → Option α) :
    runWarp ops layout geometry fuel (program kind dest selector width) (List.range 64)
      fuel.warp (initial layout input outside) =
      some (storePartial dest chosen input outside 64) := by
  change runWarp ops layout geometry fuel (program kind dest selector width) (List.range 64)
    (7+1) _ = _
  rw [runWarp, load_fold ops kind dest selector width input outside 64 (by omega)]
  simp only [bind, pure, Option.bind, converged_load, ↓reduceIte]
  rw [shuffle_eq kind dest selector width chosen hv input outside]
  simp only [bind, pure, Option.bind]
  rw [runWarp, store_fold ops kind dest selector width chosen input outside 64 (by omega)]
  simp only [bind, pure, Option.bind, converged_store, reduceCtorEq, ↓reduceIte]

theorem block_eq (ops : Ops α) (kind : ShuffleKind) (dest : Nat)
    (selector : Index) (width : Nat) (chosen : Nat → Nat)
    (hv : Valid kind selector width chosen)
    (input : Nat → Nat → α) (outside : Location → Option α) :
    runBlock ops layout geometry fuel (program kind dest selector width) 0 fuel.block
      (initial layout input outside) = some (storePartial dest chosen input outside 64) := by
  have hws : List.range ((geometry.block + geometry.warp - 1) / geometry.warp) = [0] := by decide
  have hwarp : warpThreads geometry 0 0 = List.range 64 := by decide
  have hblock : blockThreads geometry 0 = List.range 64 := by decide
  have hw := warp_eq ops kind dest selector width chosen hv input outside
  change runBlock ops layout geometry fuel (program kind dest selector width) 0 (7+1) _ = _
  rw [runBlock, hws]
  simp only [List.foldlM_cons, List.foldlM_nil, hwarp, hw, bind, pure, Option.bind,
    hblock, converged_store, reduceCtorEq, or_true, ↓reduceIte]

theorem launch_eq (ops : Ops α) (kind : ShuffleKind) (dest : Nat)
    (selector : Index) (width : Nat) (chosen : Nat → Nat)
    (hv : Valid kind selector width chosen)
    (input : Nat → Nat → α) (outside : Location → Option α) :
    runLaunch ops layout geometry fuel (program kind dest selector width)
      (initial layout input outside) = some (storePartial dest chosen input outside 64) := by
  have hblocks : List.range geometry.grid = [0] := by decide
  have hthreads : List.range (geometry.grid * geometry.block) = List.range 64 := by decide
  rw [runLaunch, if_neg (by decide)]
  change runGrid ops layout geometry fuel (program kind dest selector width) (7+1) _ = _
  rw [runGrid, hblocks]
  simp only [List.foldlM_cons, List.foldlM_nil, block_eq ops kind dest selector width chosen hv,
    bind, pure, Option.bind, hthreads, converged_store, reduceCtorEq, ↓reduceIte]

theorem mapM_map (f : ι → κ) (g : κ → Option α) (xs : List ι) :
    (xs.map f).mapM g = xs.mapM (fun x => g (f x)) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [List.mapM_cons, ih, bind, pure, Option.bind]

def spec (chosen : Nat → Nat) (input : Nat → Nat → α) : List α :=
  (List.range 64).map (fun t => input 0 (chosen t))

theorem final_extract (dest : Nat) (chosen : Nat → Nat) (input : Nat → Nat → α)
    (outside : Location → Option α) :
    extract layout (storePartial dest chosen input outside 64) = some (spec chosen input) := by
  simp only [extract, layout, List.zipIdx_cons, List.zipIdx_nil, List.flatMap_cons,
    List.flatMap_nil, List.nil_append]
  simp only [List.map_cons, List.map_nil, show Role.input ≠ Role.output by decide,
    ↓reduceIte, List.nil_append, List.append_nil]
  change (((List.range 64).map (fun i => (1, i))).mapM
    (fun bi => (storePartial dest chosen input outside 64).memory
      ⟨.global, 0, bi.1, bi.2⟩) : Option (List α)) = _
  rw [mapM_map]
  exact mapM_some (List.range 64) _ _ (by
    intro t ht
    exact store_output dest chosen input outside 64 t (List.mem_range.mp ht))

/-- Actual whole-launch completion, RF, and output equality for every input. -/
theorem correct (ops : Ops α) (kind : ShuffleKind) (dest : Nat)
    (selector : Index) (width : Nat) (chosen : Nat → Nat)
    (hv : Valid kind selector width chosen) :
    Correct ops layout geometry fuel (program kind dest selector width) (spec chosen) := by
  intro input outside
  exact ⟨storePartial dest chosen input outside 64,
    launch_eq ops kind dest selector width chosen hv input outside,
    owned_raceFree geometry _ (store_owned dest chosen input outside 64),
    final_extract dest chosen input outside⟩

#print axioms correct
end LarkCollective.Transfer
