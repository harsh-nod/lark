import Lark.MFMA

/-! Source-bound single-wave 16×16 half-input/float-output MFMA tile proof. -/
namespace LarkMFMA.Tile
open LarkNonlinear
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def layout : Layout := ⟨[⟨.input, 256⟩, ⟨.input, 256⟩, ⟨.input, 256⟩, ⟨.output, 256⟩], [], []⟩
def geometry : Geometry := ⟨1, 64, 64⟩
def fuel : Fuel := ⟨64, 8, 8, 8⟩
def cell (buffer offset : Nat) : Location := ⟨.global, 0, buffer, offset⟩
def aAddress (t e : Nat) : Nat := (t % 16) * 16 + (t / 16) * 4 + e
def bAddress (t e : Nat) : Nat := ((t / 16) * 4 + e) * 16 + t % 16
def address (t r : Nat) : Nat := if r < 4 then aAddress t (r % 4) else bAddress t (r % 4)
def aIndex (e : Nat) : Index :=
  .add (.add (.mul (.mod (.ivar 0) (.const 16)) (.const 16))
    (.mul (.div (.ivar 0) (.const 16)) (.const 4))) (.const (e : Int))
def bIndex (e : Nat) : Index :=
  .add (.mul (.add (.mul (.div (.ivar 0) (.const 16)) (.const 4))
    (.const (e : Int))) (.const 16)) (.mod (.ivar 0) (.const 16))
def index (r : Nat) : Index := if r < 4 then aIndex (r % 4) else bIndex (r % 4)
def loadInstruction (r : Nat) : Instr := .scalar (.assign r (.load .global (r / 4) (index r)))
def storeInstruction (e : Nat) : Instr := .scalar (.store .global 3 (bIndex e) (.reg (8 + e)))
def program : List Instr :=
  [.scalar (.index 0 .tid)] ++ (List.range 12).map loadInstruction ++
    [.mfma 8 0 4 8] ++ (List.range 4).map storeInstruction ++ [.scalar .halt]

theorem addresses_bound (t e : Nat) (ht : t < 64) (he : e < 4) :
    aAddress t e < 256 ∧ bAddress t e < 256 := by
  unfold aAddress bAddress
  omega

def owner (offset : Nat) : Nat := (offset / 64) * 16 + offset % 16
def element (offset : Nat) : Nat := offset / 16 % 4

theorem output_owner (t e : Nat) (ht : t < 64) (he : e < 4) :
    owner (bAddress t e) = t ∧ element (bAddress t e) = e := by
  unfold owner element bAddress
  omega

theorem output_inverse (offset : Nat) (h : offset < 256) :
    owner offset < 64 ∧ element offset < 4 ∧
    bAddress (owner offset) (element offset) = offset := by
  unfold owner element bAddress
  omega

theorem a_source (row k : Nat) (hr : row < 16) (hk : k < 16) :
    aLane row k < 64 ∧ aAddress (aLane row k) (k % 4) = row * 16 + k := by
  unfold aLane aAddress
  omega

theorem b_source (k col : Nat) (hk : k < 16) (hc : col < 16) :
    bLane k col < 64 ∧ bAddress (bLane k col) (k % 4) = k * 16 + col := by
  unfold bLane bAddress
  omega

theorem int32_nat (n : Nat) (h : n < 2147483648) :
    int32 (n : Int) = some (n : Int) := by
  simp [int32, show (0 : Int) ≤ (n : Int) by omega,
    show (n : Int) < 2147483648 by omega]

theorem eval_add (g : Geometry) (t : Nat) (s : State α) (a b : Index) (x y : Nat)
    (ha : evalIndex g t s a = some (x : Int))
    (hb : evalIndex g t s b = some (y : Int)) (h : x+y < 2147483648) :
    evalIndex g t s (.add a b) = some ((x+y : Nat) : Int) := by
  simp only [evalIndex, ha, hb, bind, pure, Option.bind]
  exact int32_nat (x+y) h

theorem eval_mul (g : Geometry) (t : Nat) (s : State α) (a b : Index) (x y : Nat)
    (ha : evalIndex g t s a = some (x : Int))
    (hb : evalIndex g t s b = some (y : Int)) (h : x*y < 2147483648) :
    evalIndex g t s (.mul a b) = some ((x*y : Nat) : Int) := by
  simp only [evalIndex, ha, hb, bind, pure, Option.bind]
  exact int32_nat (x*y) h

theorem eval_lane_parts (t : Nat) (s : State α) (hi : s.indices t 0 = some (t : Int)) :
    evalIndex geometry t s (.div (.ivar 0) (.const 16)) = some ((t/16 : Nat) : Int) ∧
    evalIndex geometry t s (.mod (.ivar 0) (.const 16)) = some ((t%16 : Nat) : Int) := by
  have hn : ¬ ((t : Int)<0) := by omega
  simp only [evalIndex, hi, int32_nat 16 (by decide), bind, pure, Option.bind,
    show ¬ ((16 : Int)=0 ∨ (t : Int)<0 ∨ (16 : Int)<0) by omega, ↓reduceIte]
  exact ⟨congrArg some (Int.ofNat_ediv t 16).symm,
    congrArg some (Int.ofNat_emod t 16).symm⟩

theorem address_eval (t e : Nat) (s : State α) (ht : t < 64) (he : e < 4)
    (hi : s.indices t 0 = some (t : Int)) :
    evalIndex geometry t s (aIndex e) = some ((aAddress t e : Nat) : Int) ∧
    evalIndex geometry t s (bIndex e) = some ((bAddress t e : Nat) : Int) := by
  have parts := eval_lane_parts t s hi
  have hc16 : evalIndex geometry t s (.const 16) = some (16 : Int) := int32_nat 16 (by decide)
  have hc4 : evalIndex geometry t s (.const 4) = some (4 : Int) := int32_nat 4 (by decide)
  have hm1 := eval_mul geometry t s _ _ (t%16) 16 parts.2
    hc16 (by omega)
  have hm2 := eval_mul geometry t s _ _ (t/16) 4 parts.1
    hc4 (by omega)
  have ha := eval_add geometry t s _ _ ((t%16)*16) ((t/16)*4) hm1 hm2 (by omega)
  have hc : evalIndex geometry t s (.const (e : Int)) = some (e : Int) :=
    int32_nat e (by omega)
  have hab := eval_add geometry t s _ _ ((t/16)*4) e hm2 hc (by omega)
  have hbm := eval_mul geometry t s _ _ ((t/16)*4+e) 16 hab
    hc16 (by omega)
  exact ⟨eval_add geometry t s _ _ _ e ha hc (by omega),
    eval_add geometry t s _ _ _ (t%16) hbm parts.2 (by omega)⟩

theorem program_load (r : Nat) (hr : r < 12) :
    program[1+r]? = some (loadInstruction r) := by
  simp [program, List.getElem?_append, hr, Nat.add_comm 1 r]

theorem program_matrix : program[13]? = some (.mfma 8 0 4 8) := by decide
theorem program_halt : program[18]? = some (.scalar .halt) := by decide

def Reads (input : Nat → Nat → α) (s : State α) : Prop :=
  ∀ b i, b < 3 → i < 256 → s.memory (cell b i) = some (input b i)

def indexed (t : Nat) (s : State α) : State α :=
  advance { s with indices := fun u r =>
    if u = t ∧ r = 0 then some (t : Int) else s.indices u r } t 1

def loadedReg (input : Nat → Nat → α) (t r : Nat) (s : State α) : State α :=
  advance { record s t (cell (r/4) (address t r)) false with
    regs := fun u q => if u = t ∧ q = r then some (input (r/4) (address t r)) else s.regs u q }
    t (r+2)

def loadPrefix (input : Nat → Nat → α) (t : Nat) (s : State α) : Nat → State α
  | 0 => indexed t s
  | n+1 => loadedReg input t n (loadPrefix input t s n)

theorem prefix_pc (input : Nat → Nat → α) (t u : Nat) (s : State α) (n : Nat) :
    (loadPrefix input t s n).pc u = if u = t then n+1 else s.pc u := by
  induction n with
  | zero => simp [loadPrefix, indexed, advance]
  | succ n ih =>
      by_cases he : u = t <;> simp [loadPrefix, loadedReg, advance, record, ih, he, Nat.add_assoc]

theorem prefix_memory (input : Nat → Nat → α) (t : Nat) (s : State α) (n : Nat) :
    (loadPrefix input t s n).memory = s.memory := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [loadPrefix, loadedReg, indexed, advance, record] using ih

theorem prefix_indices (input : Nat → Nat → α) (t : Nat) (s : State α) (n : Nat) :
    (loadPrefix input t s n).indices = (indexed t s).indices := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [loadPrefix, loadedReg, advance, record] using ih

theorem prefix_regs (input : Nat → Nat → α) (t u r : Nat) (s : State α) (n : Nat) :
    (loadPrefix input t s n).regs u r =
      if u = t ∧ r < n then some (input (r/4) (address t r)) else s.regs u r := by
  induction n with
  | zero => simp [loadPrefix, indexed, advance]
  | succ n ih =>
      simp only [loadPrefix, loadedReg, advance, record, ih]
      by_cases hu : u = t
      · subst u
        by_cases hr : r = n
        · simp [hr]
        · by_cases hn : r < n
          · have hnext : r < n+1 := by omega
            simp [hr, hn, hnext]
          · have hnext : ¬ r < n+1 := by omega
            simp [hr, hn, hnext]
      · simp [hu]

theorem lane_step (ops : Ops α) (t k : Nat) (s next : State α)
    (instruction : LarkNonlinear.Instr) (hp : parked program s t = none)
    (hi : program[s.pc t]? = some (.scalar instruction))
    (he : execute ops layout geometry t instruction s = some next) :
    runLane ops layout geometry program t (k+1) s =
      runLane ops layout geometry program t k next := by
  rw [runLane, hp]
  simp only [hi, bind, pure, Option.bind, he]

theorem load_step (ops : Ops α) (input : Nat → Nat → α) (t r : Nat) (s : State α)
    (ht : t < 64) (hr : r < 12) (hp : s.pc t = r+1)
    (hi : s.indices t 0 = some (t : Int)) (reads : Reads input s) :
    execute ops layout geometry t (.assign r (.load .global (r/4) (index r))) s =
      some (loadedReg input t r s) := by
  have he := address_eval t (r%4) s ht (Nat.mod_lt _ (by decide)) hi
  have hbound : address t r < 256 := by
    unfold address
    split
    · exact (addresses_bound t (r%4) ht (Nat.mod_lt _ (by decide))).1
    · exact (addresses_bound t (r%4) ht (Nat.mod_lt _ (by decide))).2
  have hindex : evalIndex geometry t s (index r) = some ((address t r : Nat) : Int) := by
    unfold index address
    split
    · exact he.1
    · exact he.2
  have hb : r/4 < 3 := by omega
  have hnonnegative : ¬ ((address t r : Nat) : Int) < 0 := by omega
  have hlocation : location layout geometry t .global (r/4) (address t r : Int) false =
      some (cell (r/4) (address t r)) := by
    have cases : r/4 = 0 ∨ r/4 = 1 ∨ r/4 = 2 := by omega
    rcases cases with h | h | h <;> simp [location, layout, cell, h, hnonnegative, hbound]
  simp only [execute, evalExpr, hindex, bind, pure, Option.bind, hlocation,
    reads (r/4) (address t r) hb hbound]
  simp [loadedReg, advance, record, hp, Nat.add_assoc]

def loaded (input : Nat → Nat → α) (t : Nat) (s : State α) : State α :=
  loadPrefix input t s 12

theorem load_lane (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α)
    (ht : t < 64) (hp : s.pc t = 0) (reads : Reads input s) :
    runLane ops layout geometry program t fuel.lane s = some (loaded input t s) := by
  have hindex : execute ops layout geometry t (.index 0 .tid) s = some (indexed t s) := by
    simp [execute, evalIndex, geometry, Nat.mod_eq_of_lt ht, int32_nat t (by omega),
      indexed, advance, hp]
  change runLane ops layout geometry program t (63+1) s = _
  rw [lane_step ops _ _ _ _ _ (by simp [parked, program, hp]) (by simp [program, hp]) hindex]
  change runLane ops layout geometry program t 63 (loadPrefix input t s 0) = _
  have step (r : Nat) (hr : r < 12) :
      runLane ops layout geometry program t (63-r) (loadPrefix input t s r) =
      runLane ops layout geometry program t (62-r) (loadPrefix input t s (r+1)) := by
    have pc : (loadPrefix input t s r).pc t = r+1 := by simp [prefix_pc]
    have fetch : program[(loadPrefix input t s r).pc t]? = some (loadInstruction r) := by
      simpa [pc, Nat.add_comm] using program_load r hr
    have parkedNone : parked program (loadPrefix input t s r) t = none := by
      simp [parked, fetch, loadInstruction]
    have exe := load_step ops input t r (loadPrefix input t s r) ht hr pc
      (by simp [prefix_indices, indexed, advance])
      (by simpa only [Reads, prefix_memory] using reads)
    have fuelStep : 63-r = (62-r)+1 := by omega
    rw [fuelStep]
    exact lane_step ops _ _ _ _ _ parkedNone fetch exe
  rw [step 0 (by decide), step 1 (by decide), step 2 (by decide), step 3 (by decide),
      step 4 (by decide), step 5 (by decide), step 6 (by decide), step 7 (by decide),
      step 8 (by decide), step 9 (by decide), step 10 (by decide), step 11 (by decide)]
  change runLane ops layout geometry program t (50+1) (loadPrefix input t s 12) = _
  have pc : (loadPrefix input t s 12).pc t = 13 := by simp [prefix_pc]
  simp only [runLane, parked, pc, program_matrix]
  rfl

def loadPartial (input : Nat → Nat → α) (outside : Location → Option α) : Nat → State α
  | 0 => initial layout input outside
  | k+1 => loaded input k (loadPartial input outside k)

theorem load_pc (input : Nat → Nat → α) (outside : Location → Option α) (k t : Nat) :
    (loadPartial input outside k).pc t = if t < k then 13 else 0 := by
  induction k with
  | zero => simp [loadPartial, initial]
  | succ k ih =>
      simp only [loadPartial, loaded, prefix_pc, ih]
      by_cases he : t = k
      · simp [he]
      · by_cases ht : t < k
        · have hn : t < k+1 := by omega
          simp [he, ht, hn]
        · have hn : ¬ t < k+1 := by omega
          simp [he, ht, hn]

theorem load_indices (input : Nat → Nat → α) (outside : Location → Option α)
    (k t r : Nat) :
    (loadPartial input outside k).indices t r =
      if t < k ∧ r = 0 then some (t : Int) else none := by
  induction k with
  | zero => simp [loadPartial, initial]
  | succ k ih =>
      simp only [loadPartial, loaded, prefix_indices, indexed, advance, ih]
      by_cases he : t = k
      · simp [he]
      · by_cases ht : t < k
        · have hn : t < k+1 := by omega
          simp [he, ht, hn]
        · have hn : ¬ t < k+1 := by omega
          simp [he, ht, hn]

theorem load_regs (input : Nat → Nat → α) (outside : Location → Option α)
    (k t r : Nat) :
    (loadPartial input outside k).regs t r =
      if t < k ∧ r < 12 then some (input (r/4) (address t r)) else none := by
  induction k with
  | zero => simp [loadPartial, initial]
  | succ k ih =>
      simp only [loadPartial, loaded, prefix_regs, ih]
      by_cases he : t = k
      · simp [he]
      · by_cases ht : t < k
        · have hn : t < k+1 := by omega
          simp [he, ht, hn]
        · have hn : ¬ t < k+1 := by omega
          simp [he, ht, hn]

theorem load_memory (input : Nat → Nat → α) (outside : Location → Option α) (k : Nat) :
    (loadPartial input outside k).memory = (initial layout input outside).memory := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [loadPartial, loaded, prefix_memory] using ih

theorem load_fold (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α)
    (k : Nat) (hk : k ≤ 64) :
    (List.range k).foldlM (fun s t => runLane ops layout geometry program t fuel.lane s)
      (initial layout input outside) = some (loadPartial input outside k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [List.range_succ, List.foldlM_append, ih (by omega)]
      simp only [List.foldlM_cons, List.foldlM_nil, bind, pure, Option.bind]
      rw [load_lane ops input k _ (by omega) (by simp [load_pc]) (by
        intro b i hb hi
        rw [load_memory]
        have cases : b = 0 ∨ b = 1 ∨ b = 2 := by omega
        rcases cases with rfl | rfl | rfl <;> simp [initial, layout, cell, hi])]
      rfl

def coordinates : List (Nat × Nat) :=
  (List.range 64).flatMap (fun t => (List.range 4).map (fun e => (t, e)))

theorem coordinates_mem (t e : Nat) :
    (t,e) ∈ coordinates ↔ t < 64 ∧ e < 4 := by
  simp [coordinates, List.mem_flatMap]

-- Use the proved register/memory invariants instead of expanding 64 state updates
-- during higher-order unification of matrix operands.
attribute [irreducible] loadPartial

theorem mapM_some (xs : List ι) (f : ι → Option α) (value : ι → α)
    (h : ∀ x ∈ xs, f x = some (value x)) :
    xs.mapM f = some (xs.map value) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.mapM_cons, h x (by simp), Option.some_bind,
        ih (by intro t ht; exact h t (by simp [ht])), List.map_cons]
      rfl

theorem loaded_a (input : Nat → Nat → α) (outside : Location → Option α)
    (t e : Nat) (ht : t < 64) (he : e < 4) :
    (loadPartial input outside 64).regs t e = some (input 0 (aAddress t e)) := by
  simp [load_regs, address, ht, he, show e < 12 by omega,
    Nat.div_eq_of_lt he, Nat.mod_eq_of_lt he]

theorem loaded_b (input : Nat → Nat → α) (outside : Location → Option α)
    (t e : Nat) (ht : t < 64) (he : e < 4) :
    (loadPartial input outside 64).regs t (4+e) = some (input 1 (bAddress t e)) := by
  simp [load_regs, address, ht, show ¬ 4+e < 4 by omega, show 4+e < 12 by omega,
    show (4+e)/4 = 1 by omega, show (4+e)%4 = e by omega]

theorem loaded_c (input : Nat → Nat → α) (outside : Location → Option α)
    (t e : Nat) (ht : t < 64) (he : e < 4) :
    (loadPartial input outside 64).regs t (8+e) = some (input 2 (bAddress t e)) := by
  simp [load_regs, address, ht, show ¬ 8+e < 4 by omega, show 8+e < 12 by omega,
    show (8+e)/4 = 2 by omega, show (8+e)%4 = e by omega]

def result (ops : Ops α) (input : Nat → Nat → α) (t e : Nat) : α :=
  ops.add (dot ops (fun k => input 0 (outputRow t e * 16 + k))
    (fun k => input 1 (k * 16 + outputCol t))) (input 2 (bAddress t e))

theorem mfma_element (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α)
    (t e : Nat) (ht : t < 64) (he : e < 4) :
    mfmaElement ops geometry (List.range 64) 8 0 4 8
      (loadPartial input outside 64) (t,e) = some ((t,8+e), result ops input t e) := by
  have hr : outputRow t e < 16 := by unfold outputRow; omega
  have hc : outputCol t < 16 := Nat.mod_lt _ (by decide)
  have terms :
      (List.range 16).mapM (fun k => do
        let al := aLane (outputRow t e) k
        let bl := bLane k (outputCol t)
        if !((List.range 64).contains al) ∨ !((List.range 64).contains bl) then none else do
          let av ← (loadPartial input outside 64).regs al (k%4)
          let bv ← (loadPartial input outside 64).regs bl (4+k%4)
          pure (ops.mul (ops.fromHalf av) (ops.fromHalf bv))) =
      some ((List.range 16).map fun k =>
        ops.mul (ops.fromHalf (input 0 (outputRow t e * 16 + k)))
          (ops.fromHalf (input 1 (k * 16 + outputCol t)))) := by
    apply mapM_some
    intro k hk
    have ak := a_source (outputRow t e) k hr (List.mem_range.mp hk)
    have bk := b_source k (outputCol t) (List.mem_range.mp hk) hc
    have hm : k%4 < 4 := Nat.mod_lt _ (by decide)
    simp only [List.contains_iff_mem, List.mem_range, ak.1, bk.1, Bool.not_true,
      Bool.false_eq_true, or_self, ↓reduceIte]
    rw [loaded_a input outside _ _ ak.1 hm, loaded_b input outside _ _ bk.1 hm]
    simp [ak.1, bk.1, ak.2, bk.2]
  unfold mfmaElement
  simp only [geometry, Nat.mod_eq_of_lt ht, Nat.div_eq_of_lt ht, Nat.zero_mul,
    Nat.zero_add]
  rw [terms]
  simp only [bind, pure, Option.bind, loaded_c input outside t e ht he]
  rfl

def values (ops : Ops α) (input : Nat → Nat → α) : List ((Nat × Nat) × α) :=
  coordinates.map (fun (t,e) => ((t,8+e), result ops input t e))

theorem mfma_values (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) :
    mfmaValues ops geometry program (List.range 64) (loadPartial input outside 64) =
      some (values ops input) := by
  have hhead : (List.range 64).head? = some 0 := by decide
  have hpc : (loadPartial input outside 64).pc 0 = 13 := by simp [load_pc]
  rewrite [mfmaValues_of ops geometry program (List.range 64) (loadPartial input outside 64)
    0 8 0 4 8 (by decide) (by decide) (by decide) hhead
    (by rw [hpc]; exact program_matrix)]
  exact mapM_some coordinates
    (mfmaElement ops geometry (List.range 64) 8 0 4 8 (loadPartial input outside 64))
    (fun pair => ((pair.1,8+pair.2), result ops input pair.1 pair.2)) (by
      intro pair hp
      have hm := (coordinates_mem pair.1 pair.2).mp hp
      exact mfma_element ops input outside pair.1 pair.2 hm.1 hm.2)

def matrixState (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) : State α :=
  mfmaUpdates (values ops input) (loadPartial input outside 64)

theorem matrix_eq (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) :
    runMFMA ops geometry program (List.range 64) (loadPartial input outside 64) =
      some (matrixState ops input outside) := by
  exact runMFMA_of ops geometry program (List.range 64) (loadPartial input outside 64)
    (values ops input) (mfma_values ops input outside)

def keys : List (Nat × Nat) := coordinates.map (fun pair => (pair.1,8+pair.2))

theorem keys_mem (t e : Nat) (ht : t < 64) (he : e < 4) : (t,8+e) ∈ keys := by
  apply List.mem_map.mpr
  exact ⟨(t,e), (coordinates_mem t e).mpr ⟨ht,he⟩, rfl⟩

theorem values_keys (ops : Ops α) (input : Nat → Nat → α) :
    values ops input = keys.map (fun key => (key, result ops input key.1 (key.2-8))) := by
  simp [values, keys, List.map_map, Nat.add_sub_cancel_left]

theorem lookup_map (xs : List (Nat × Nat)) (value : (Nat × Nat) → α) (key : Nat × Nat)
    (ht : key ∈ xs) : List.lookup key (xs.map (fun k => (k,value k))) = some (value key) := by
  induction xs with
  | nil => simp at ht
  | cons a xs ih =>
      by_cases he : key = a
      · subst key; simp
      · have hm : key ∈ xs := by simpa [he] using ht
        have hb : (key == a) = false := by simp [he]
        simpa only [List.map_cons, List.lookup_cons, hb] using ih hm

theorem matrix_regs (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α)
    (t e : Nat) (ht : t < 64) (he : e < 4) :
    (matrixState ops input outside).regs t (8+e) = some (result ops input t e) := by
  change (match List.lookup (t,8+e) (values ops input) with
    | some v => some v
    | none => (loadPartial input outside 64).regs t (8+e)) = _
  rewrite [values_keys, lookup_map keys _ (t,8+e) (keys_mem t e ht he)]
  simp [Nat.add_sub_cancel_left]

theorem values_any (ops : Ops α) (input : Nat → Nat → α) (t : Nat) :
    (values ops input).any (fun pair => pair.1.1 == t) = decide (t < 64) := by
  apply Bool.eq_iff_iff.mpr
  simp [values, coordinates, List.any_eq_true, List.mem_flatMap]
  intro _
  exact ⟨0, by decide⟩

theorem matrix_pc (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α)
    (t : Nat) : (matrixState ops input outside).pc t = if t < 64 then 14 else 0 := by
  by_cases ht : t < 64 <;> simp [matrixState, mfmaUpdates, values_any, load_pc, ht]

theorem matrix_indices (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α)
    (t r : Nat) : (matrixState ops input outside).indices t r =
      if t < 64 ∧ r = 0 then some (t : Int) else none := by
  exact load_indices input outside 64 t r

theorem matrix_memory (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) :
    (matrixState ops input outside).memory = (initial layout input outside).memory :=
  load_memory input outside 64

def Safe (trace : List Access) : Prop :=
  ∀ a ∈ trace, (a.write = false ∧ a.location.buffer < 3) ∨
    (a.write = true ∧ a.location.buffer = 3 ∧ a.thread = owner a.location.offset)

theorem safe_raceFree (g : Geometry) (trace : List Access) (hs : Safe trace) :
    raceFree g trace = true := by
  apply List.all_eq_true.mpr
  intro a ha
  apply List.all_eq_true.mpr
  intro b hb
  rcases hs a ha with ⟨haw,hab⟩ | ⟨haw,hab,hat⟩
  · rcases hs b hb with ⟨hbw,hbb⟩ | ⟨hbw,hbb,hbt⟩
    · simp [conflict, haw, hbw]
    · have hn : a.location.buffer ≠ b.location.buffer := by omega
      simp [conflict, sameLocation, hn]
  · rcases hs b hb with ⟨hbw,hbb⟩ | ⟨hbw,hbb,hbt⟩
    · have hn : a.location.buffer ≠ b.location.buffer := by omega
      simp [conflict, sameLocation, hn]
    · by_cases he : a.thread = b.thread
      · simp [conflict, he]
      · have hn : a.location.offset ≠ b.location.offset := by
          intro hh
          apply he
          rw [hat,hbt,hh]
        simp [conflict, sameLocation, hn]

theorem prefix_safe (input : Nat → Nat → α) (t : Nat) (s : State α)
    (n : Nat) (hn : n ≤ 12) (hs : Safe s.trace) :
    Safe (loadPrefix input t s n).trace := by
  induction n with
  | zero => exact hs
  | succ n ih =>
      intro a ha
      simp only [loadPrefix, loadedReg, advance, record, List.mem_cons] at ha
      rcases ha with rfl | ha
      · exact Or.inl ⟨rfl, by simp [cell]; omega⟩
      · exact ih (by omega) a ha

theorem load_safe (input : Nat → Nat → α) (outside : Location → Option α) (k : Nat) :
    Safe (loadPartial input outside k).trace := by
  induction k with
  | zero => simp [Safe, loadPartial, initial]
  | succ k ih =>
      unfold loadPartial
      exact prefix_safe input k _ 12 (by decide) ih

theorem matrix_safe (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) :
    Safe (matrixState ops input outside).trace := load_safe input outside 64

def storedOne (ops : Ops α) (input : Nat → Nat → α) (t e : Nat) (s : State α) : State α :=
  advance { record s t (cell 3 (bAddress t e)) true with
    memory := fun l => if l = cell 3 (bAddress t e)
      then some (result ops input t e) else s.memory l } t (15+e)

def storePrefix (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) : Nat → State α
  | 0 => s
  | n+1 => storedOne ops input t n (storePrefix ops input t s n)

theorem store_prefix_indices (ops : Ops α) (input : Nat → Nat → α)
    (t : Nat) (s : State α) (n : Nat) : (storePrefix ops input t s n).indices = s.indices := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [storePrefix, storedOne, advance, record] using ih

theorem store_prefix_regs (ops : Ops α) (input : Nat → Nat → α)
    (t : Nat) (s : State α) (n : Nat) : (storePrefix ops input t s n).regs = s.regs := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [storePrefix, storedOne, advance, record] using ih

theorem store_prefix_pc (ops : Ops α) (input : Nat → Nat → α)
    (t u : Nat) (s : State α) (n : Nat) (hp : s.pc t = 14) :
    (storePrefix ops input t s n).pc u = if u = t then 14+n else s.pc u := by
  induction n with
  | zero => by_cases he : u = t <;> simp [storePrefix, he, hp]
  | succ n ih =>
      by_cases he : u = t <;> simp [storePrefix, storedOne, advance, record, ih, he, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

theorem store_prefix_final_pc (ops : Ops α) (input : Nat → Nat → α)
    (t u : Nat) (s : State α) :
    (storePrefix ops input t s 4).pc u = if u = t then 18 else s.pc u := by
  by_cases he : u = t <;> simp [storePrefix, storedOne, advance, record, he]

theorem output_injective (t e u v : Nat) (ht : t < 64) (he : e < 4)
    (hu : u < 64) (hv : v < 4) : bAddress t e = bAddress u v ↔ t = u ∧ e = v := by
  constructor
  · intro hh
    have ha := congrArg owner hh
    have hb := congrArg element hh
    exact ⟨by simpa only [(output_owner t e ht he).1, (output_owner u v hu hv).1] using ha,
      by simpa only [(output_owner t e ht he).2, (output_owner u v hu hv).2] using hb⟩
  · rintro ⟨rfl,rfl⟩; rfl

theorem store_prefix_memory (ops : Ops α) (input : Nat → Nat → α)
    (t u v : Nat) (s : State α) (n : Nat) (ht : t < 64) (hu : u < 64) (hv : v < 4)
    (hn : n ≤ 4) :
    (storePrefix ops input t s n).memory (cell 3 (bAddress u v)) =
      if u = t ∧ v < n then some (result ops input u v) else s.memory (cell 3 (bAddress u v)) := by
  induction n with
  | zero => simp [storePrefix]
  | succ n ih =>
      have hi : n < 4 := by omega
      have eqcell : cell 3 (bAddress u v) = cell 3 (bAddress t n) ↔ u = t ∧ v = n := by
        constructor
        · intro hh
          exact (output_injective u v t n hu hv ht hi).mp (congrArg Location.offset hh)
        · rintro ⟨rfl,rfl⟩; rfl
      simp only [storePrefix, storedOne, advance, record]
      by_cases he : u = t ∧ v = n
      · rcases he with ⟨rfl,rfl⟩
        simp
      · have hne : cell 3 (bAddress u v) ≠ cell 3 (bAddress t n) := by
          intro hh; exact he (eqcell.mp hh)
        rewrite [if_neg hne, ih (by omega)]
        by_cases hut : u = t
        · have hvn : v ≠ n := by intro hh; exact he ⟨hut,hh⟩
          have hsame : (v < n+1) = (v < n) := propext (by omega)
          simp only [hut, true_and, hsame]
        · simp [hut]

theorem store_prefix_safe (ops : Ops α) (input : Nat → Nat → α)
    (t : Nat) (s : State α) (n : Nat) (ht : t < 64) (hn : n ≤ 4) (hs : Safe s.trace) :
    Safe (storePrefix ops input t s n).trace := by
  induction n with
  | zero => exact hs
  | succ n ih =>
      intro a ha
      simp only [storePrefix, storedOne, advance, record, List.mem_cons] at ha
      rcases ha with rfl | ha
      · exact Or.inr ⟨rfl, rfl, (output_owner t n ht (by omega)).1.symm⟩
      · exact ih (by omega) a ha

theorem program_store (e : Nat) (he : e < 4) :
    program[14+e]? = some (storeInstruction e) := by
  have cases : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl <;> decide

theorem store_step (ops : Ops α) (input : Nat → Nat → α) (t e : Nat) (s : State α)
    (ht : t < 64) (he : e < 4) (hp : s.pc t = 14+e)
    (hi : s.indices t 0 = some (t : Int)) (hr : s.regs t (8+e) = some (result ops input t e)) :
    execute ops layout geometry t (.store .global 3 (bIndex e) (.reg (8+e))) s =
      some (storedOne ops input t e s) := by
  have hindex := (address_eval t e s ht he hi).2
  have hbound := (addresses_bound t e ht he).2
  have hnonnegative : ¬ ((bAddress t e : Nat) : Int) < 0 := by omega
  have hrole : (Role.output == Role.input) = false := by decide
  have hlocation : location layout geometry t .global 3 (bAddress t e : Int) true =
      some (cell 3 (bAddress t e)) := by
    simp [location, layout, cell, hnonnegative, hbound, hrole]
  simp only [execute, evalExpr, hindex, hlocation, hr, bind, pure, Option.bind]
  simp [storedOne, advance, record, hp, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem store_lane (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α)
    (ht : t < 64) (hp : s.pc t = 14) (hi : s.indices t 0 = some (t : Int))
    (hr : ∀ e, e < 4 → s.regs t (8+e) = some (result ops input t e)) :
    runLane ops layout geometry program t fuel.lane s = some (storePrefix ops input t s 4) := by
  change runLane ops layout geometry program t 64 (storePrefix ops input t s 0) = _
  have step (e : Nat) (he : e < 4) :
      runLane ops layout geometry program t (64-e) (storePrefix ops input t s e) =
      runLane ops layout geometry program t (63-e) (storePrefix ops input t s (e+1)) := by
    have pc : (storePrefix ops input t s e).pc t = 14+e := by
      simp [store_prefix_pc, hp]
    have fetch : program[(storePrefix ops input t s e).pc t]? = some (storeInstruction e) := by
      simpa [pc] using program_store e he
    have parkedNone : parked program (storePrefix ops input t s e) t = none := by
      simp [parked, fetch, storeInstruction]
    have exe := store_step ops input t e (storePrefix ops input t s e) ht he pc
      (by simpa only [store_prefix_indices] using hi)
      (by simpa only [store_prefix_regs] using hr e he)
    have fuelStep : 64-e = (63-e)+1 := by omega
    rewrite [fuelStep]
    exact lane_step ops _ _ _ _ _ parkedNone fetch exe
  rewrite [step 0 (by decide), step 1 (by decide), step 2 (by decide), step 3 (by decide)]
  change runLane ops layout geometry program t (59+1) (storePrefix ops input t s 4) = _
  have pc : (storePrefix ops input t s 4).pc t = 18 := by simp [store_prefix_final_pc]
  simp only [runLane, parked, pc, program_halt]

def storePartial (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) : Nat → State α
  | 0 => matrixState ops input outside
  | k+1 => storePrefix ops input k (storePartial ops input outside k) 4

theorem store_pc (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α)
    (k t : Nat) : (storePartial ops input outside k).pc t =
      if t < k then 18 else if t < 64 then 14 else 0 := by
  induction k with
  | zero => simp [storePartial, matrix_pc]
  | succ k ih =>
      simp only [storePartial, store_prefix_final_pc, ih]
      by_cases he : t = k
      · simp [he]
      · by_cases ht : t < k
        · have hn : t < k+1 := by omega
          simp [he,ht,hn]
        · have hn : ¬ t < k+1 := by omega
          simp [he,ht,hn]

theorem store_indices (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α)
    (k t r : Nat) : (storePartial ops input outside k).indices t r =
      if t < 64 ∧ r = 0 then some (t : Int) else none := by
  induction k with
  | zero => exact matrix_indices ops input outside t r
  | succ k ih => simpa only [storePartial, store_prefix_indices] using ih

theorem store_regs (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α)
    (k t e : Nat) (ht : t < 64) (he : e < 4) :
    (storePartial ops input outside k).regs t (8+e) = some (result ops input t e) := by
  induction k with
  | zero => exact matrix_regs ops input outside t e ht he
  | succ k ih => simpa only [storePartial, store_prefix_regs] using ih

theorem store_output (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α)
    (k t e : Nat) (hk : k ≤ 64) (ht : t < k) (he : e < 4) :
    (storePartial ops input outside k).memory (cell 3 (bAddress t e)) = some (result ops input t e) := by
  induction k with
  | zero => omega
  | succ k ih =>
      rewrite [storePartial, store_prefix_memory ops input k t e _ 4 (by omega) (by omega) he (by decide)]
      by_cases htk : t = k
      · simp [htk,he]
      · rewrite [if_neg (by simp [htk])]
        exact ih (by omega) (by omega)

theorem store_safe (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α)
    (k : Nat) (hk : k ≤ 64) : Safe (storePartial ops input outside k).trace := by
  induction k with
  | zero => exact matrix_safe ops input outside
  | succ k ih => exact store_prefix_safe ops input k _ 4 (by omega) (by decide) (ih (by omega))

theorem store_fold (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α)
    (k : Nat) (hk : k ≤ 64) :
    (List.range k).foldlM (fun s t => runLane ops layout geometry program t fuel.lane s)
      (matrixState ops input outside) = some (storePartial ops input outside k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rewrite [List.range_succ, List.foldlM_append, ih (by omega)]
      simp only [List.foldlM_cons, List.foldlM_nil, bind, pure, Option.bind]
      rewrite [store_lane ops input k _ (by omega) (by simp [store_pc, show k < 64 by omega])
        (by simp [store_indices, show k < 64 by omega])
        (by intro e he; exact store_regs ops input outside k k e (by omega) he)]
      rfl

theorem converged_load (input : Nat → Nat → α) (outside : Location → Option α) :
    converged program (List.range 64) (loadPartial input outside 64) = some .matrix := by
  have hhead : (List.range 64).head? = some 0 := by decide
  have ha : (List.range 64).all (fun t => (loadPartial input outside 64).pc t ==
      (loadPartial input outside 64).pc 0) = true := by
    apply List.all_eq_true.mpr
    intro t ht
    simp [load_pc, List.mem_range.mp ht]
  simp only [converged, hhead, bind, pure, Option.bind, ha, ↓reduceIte]
  simp only [parked, load_pc, show (0:Nat)<64 by decide, ↓reduceIte, program_matrix]

theorem converged_store (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) :
    converged program (List.range 64) (storePartial ops input outside 64) = some .halt := by
  have hhead : (List.range 64).head? = some 0 := by decide
  have ha : (List.range 64).all (fun t => (storePartial ops input outside 64).pc t ==
      (storePartial ops input outside 64).pc 0) = true := by
    apply List.all_eq_true.mpr
    intro t ht
    simp [store_pc, List.mem_range.mp ht]
  simp only [converged, hhead, bind, pure, Option.bind, ha, ↓reduceIte]
  simp only [parked, store_pc, show (0:Nat)<64 by decide, ↓reduceIte, program_halt]

theorem warp_eq (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) :
    runWarp ops layout geometry fuel program (List.range 64) fuel.warp
      (initial layout input outside) = some (storePartial ops input outside 64) := by
  have h1 := runWarp_matrix_step ops layout geometry fuel program (List.range 64) 7
    (initial layout input outside) (loadPartial input outside 64) (matrixState ops input outside)
    (load_fold ops input outside 64 (by decide)) (converged_load input outside)
    (matrix_eq ops input outside)
  have h2 := runWarp_halt ops layout geometry fuel program (List.range 64) 6
    (matrixState ops input outside) (storePartial ops input outside 64)
    (store_fold ops input outside 64 (by decide)) (converged_store ops input outside)
  exact h1.trans h2

theorem block_eq (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) :
    runBlock ops layout geometry fuel program 0 fuel.block (initial layout input outside) =
      some (storePartial ops input outside 64) := by
  have hws : List.range ((geometry.block+geometry.warp-1)/geometry.warp) = [0] := by decide
  have hwarp : warpThreads geometry 0 0 = List.range 64 := by decide
  have hblock : blockThreads geometry 0 = List.range 64 := by decide
  have hf : (List.range ((geometry.block+geometry.warp-1)/geometry.warp)).foldlM
      (fun s w => runWarp ops layout geometry fuel program (warpThreads geometry 0 w) fuel.warp s)
      (initial layout input outside) = some (storePartial ops input outside 64) := by
    rewrite [hws, foldlM_singleton, hwarp]
    exact warp_eq ops input outside
  exact runBlock_halt ops layout geometry fuel program 0 7 _ _ hf
    (by rewrite [hblock]; exact converged_store ops input outside)

theorem grid_eq (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) :
    runGrid ops layout geometry fuel program fuel.grid (initial layout input outside) =
      some (storePartial ops input outside 64) := by
  have hblocks : List.range geometry.grid = [0] := by decide
  have hthreads : List.range (geometry.grid*geometry.block) = List.range 64 := by decide
  have hf : (List.range geometry.grid).foldlM
      (fun s b => runBlock ops layout geometry fuel program b fuel.block s)
      (initial layout input outside) = some (storePartial ops input outside 64) := by
    rewrite [hblocks, foldlM_singleton]
    exact block_eq ops input outside
  exact runGrid_halt ops layout geometry fuel program 7 _ _ hf
    (by rewrite [hthreads]; exact converged_store ops input outside)

theorem launch_eq (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) :
    runLaunch ops layout geometry fuel program (initial layout input outside) =
      some (storePartial ops input outside 64) := by
  exact (runLaunch_of ops layout geometry fuel program (initial layout input outside)
    (by decide) (by decide) (by decide) (by decide)).trans (grid_eq ops input outside)

def outputValue (ops : Ops α) (input : Nat → Nat → α) (offset : Nat) : α :=
  ops.add (dot ops (fun k => input 0 ((offset/16)*16+k))
    (fun k => input 1 (k*16+offset%16))) (input 2 offset)

def spec (ops : Ops α) (input : Nat → Nat → α) : List α :=
  (List.range 256).map (outputValue ops input)

theorem result_value (ops : Ops α) (input : Nat → Nat → α) (offset : Nat) (h : offset < 256) :
    result ops input (owner offset) (element offset) = outputValue ops input offset := by
  have hrow : outputRow (owner offset) (element offset) = offset/16 := by
    unfold outputRow owner element
    omega
  have hcol : outputCol (owner offset) = offset%16 := by unfold outputCol owner; omega
  simp only [result, outputValue, hrow, hcol, (output_inverse offset h).2.2]

theorem final_cell (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α)
    (offset : Nat) (h : offset < 256) :
    (storePartial ops input outside 64).memory (cell 3 offset) = some (outputValue ops input offset) := by
  have hi := output_inverse offset h
  have hs := store_output ops input outside 64 (owner offset) (element offset) (by decide) hi.1 hi.2.1
  rewrite [hi.2.2, result_value ops input offset h] at hs
  exact hs

theorem mapM_map (f : ι → κ) (g : κ → Option α) (xs : List ι) :
    (xs.map f).mapM g = xs.mapM (fun x => g (f x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [List.mapM_cons, ih, bind, pure, Option.bind]

theorem final_extract (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) :
    extract layout (storePartial ops input outside 64) = some (spec ops input) := by
  simp only [extract, layout, List.zipIdx_cons, List.zipIdx_nil, List.flatMap_cons,
    List.flatMap_nil, List.nil_append]
  simp only [List.map_cons, List.map_nil, show Role.input ≠ Role.output by decide,
    ↓reduceIte, List.nil_append, List.append_nil]
  change (((List.range 256).map (fun i => (3,i))).mapM
    (fun bi => (storePartial ops input outside 64).memory ⟨.global,0,bi.1,bi.2⟩) :
      Option (List α)) = _
  rewrite [mapM_map]
  exact mapM_some (List.range 256) _ _ (by
    intro t ht
    exact final_cell ops input outside t (List.mem_range.mp ht))

/-- Actual full-wave launch completion, race freedom and all matrix outputs. -/
theorem correct (ops : Ops α) : Correct ops layout geometry fuel program (spec ops) := by
  intro input outside
  exact ⟨storePartial ops input outside 64, launch_eq ops input outside,
    safe_raceFree geometry _ (store_safe ops input outside 64 (by decide)),
    final_extract ops input outside⟩

#print axioms load_fold
#print axioms mfma_element
#print axioms matrix_eq
#print axioms safe_raceFree
#print axioms store_fold
#print axioms correct
end LarkMFMA.Tile
