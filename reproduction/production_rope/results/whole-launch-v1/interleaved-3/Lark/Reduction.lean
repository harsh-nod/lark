import Lark.Pointwise

/-!
Induction for the actual scalar machine's counted dot-product loop and grid.
The machine model is unchanged. The conclusion is its existing Correct predicate,
including completion, race freedom and every output, for all inputs/outside memory.
-/
namespace LarkReduction
open LarkNonlinear
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def layout (n k : Nat) : Layout :=
  ⟨[⟨.input, n*k⟩, ⟨.input, k⟩, ⟨.output, n⟩], [], []⟩
def geometry (n w : Nat) : Geometry := LarkPointwise.geometry n w
def cell (b i : Nat) : Location := ⟨.global, 0, b, i⟩
def matrixIndex (k : Nat) : Index :=
  .add (.mul (.ivar 0) (.const (k : Int))) (.ivar 1)

def program (k : Nat) : List Instr :=
  [.index 0 .bid,
   .assign 0 (.lit 0 1),
   .index 1 (.const 0),
   .branch (.lt (.ivar 1) (.const (k : Int))) 7,
   .assign 0 (.bin .add (.reg 0) (.bin .mul
     (.un .fromHalf (.load .global 0 (matrixIndex k)))
     (.un .fromHalf (.load .global 1 (.ivar 1))))),
   .index 1 (.add (.ivar 1) (.const 1)),
   .jump 3,
   .store .global 2 (.ivar 0) (.un .toHalf (.reg 0)),
   .halt]

def Reads (n k : Nat) (input : Nat → Nat → α) (s : State α) : Prop :=
  (∀ i, i < n*k → s.memory (cell 0 i) = some (input 0 i)) ∧
  (∀ j, j < k → s.memory (cell 1 j) = some (input 1 j))

def setIndex (s : State α) (t r : Nat) (v : Int) (pc : Nat) : State α :=
  advance { s with indices := fun u q => if u = t ∧ q = r then some v else s.indices u q } t pc
def setReg (s : State α) (t r : Nat) (v : α) (pc : Nat) : State α :=
  advance { s with regs := fun u q => if u = t ∧ q = r then some v else s.regs u q } t pc

def term (ops : Ops α) (input : Nat → Nat → α) (k t j : Nat) : α :=
  ops.mul (ops.fromHalf (input 0 (t*k+j))) (ops.fromHalf (input 1 j))

def next (ops : Ops α) (input : Nat → Nat → α) (k t j : Nat) (acc : α)
    (s : State α) : State α :=
  let s := advance s t 4
  let s := record (record s t (cell 0 (t*k+j)) false) t (cell 1 j) false
  let s := setReg s t 0 (ops.add acc (term ops input k t j)) 5
  let s := setIndex s t 1 ((j+1 : Nat) : Int) 6
  advance s t 3

def stored (ops : Ops α) (t : Nat) (acc : α) (s : State α) : State α :=
  advance { record s t (cell 2 t) true with
    memory := fun l => if l = cell 2 t then some (ops.toHalf acc) else s.memory l } t 8

def iterate (ops : Ops α) (input : Nat → Nat → α) (k t : Nat) :
    Nat → Nat → α → State α → State α
  | _, 0, acc, s => stored ops t acc (advance s t 7)
  | j, r+1, acc, s => iterate ops input k t (j+1) r
      (ops.add acc (term ops input k t j)) (next ops input k t j acc s)

def folded (ops : Ops α) (input : Nat → Nat → α) (k t : Nat) : Nat → Nat → α → α
  | _, 0, acc => acc
  | j, r+1, acc => folded ops input k t (j+1) r (ops.add acc (term ops input k t j))

def initialized (ops : Ops α) (t : Nat) (s : State α) : State α :=
  setIndex (setReg (setIndex s t 0 (t : Int) 1) t 0 (ops.literal 0 1) 2) t 1 0 3

def finished (ops : Ops α) (input : Nat → Nat → α) (k t : Nat) (s : State α) : State α :=
  iterate ops input k t 0 k (ops.literal 0 1) (initialized ops t s)

def result (ops : Ops α) (input : Nat → Nat → α) (k t : Nat) : α :=
  ops.toHalf (folded ops input k t 0 k (ops.literal 0 1))

theorem int32_cast (n : Nat) (h : n < 2147483648) :
    int32 (n : Int) = some (n : Int) := by
  have h0 : (0 : Int) ≤ (n : Int) := by omega
  have h1 : (n : Int) < 2147483648 := by omega
  simp [int32, h0, h1]

theorem address_bound (n k t j : Nat) (ht : t < n) (hj : j < k) :
    t*k+j < n*k := by
  calc
    t*k+j < t*k+k := Nat.add_lt_add_left hj _
    _ = (t+1)*k := by simp [Nat.add_mul]
    _ ≤ n*k := Nat.mul_le_mul_right k (by omega)

theorem k_bound (n k : Nat) (hn : 0 < n) (hb : n*k < 2147483648) :
    k < 2147483648 := by
  have he := Nat.mul_le_mul_right k (show 1 ≤ n by omega)
  simp only [Nat.one_mul] at he
  omega

theorem eval_mul_of (g : Geometry) (t : Nat) (s : State α) (a b : Index) (x y z : Int)
    (ha : evalIndex g t s a = some x) (hb : evalIndex g t s b = some y)
    (hop : int32 (x*y) = some z) : evalIndex g t s (.mul a b) = some z := by
  change (do let p ← evalIndex g t s a; let q ← evalIndex g t s b; int32 (p*q)) = _
  rw [ha, hb]
  exact hop

theorem eval_add_of (g : Geometry) (t : Nat) (s : State α) (a b : Index) (x y z : Int)
    (ha : evalIndex g t s a = some x) (hb : evalIndex g t s b = some y)
    (hop : int32 (x+y) = some z) : evalIndex g t s (.add a b) = some z := by
  change (do let p ← evalIndex g t s a; let q ← evalIndex g t s b; int32 (p+q)) = _
  rw [ha, hb]
  exact hop

theorem execute_index_of (ops : Ops α) (l : Layout) (g : Geometry) (t r pc : Nat)
    (ix : Index) (s : State α) (v : Int) (he : evalIndex g t s ix = some v)
    (hp : s.pc t + 1 = pc) :
    execute ops l g t (.index r ix) s = some (setIndex s t r v pc) := by
  simp only [execute, he, hp, bind, pure, Option.bind]
  rfl

theorem execute_pure_of (ops : Ops α) (l : Layout) (g : Geometry) (t r pc : Nat)
    (e : Expr) (s : State α) (v : α) (he : evalExpr ops l g t e s = some (v,s))
    (hp : s.pc t + 1 = pc) :
    execute ops l g t (.assign r e) s = some (setReg s t r v pc) := by
  simp only [execute, he, hp, bind, pure, Option.bind]
  rfl

theorem bid_index (n w t : Nat) (s : State α) (ht : t < 2147483648) :
    evalIndex (geometry n w) t s .bid = some (t : Int) := by
  simp only [evalIndex, geometry, LarkPointwise.geometry, Nat.div_one]
  exact int32_cast t ht

theorem matrix_index (g : Geometry) (t k j : Nat) (s : State α)
    (hi : s.indices t 0 = some (t : Int)) (hj : s.indices t 1 = some (j : Int))
    (hk : k < 2147483648) (hm : t*k < 2147483648) (ha : t*k+j < 2147483648) :
    evalIndex g t s (matrixIndex k) = some ((t*k+j : Nat) : Int) := by
  have hmul : evalIndex g t s (.mul (.ivar 0) (.const (k : Int))) =
      some ((t*k : Nat) : Int) := by
    exact eval_mul_of g t s _ _ (t : Int) (k : Int) ((t*k : Nat) : Int) hi
      (int32_cast k hk) (Eq.trans
        (congrArg int32 (Int.natCast_mul t k).symm) (int32_cast (t*k) hm))
  exact eval_add_of g t s _ _ ((t*k : Nat) : Int) (j : Int) ((t*k+j : Nat) : Int)
    hmul hj (Eq.trans (congrArg int32 (Int.natCast_add (t*k) j).symm)
      (int32_cast (t*k+j) ha))

theorem matrix_location (n k t i : Nat) (g : Geometry) (hi : i < n*k) :
    location (layout n k) g t .global 0 (i : Int) false = some (cell 0 i) := by
  have hneg : ¬ (i : Int) < 0 := by omega
  simp [location, layout, cell, hneg, hi]

theorem load_matrix (ops : Ops α) (n k w t j : Nat) (s : State α)
    (input : Nat → Nat → α) (hr : Reads n k input s)
    (hi : s.indices t 0 = some (t : Int)) (hij : s.indices t 1 = some (j : Int))
    (ht : t < n) (hj : j < k) (hb : n*k < 2147483648) :
    evalExpr ops (layout n k) (geometry n w) t
      (.un .fromHalf (.load .global 0 (matrixIndex k))) s =
      some (ops.fromHalf (input 0 (t*k+j)), record s t (cell 0 (t*k+j)) false) := by
  have ha := address_bound n k t j ht hj
  have hix := matrix_index (geometry n w) t k j s hi hij
    (k_bound n k (by omega) hb) (by omega) (by omega)
  have hl := matrix_location n k t (t*k+j) (geometry n w) ha
  simp only [evalExpr, hix, bind, pure, Option.bind, hl, hr.1 _ ha]
  rfl

theorem load_vector (ops : Ops α) (n k w t j : Nat) (s : State α)
    (input : Nat → Nat → α) (hr : Reads n k input s)
    (hij : s.indices t 1 = some (j : Int)) (hj : j < k) :
    evalExpr ops (layout n k) (geometry n w) t
      (.un .fromHalf (.load .global 1 (.ivar 1))) s =
      some (ops.fromHalf (input 1 j), record s t (cell 1 j) false) := by
  have hneg : ¬ (j : Int) < 0 := by omega
  have hl : location (layout n k) (geometry n w) t .global 1
      (j : Int) false = some (cell 1 j) := by
    simp [location, layout, cell, hneg, hj]
  simp only [evalExpr, evalIndex, hij, bind, pure, Option.bind, hl, hr.2 _ hj]
  rfl

theorem reads_advance (n k t pc : Nat) (input : Nat → Nat → α) (s : State α)
    (h : Reads n k input s) : Reads n k input (advance s t pc) := h

theorem reads_record (n k t : Nat) (input : Nat → Nat → α) (s : State α)
    (l : Location) (write : Bool) (h : Reads n k input s) :
    Reads n k input (record s t l write) := h

theorem eval_bin_of (ops : Ops α) (l : Layout) (g : Geometry) (t : Nat)
    (op : Binary) (a b : Expr) (s s1 s2 : State α) (x y : α)
    (ha : evalExpr ops l g t a s = some (x, s1))
    (hb : evalExpr ops l g t b s1 = some (y, s2)) :
    evalExpr ops l g t (.bin op a b) s = some (applyBinary ops op x y, s2) := by
  change (do let (x, first) ← evalExpr ops l g t a s
             let (y, last) ← evalExpr ops l g t b first
             pure (applyBinary ops op x y, last)) = _
  rw [ha]
  simp only [bind, pure, Option.bind]
  rw [hb]

theorem predicate_lt_of (g : Geometry) (t : Nat) (s : State α)
    (a b : Index) (x y : Int) (ha : evalIndex g t s a = some x)
    (hb : evalIndex g t s b = some y) (hxy : x < y) :
    evalPredicate g t s (.lt a b) = some true := by
  simp only [evalPredicate, ha, hb, bind, pure, Option.bind, hxy]
  rfl

theorem predicate_nlt_of (g : Geometry) (t : Nat) (s : State α)
    (a b : Index) (x y : Int) (ha : evalIndex g t s a = some x)
    (hb : evalIndex g t s b = some y) (hxy : ¬ x < y) :
    evalPredicate g t s (.lt a b) = some false := by
  simp only [evalPredicate, ha, hb, bind, pure, Option.bind, hxy]
  rfl

theorem eval_accumulate (ops : Ops α) (n k w t j : Nat) (s : State α)
    (input : Nat → Nat → α) (acc : α) (hr : Reads n k input s)
    (hi : s.indices t 0 = some (t : Int)) (hij : s.indices t 1 = some (j : Int))
    (hacc : s.regs t 0 = some acc) (ht : t < n) (hj : j < k)
    (hb : n*k < 2147483648) :
    evalExpr ops (layout n k) (geometry n w) t
      (.bin .add (.reg 0) (.bin .mul
        (.un .fromHalf (.load .global 0 (matrixIndex k)))
        (.un .fromHalf (.load .global 1 (.ivar 1))))) s =
      some (ops.add acc (term ops input k t j),
        record (record s t (cell 0 (t*k+j)) false) t (cell 1 j) false) := by
  have ha := load_matrix ops n k w t j s input hr hi hij ht hj hb
  have hbs := load_vector ops n k w t j (record s t (cell 0 (t*k+j)) false)
    input hr hij hj
  have hm := eval_bin_of ops (layout n k) (geometry n w) t .mul _ _ _ _ _ _ _ ha hbs
  have hreg : evalExpr ops (layout n k) (geometry n w) t (.reg 0) s = some (acc, s) := by
    simp [evalExpr, hacc]
  exact eval_bin_of ops (layout n k) (geometry n w) t .add _ _ _ _ _ _ _ hreg hm

theorem branch_true (ops : Ops α) (n k w t j : Nat) (s : State α)
    (hp : s.pc t = 3) (hij : s.indices t 1 = some (j : Int))
    (hj : j < k) (hk : k < 2147483648) :
    execute ops (layout n k) (geometry n w) t
      (.branch (.lt (.ivar 1) (.const (k : Int))) 7) s = some (advance s t 4) := by
  have he := predicate_lt_of (geometry n w) t s (.ivar 1) (.const (k : Int))
    (j : Int) (k : Int) hij (int32_cast k hk) (by omega)
  simp only [execute, he, bind, pure, Option.bind, hp]
  rfl

theorem execute_accumulate (ops : Ops α) (n k w t j : Nat) (s : State α)
    (input : Nat → Nat → α) (acc : α) (hr : Reads n k input s)
    (hi : s.indices t 0 = some (t : Int)) (hij : s.indices t 1 = some (j : Int))
    (hacc : s.regs t 0 = some acc) (hp : s.pc t = 4)
    (ht : t < n) (hj : j < k) (hb : n*k < 2147483648) :
    execute ops (layout n k) (geometry n w) t
      (.assign 0 (.bin .add (.reg 0) (.bin .mul
        (.un .fromHalf (.load .global 0 (matrixIndex k)))
        (.un .fromHalf (.load .global 1 (.ivar 1)))))) s =
      some (setReg (record (record s t (cell 0 (t*k+j)) false) t (cell 1 j) false)
        t 0 (ops.add acc (term ops input k t j)) 5) := by
  have he := eval_accumulate ops n k w t j s input acc hr hi hij hacc ht hj hb
  simp only [execute, he, bind, pure, Option.bind, hp]
  rfl

theorem execute_counter (ops : Ops α) (n k w t j : Nat) (s : State α)
    (hij : s.indices t 1 = some (j : Int)) (hp : s.pc t = 5)
    (hj : j+1 < 2147483648) :
    execute ops (layout n k) (geometry n w) t
      (.index 1 (.add (.ivar 1) (.const 1))) s =
      some (setIndex s t 1 ((j+1 : Nat) : Int) 6) := by
  have hi : evalIndex (geometry n w) t s (.add (.ivar 1) (.const 1)) =
      some ((j+1 : Nat) : Int) :=
    eval_add_of (geometry n w) t s _ _ (j : Int) 1 ((j+1 : Nat) : Int) hij
      (by rfl) (Eq.trans (congrArg int32 (Int.natCast_add j 1).symm) (int32_cast (j+1) hj))
  simp only [execute, hi, hp, bind, pure, Option.bind]
  rfl

theorem loop_step (ops : Ops α) (n k w t j f : Nat) (s : State α)
    (input : Nat → Nat → α) (acc : α) (hr : Reads n k input s)
    (hi : s.indices t 0 = some (t : Int)) (hij : s.indices t 1 = some (j : Int))
    (hacc : s.regs t 0 = some acc) (hp : s.pc t = 3)
    (ht : t < n) (hj : j < k) (hb : n*k < 2147483648) :
    runLane ops (layout n k) (geometry n w) (program k) t (f+4) s =
      runLane ops (layout n k) (geometry n w) (program k) t f
        (next ops input k t j acc s) := by
  let s1 := advance s t 4
  let s2 := setReg (record (record s1 t (cell 0 (t*k+j)) false) t (cell 1 j) false)
    t 0 (ops.add acc (term ops input k t j)) 5
  let s3 := setIndex s2 t 1 ((j+1 : Nat) : Int) 6
  have hk := k_bound n k (by omega) hb
  have h1 := branch_true ops n k w t j s hp hij hj hk
  have h2 := execute_accumulate ops n k w t j s1 input acc hr hi hij hacc
    (by simp [s1, advance]) ht hj hb
  change execute ops (layout n k) (geometry n w) t _ s1 = some s2 at h2
  have h3 := execute_counter ops n k w t j s2
    (by simpa [s2, setReg, record, s1, advance] using hij)
    (by simp [s2, setReg, advance]) (by omega)
  change execute ops (layout n k) (geometry n w) t _ s2 = some s3 at h3
  have h4 : execute ops (layout n k) (geometry n w) t (.jump 3) s3 =
      some (next ops input k t j acc s) := by rfl
  rw [LarkPointwise.lane_step ops _ _ _ _ _ _ _ _
    (by simp [parked, program, hp]) (by simp [program, hp]) h1]
  rw [LarkPointwise.lane_step ops _ _ _ _ _ _ _ _
    (by simp [parked, program, s1, advance]) (by simp [program, s1, advance]) h2]
  rw [LarkPointwise.lane_step ops _ _ _ _ _ _ _ _
    (by simp [parked, program, s2, setReg, advance])
    (by simp [program, s2, setReg, advance]) h3]
  rw [LarkPointwise.lane_step ops _ _ _ _ _ _ _ _
    (by simp [parked, program, s3, setIndex, advance])
    (by simp [program, s3, setIndex, advance]) h4]

theorem execute_store (ops : Ops α) (n k w t : Nat) (s : State α) (acc : α)
    (hi : s.indices t 0 = some (t : Int)) (hacc : s.regs t 0 = some acc)
    (hp : s.pc t = 7) (ht : t < n) :
    execute ops (layout n k) (geometry n w) t
      (.store .global 2 (.ivar 0) (.un .toHalf (.reg 0))) s = some (stored ops t acc s) := by
  have hneg : ¬ (t : Int) < 0 := by omega
  have hrole : (Role.output == Role.input) = false := by decide
  have hl : location (layout n k) (geometry n w) t .global 2 (t : Int) true =
      some (cell 2 t) := by simp [location, layout, cell, hneg, ht, hrole]
  have he : evalExpr ops (layout n k) (geometry n w) t (.un .toHalf (.reg 0)) s =
      some (ops.toHalf acc, s) := by simp [evalExpr, hacc, applyUnary]
  simp only [execute, evalIndex, hi, bind, pure, Option.bind, hl, he, hp]
  rfl

theorem loop_done (ops : Ops α) (n k w t : Nat) (s : State α) (acc : α)
    (hi : s.indices t 0 = some (t : Int)) (hij : s.indices t 1 = some (k : Int))
    (hacc : s.regs t 0 = some acc) (hp : s.pc t = 3)
    (ht : t < n) (hk : k < 2147483648) :
    runLane ops (layout n k) (geometry n w) (program k) t 3 s =
      some (stored ops t acc (advance s t 7)) := by
  have hg := predicate_nlt_of (geometry n w) t s (.ivar 1) (.const (k : Int))
    (k : Int) (k : Int) hij (int32_cast k hk) (by omega)
  have h1 : execute ops (layout n k) (geometry n w) t
      (.branch (.lt (.ivar 1) (.const (k : Int))) 7) s = some (advance s t 7) := by
    simp only [execute, hg, bind, pure, Option.bind]
    rfl
  have h2 := execute_store ops n k w t (advance s t 7) acc hi hacc
    (by simp [advance]) ht
  rw [LarkPointwise.lane_step ops _ _ _ _ _ _ _ _
    (by simp [parked, program, hp]) (by simp [program, hp]) h1]
  rw [LarkPointwise.lane_step ops _ _ _ _ _ _ _ _
    (by simp [parked, program, advance]) (by simp [program, advance]) h2]
  simp [runLane, parked, program, stored, advance]

theorem loop_eq (ops : Ops α) (n k w t r : Nat) (j : Nat) (s : State α)
    (input : Nat → Nat → α) (acc : α) (hr : Reads n k input s)
    (hi : s.indices t 0 = some (t : Int)) (hij : s.indices t 1 = some (j : Int))
    (hacc : s.regs t 0 = some acc) (hp : s.pc t = 3)
    (ht : t < n) (hcount : j+r=k) (hb : n*k < 2147483648) :
    runLane ops (layout n k) (geometry n w) (program k) t (4*r+3) s =
      some (iterate ops input k t j r acc s) := by
  induction r generalizing j acc s with
  | zero =>
      have hj : j=k := by omega
      subst j
      simpa [iterate] using loop_done ops n k w t s acc hi hij hacc hp ht
        (k_bound n k (by omega) hb)
  | succ r ih =>
      have hlt : j<k := by omega
      have hf : 4*(r+1)+3 = (4*r+3)+4 := by omega
      rw [hf, loop_step ops n k w t j (4*r+3) s input acc hr hi hij hacc hp ht hlt hb]
      change _ = some (iterate ops input k t (j+1) r _ _)
      apply ih
      · exact hr
      · simpa [next, setIndex, setReg, advance, record] using hi
      · simp [next, setIndex, setReg, advance, record]
      · simp [next, setIndex, setReg, advance, record]
      · simp [next, advance]
      · omega

theorem iterate_memory (ops : Ops α) (input : Nat → Nat → α) (k t r j : Nat)
    (acc : α) (s : State α) (l : Location) :
    (iterate ops input k t j r acc s).memory l =
      if l = cell 2 t then some (ops.toHalf (folded ops input k t j r acc)) else s.memory l := by
  induction r generalizing j acc s with
  | zero => rfl
  | succ r ih =>
      change (iterate ops input k t (j+1) r _ _).memory l = _
      exact ih (j+1) (ops.add acc (term ops input k t j)) (next ops input k t j acc s)

theorem iterate_pc (ops : Ops α) (input : Nat → Nat → α) (k t r j : Nat)
    (acc : α) (s : State α) (u : Nat) :
    (iterate ops input k t j r acc s).pc u = if u=t then 8 else s.pc u := by
  induction r generalizing j acc s with
  | zero =>
      by_cases hu : u=t <;> simp [iterate, stored, advance, record, hu]
  | succ r ih =>
      change (iterate ops input k t (j+1) r _ _).pc u = _
      rw [ih]
      by_cases hu : u=t <;>
        simp [next, setIndex, setReg, record, advance, hu]

theorem iterate_reads (ops : Ops α) (input : Nat → Nat → α) (n k t r j : Nat)
    (acc : α) (s : State α) (hr : Reads n k input s) :
    Reads n k input (iterate ops input k t j r acc s) := by
  constructor
  · intro i hi
    simpa [iterate_memory, cell] using hr.1 i hi
  · intro i hi
    simpa [iterate_memory, cell] using hr.2 i hi

def Owned (tr : List Access) : Prop :=
  ∀ a ∈ tr, if a.write then a.location = cell 2 a.thread else a.location.buffer < 2

theorem owned_read (tr : List Access) (h : Owned tr) (t b i : Nat) (e : Epoch) (hb : b<2) :
    Owned (⟨t, cell b i, false, e⟩ :: tr) := by
  intro a ha
  simp only [List.mem_cons] at ha
  rcases ha with rfl | ha
  · exact hb
  · exact h a ha

theorem owned_write (tr : List Access) (h : Owned tr) (t : Nat) (e : Epoch) :
    Owned (⟨t, cell 2 t, true, e⟩ :: tr) := by
  intro a ha
  simp only [List.mem_cons] at ha
  rcases ha with rfl | ha
  · rfl
  · exact h a ha

theorem next_owned (ops : Ops α) (input : Nat → Nat → α) (k t j : Nat)
    (acc : α) (s : State α) (h : Owned s.trace) :
    Owned (next ops input k t j acc s).trace := by
  exact owned_read _ (owned_read _ h t 0 (t*k+j) (s.epochs t) (by decide))
    t 1 j (s.epochs t) (by decide)

theorem iterate_owned (ops : Ops α) (input : Nat → Nat → α) (k t r j : Nat)
    (acc : α) (s : State α) (h : Owned s.trace) :
    Owned (iterate ops input k t j r acc s).trace := by
  induction r generalizing j acc s with
  | zero => exact owned_write _ h t (s.epochs t)
  | succ r ih => exact ih (j+1) _ _ (next_owned ops input k t j acc s h)

theorem initialize_eq (ops : Ops α) (n k w t f : Nat) (s : State α)
    (hp : s.pc t = 0) (ht : t < 2147483648) :
    runLane ops (layout n k) (geometry n w) (program k) t (f+3) s =
      runLane ops (layout n k) (geometry n w) (program k) t f (initialized ops t s) := by
  let s1 := setIndex s t 0 (t : Int) 1
  let s2 := setReg s1 t 0 (ops.literal 0 1) 2
  have hi := bid_index n w t s ht
  have h1 : execute ops (layout n k) (geometry n w) t (.index 0 .bid) s = some s1 :=
    execute_index_of ops (layout n k) (geometry n w) t 0 1 .bid s (t : Int) hi (by omega)
  have hpc1 : s1.pc t = 1 := by simp [s1, setIndex, advance]
  have he : evalExpr ops (layout n k) (geometry n w) t (.lit 0 1) s1 =
      some (ops.literal 0 1, s1) := by rfl
  have h2 : execute ops (layout n k) (geometry n w) t (.assign 0 (.lit 0 1)) s1 =
      some s2 :=
    execute_pure_of ops (layout n k) (geometry n w) t 0 2 (.lit 0 1) s1
      (ops.literal 0 1) he (by omega)
  have hpc2 : s2.pc t = 2 := by simp [s2, setReg, advance]
  have hz : evalIndex (geometry n w) t s2 (.const 0) = some 0 := by rfl
  have h3 : execute ops (layout n k) (geometry n w) t (.index 1 (.const 0)) s2 =
      some (initialized ops t s) :=
    execute_index_of ops (layout n k) (geometry n w) t 1 3 (.const 0) s2 0 hz (by omega)
  rw [LarkPointwise.lane_step ops _ _ _ _ _ _ _ _
    (by simp [parked, program, hp]) (by simp [program, hp]) h1]
  rw [LarkPointwise.lane_step ops _ _ _ _ _ _ _ _
    (by simp [parked, program, hpc1]) (by simp [program, hpc1]) h2]
  rw [LarkPointwise.lane_step ops _ _ _ _ _ _ _ _
    (by simp [parked, program, hpc2]) (by simp [program, hpc2]) h3]

theorem lane_eq (ops : Ops α) (input : Nat → Nat → α) (n k w t : Nat) (s : State α)
    (hp : s.pc t = 0) (hr : Reads n k input s)
    (ht : t < n) (hk : 0 < k) (hb : n*k < 2147483648) :
    runLane ops (layout n k) (geometry n w) (program k) t (4*k+6) s =
      some (finished ops input k t s) := by
  have hn := Nat.mul_le_mul_left n (show 1 ≤ k by omega)
  simp only [Nat.mul_one] at hn
  have htb : t < 2147483648 := by omega
  have hf : 4*k+6 = (4*k+3)+3 := by omega
  rw [hf, initialize_eq ops n k w t (4*k+3) s hp htb]
  apply loop_eq ops n k w t k 0 (initialized ops t s) input (ops.literal 0 1)
  · exact hr
  · simp [initialized, setIndex, setReg, advance]
  · simp [initialized, setIndex, setReg, advance]
  · simp [initialized, setIndex, setReg, advance]
  · simp [initialized, setIndex, advance]
  · exact ht
  · omega
  · exact hb

theorem finished_memory (ops : Ops α) (input : Nat → Nat → α) (k t : Nat)
    (s : State α) (l : Location) :
    (finished ops input k t s).memory l =
      if l = cell 2 t then some (result ops input k t) else s.memory l := by
  exact iterate_memory ops input k t k 0 (ops.literal 0 1) (initialized ops t s) l

theorem finished_pc (ops : Ops α) (input : Nat → Nat → α) (k t : Nat)
    (s : State α) (u : Nat) :
    (finished ops input k t s).pc u = if u=t then 8 else s.pc u := by
  unfold finished
  rw [iterate_pc]
  by_cases hu : u=t <;> simp [initialized, setIndex, setReg, advance, hu]

theorem finished_reads (ops : Ops α) (input : Nat → Nat → α) (n k t : Nat)
    (s : State α) (hr : Reads n k input s) : Reads n k input (finished ops input k t s) :=
  iterate_reads ops input n k t k 0 (ops.literal 0 1) (initialized ops t s) hr

theorem finished_owned (ops : Ops α) (input : Nat → Nat → α) (k t : Nat)
    (s : State α) (h : Owned s.trace) : Owned (finished ops input k t s).trace :=
  iterate_owned ops input k t k 0 (ops.literal 0 1) (initialized ops t s) h

theorem owned_raceFree (g : Geometry) (tr : List Access) (h : Owned tr) :
    raceFree g tr = true := by
  apply List.all_eq_true.mpr
  intro a ha
  apply List.all_eq_true.mpr
  intro b hb
  have hx := h a ha
  have hy := h b hb
  by_cases ht : a.thread = b.thread
  · simp [conflict, ht]
  · cases haw : a.write <;> cases hbw : b.write
    · simp [conflict, haw, hbw]
    · simp only [haw, hbw, Bool.false_eq_true, ↓reduceIte] at hx hy
      have hbeq : (a.location.buffer == 2) = false := by
        simp [show a.location.buffer ≠ 2 by omega]
      simp [conflict, sameLocation, haw, hbw, hy, cell, hbeq]
    · simp only [haw, hbw, Bool.false_eq_true, ↓reduceIte] at hx hy
      have hbeq : (2 == b.location.buffer) = false := by
        simp [show 2 ≠ b.location.buffer by omega]
      simp [conflict, sameLocation, haw, hbw, hx, cell, hbeq]
    · simp only [haw, hbw, Bool.false_eq_true, ↓reduceIte] at hx hy
      have hbeq : (a.thread == b.thread) = false := by simp [ht]
      simp [conflict, sameLocation, haw, hbw, hx, hy, cell, hbeq]

def partialState (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α)
    (n k : Nat) : Nat → State α
  | 0 => initial (layout n k) input outside
  | q+1 => finished ops input k q (partialState ops input outside n k q)

theorem partialState_pc (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (n k q t : Nat) :
    (partialState ops input outside n k q).pc t = if t<q then 8 else 0 := by
  induction q with
  | zero => simp [partialState, initial]
  | succ q ih =>
      simp only [partialState, finished_pc, ih]
      by_cases h : t=q
      · simp [h]
      · by_cases h' : t<q
        · have hh : t<q+1 := by omega
          simp [h, h', hh]
        · have hh : ¬ t<q+1 := by omega
          simp [h, h', hh]

theorem partialState_reads (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (n k q : Nat) :
    Reads n k input (partialState ops input outside n k q) := by
  induction q with
  | zero =>
      constructor
      · intro i hi
        simp [partialState, initial, layout, cell, hi]
      · intro j hj
        simp [partialState, initial, layout, cell, hj]
  | succ q ih => exact finished_reads ops input n k q _ ih

theorem partialState_output (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (n k q t : Nat) (ht : t<q) :
    (partialState ops input outside n k q).memory (cell 2 t) = some (result ops input k t) := by
  induction q with
  | zero => omega
  | succ q ih =>
      simp only [partialState, finished_memory, cell, Location.mk.injEq,
        and_self_left, true_and]
      by_cases h : t=q
      · simp [h]
      · simpa [h, cell] using ih (by omega)

theorem partialState_owned (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (n k q : Nat) :
    Owned (partialState ops input outside n k q).trace := by
  induction q with
  | zero => simp [Owned, partialState, initial]
  | succ q ih => exact finished_owned ops input k q _ ih

def fuel (k : Nat) : Fuel := ⟨4*k+6, 1, 1, 1⟩
def spec (ops : Ops α) (n k : Nat) (input : Nat → Nat → α) : List α :=
  (List.range n).map (fun t => result ops input k t)

theorem converged_done (k : Nat) (s : State α) (ts : List Nat)
    (hne : ts ≠ []) (hp : ∀ t ∈ ts, s.pc t = 8) :
    converged (program k) ts s = some .halt := by
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

theorem block_eq (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α)
    (n k w t : Nat) (ht : t<n) (hk : 0<k) (hb : n*k<2147483648) (hw : 0<w) :
    runBlock ops (layout n k) (geometry n w) (fuel k) (program k) t (fuel k).block
      (partialState ops input outside n k t) =
      some (partialState ops input outside n k (t+1)) := by
  have hl := lane_eq ops input n k w t (partialState ops input outside n k t)
    (by simp [partialState_pc]) (partialState_reads ops input outside n k t) ht hk hb
  change runLane ops (layout n k) (geometry n w) (program k) t (fuel k).lane
    (partialState ops input outside n k t) =
    some (partialState ops input outside n k (t+1)) at hl
  have hd : (1+w-1)/w = 1 := by
    have he : 1+w-1=w := by omega
    rw [he, Nat.div_self (by omega)]
  have hwne : w ≠ 0 := by omega
  have hwarp : warpThreads (geometry n w) t 0 = [t] := by
    simp [warpThreads, geometry, LarkPointwise.geometry, List.range_succ, hwne]
  have hblock : blockThreads (geometry n w) t = [t] := by
    simp [blockThreads, geometry, LarkPointwise.geometry, List.range_succ]
  have hc : converged (program k) [t] (partialState ops input outside n k (t+1)) =
      some .halt := by
    apply converged_done
    · simp
    · intro u hu
      simp only [List.mem_singleton] at hu
      subst u
      simp [partialState_pc]
  have hr : runWarp ops (layout n k) (geometry n w) (fuel k) (program k) [t] (fuel k).warp
      (partialState ops input outside n k t) =
      some (partialState ops input outside n k (t+1)) := by
    change runWarp ops (layout n k) (geometry n w) (fuel k) (program k) [t] 1 _ = _
    rw [runWarp]
    simp only [List.foldlM_cons, List.foldlM_nil, bind, pure, Option.bind, hl, hc]
    rfl
  have hws : List.range (((geometry n w).block + (geometry n w).warp - 1) /
      (geometry n w).warp) = [0] := by
    simp [geometry, LarkPointwise.geometry, hd, List.range_succ]
  change runBlock ops (layout n k) (geometry n w) (fuel k) (program k) t 1 _ = _
  rw [runBlock, hws]
  simp only [List.foldlM_cons, List.foldlM_nil, hwarp, hr, bind, pure, Option.bind,
    hblock, hc]
  rfl

theorem blocks_eq (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α)
    (n k w q : Nat) (hq : q≤n) (hk : 0<k) (hb : n*k<2147483648) (hw : 0<w) :
    (List.range q).foldlM (fun s t =>
      runBlock ops (layout n k) (geometry n w) (fuel k) (program k) t (fuel k).block s)
      (initial (layout n k) input outside) = some (partialState ops input outside n k q) := by
  induction q with
  | zero => rfl
  | succ q ih =>
      rw [List.range_succ, List.foldlM_append, ih (by omega)]
      simp [block_eq ops input outside n k w q (by omega) hk hb hw]

theorem launch_eq (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α)
    (n k w : Nat) (hn : 0<n) (hk : 0<k) (hb : n*k<2147483648) (hw : 0<w) :
    runLaunch ops (layout n k) (geometry n w) (fuel k) (program k)
      (initial (layout n k) input outside) = some (partialState ops input outside n k n) := by
  have hfold := blocks_eq ops input outside n k w n (by omega) hk hb hw
  have hne : List.range n ≠ [] := by
    intro he
    have hh := congrArg List.length he
    simp at hh
    omega
  have hc := converged_done k (partialState ops input outside n k n) (List.range n) hne
    (by intro t ht; simp [partialState_pc, List.mem_range.mp ht])
  simp only [runLaunch, geometry, LarkPointwise.geometry, show n ≠ 0 by omega,
    show w ≠ 0 by omega, or_false, false_or, reduceCtorEq, ↓reduceIte, fuel, runGrid]
  change ((List.range n).foldlM (fun s t =>
    runBlock ops (layout n k) (geometry n w) (fuel k) (program k) t (fuel k).block s)
      (initial (layout n k) input outside)).bind _ = _
  rw [hfold]
  simp only [bind, pure, Option.bind, Nat.mul_one, hc]
  rfl

theorem extract_eq (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α)
    (n k : Nat) :
    extract (layout n k) (partialState ops input outside n k n) = some (spec ops n k input) := by
  simp only [extract, layout, List.zipIdx_cons, List.zipIdx_nil, List.flatMap_cons,
    List.flatMap_nil, List.nil_append]
  simp only [List.map_cons, List.map_nil, show Role.input ≠ Role.output by decide,
    ↓reduceIte, List.nil_append, List.append_nil]
  change (((List.range n).map (fun i => (2, i))).mapM
    (fun bi => (partialState ops input outside n k n).memory (cell bi.1 bi.2)) :
      Option (List α)) = _
  rw [LarkPointwise.mapM_map]
  exact LarkPointwise.mapM_some (List.range n) _ _ (by
    intro i hi
    exact partialState_output ops input outside n k n i (List.mem_range.mp hi))

/-- Whole launch of the real scalar machine, not an assumed loop summary. -/
theorem correct (ops : Ops α) (n k w : Nat)
    (hn : 0<n) (hk : 0<k) (hb : n*k<2147483648) (hw : 0<w) :
    Correct ops (layout n k) (geometry n w) (fuel k) (program k) (spec ops n k) := by
  intro input outside
  refine ⟨partialState ops input outside n k n,
    launch_eq ops input outside n k w hn hk hb hw, ?_, extract_eq ops input outside n k⟩
  exact owned_raceFree (geometry n w) _ (partialState_owned ops input outside n k n)

/-- Tensor-level left-fold dot product, independent of PCs and machine state. -/
def dotSpec (ops : Ops α) (input : Nat → Nat → α) (k t : Nat) : α :=
  (List.range k).foldl (fun acc j => ops.add acc (term ops input k t j)) (ops.literal 0 1)

def matrixSpec (ops : Ops α) (n k : Nat) (input : Nat → Nat → α) : List α :=
  (List.range n).map (fun t => ops.toHalf (dotSpec ops input k t))

theorem folded_eq_list (ops : Ops α) (input : Nat → Nat → α) (k t r j : Nat) (acc : α) :
    folded ops input k t j r acc =
      (List.range' j r).foldl (fun acc z => ops.add acc (term ops input k t z)) acc := by
  induction r generalizing j acc with
  | zero => rfl
  | succ r ih =>
      rw [folded, List.range'_succ, List.foldl_cons]
      exact ih (j+1) _

theorem result_eq_dot (ops : Ops α) (input : Nat → Nat → α) (k t : Nat) :
    result ops input k t = ops.toHalf (dotSpec ops input k t) := by
  unfold result dotSpec
  rw [folded_eq_list, List.range_eq_range']

theorem spec_eq_matrixSpec (ops : Ops α) (n k : Nat) (input : Nat → Nat → α) :
    spec ops n k input = matrixSpec ops n k input := by
  simp only [spec, matrixSpec, result_eq_dot]

theorem matrix_correct (ops : Ops α) (n k w : Nat)
    (hn : 0<n) (hk : 0<k) (hb : n*k<2147483648) (hw : 0<w) :
    Correct ops (layout n k) (geometry n w) (fuel k) (program k) (matrixSpec ops n k) := by
  have hs : spec ops n k = matrixSpec ops n k := by
    funext input
    exact spec_eq_matrixSpec ops n k input
  rw [← hs]
  exact correct ops n k w hn hk hb hw

#print axioms loop_step
#print axioms loop_eq
#print axioms lane_eq
#print axioms correct
#print axioms matrix_correct

end LarkReduction
