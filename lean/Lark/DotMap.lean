import Lark.Matrix

/-!
Induction for the actual scalar machine's counted dot-product loop and grid.
Profiles supply only input address functions, bounds, and primitive index-evaluation
proofs. No assumed loop summary, execution equality or correctness field is used.
The machine model is unchanged. The conclusion is its existing Correct predicate,
including completion, race freedom and every output, for all inputs/outside memory.
-/
namespace LarkDotMap
open LarkNonlinear
open LarkReduction
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

structure Profile extends LarkDot.Profile where
  aHalf : Bool
  bHalf : Bool
  post : LarkPointwise.Scalar
  validPost : LarkPointwise.Valid post

def convert (half : Bool) (ops : Ops α) (x : α) : α := if half then ops.fromHalf x else x
def loadExpr (half : Bool) (b : Nat) (ix : Index) : Expr :=
  if half then .un .fromHalf (.load .global b ix) else .load .global b ix

def layout (p : Profile) : Layout :=
  ⟨[⟨.input, p.aSize⟩, ⟨.input, p.bSize⟩, ⟨.output, p.n⟩], [], []⟩
def geometry (p : Profile) (w : Nat) : Geometry := LarkPointwise.geometry p.n w
def cell (b i : Nat) : Location := ⟨.global, 0, b, i⟩
def program (p : Profile) : List Instr :=
  [.index 0 .bid,
   .assign 0 (.lit 0 1),
   .index 1 (.const 0),
   .branch (.lt (.ivar 1) (.const (p.k : Int))) 7,
   .assign 0 (.bin .add (.reg 0) (.bin .mul
     (loadExpr p.aHalf 0 p.aIndex)
     (loadExpr p.bHalf 1 p.bIndex))),
   .index 1 (.add (.ivar 1) (.const 1)),
   .jump 3,
   .store .global 2 (.ivar 0) (LarkPointwise.lower p.post),
   .halt]

def Reads (p : Profile) (input : Nat → Nat → α) (s : State α) : Prop :=
  (∀ i, i < p.aSize → s.memory (cell 0 i) = some (input 0 i)) ∧
  (∀ j, j < p.bSize → s.memory (cell 1 j) = some (input 1 j))

def setIndex (s : State α) (t r : Nat) (v : Int) (pc : Nat) : State α :=
  advance { s with indices := fun u q => if u = t ∧ q = r then some v else s.indices u q } t pc
def setReg (s : State α) (t r : Nat) (v : α) (pc : Nat) : State α :=
  advance { s with regs := fun u q => if u = t ∧ q = r then some v else s.regs u q } t pc

def term (ops : Ops α) (input : Nat → Nat → α) (p : Profile) (t j : Nat) : α :=
  ops.mul (convert p.aHalf ops (input 0 (p.aAddress t j))) (convert p.bHalf ops (input 1 (p.bAddress t j)))

def next (ops : Ops α) (input : Nat → Nat → α) (p : Profile) (t j : Nat) (acc : α)
    (s : State α) : State α :=
  let s := advance s t 4
  let s := record (record s t (cell 0 (p.aAddress t j)) false) t (cell 1 (p.bAddress t j)) false
  let s := setReg s t 0 (ops.add acc (term ops input p t j)) 5
  let s := setIndex s t 1 ((j+1 : Nat) : Int) 6
  advance s t 3

def stored (ops : Ops α) (p : Profile) (t : Nat) (acc : α) (s : State α) : State α :=
  advance { record s t (cell 2 t) true with
    memory := fun l => if l = cell 2 t then some (LarkPointwise.value ops acc p.post) else s.memory l } t 8

def iterate (ops : Ops α) (input : Nat → Nat → α) (p : Profile) (t : Nat) :
    Nat → Nat → α → State α → State α
  | _, 0, acc, s => stored ops p t acc (advance s t 7)
  | j, r+1, acc, s => iterate ops input p t (j+1) r
      (ops.add acc (term ops input p t j)) (next ops input p t j acc s)

def folded (ops : Ops α) (input : Nat → Nat → α) (p : Profile) (t : Nat) : Nat → Nat → α → α
  | _, 0, acc => acc
  | j, r+1, acc => folded ops input p t (j+1) r (ops.add acc (term ops input p t j))

def initialized (ops : Ops α) (t : Nat) (s : State α) : State α :=
  setIndex (setReg (setIndex s t 0 (t : Int) 1) t 0 (ops.literal 0 1) 2) t 1 0 3

def finished (ops : Ops α) (input : Nat → Nat → α) (p : Profile) (t : Nat) (s : State α) : State α :=
  iterate ops input p t 0 p.k (ops.literal 0 1) (initialized ops t s)

def result (ops : Ops α) (input : Nat → Nat → α) (p : Profile) (t : Nat) : α :=
  LarkPointwise.value ops (folded ops input p t 0 p.k (ops.literal 0 1)) p.post

theorem matrix_location (p : Profile) (t i : Nat) (g : Geometry) (hi : i < p.aSize) :
    location (layout p) g t .global 0 (i : Int) false = some (cell 0 i) := by
  have hneg : ¬ (i : Int) < 0 := by omega
  simp [location, layout, cell, hneg, hi]

theorem load_matrix (ops : Ops α) (p : Profile) (w t j : Nat) (s : State α)
    (input : Nat → Nat → α) (hr : Reads p input s)
    (hi : s.indices t 0 = some (t : Int)) (hij : s.indices t 1 = some (j : Int))
    (ht : t < p.n) (hj : j < p.k) (_hb : p.n < 2147483648 ∧ p.k < 2147483648) :
    evalExpr ops (layout p) (geometry p w) t
      (loadExpr p.aHalf 0 p.aIndex) s =
      some (convert p.aHalf ops (input 0 (p.aAddress t j)), record s t (cell 0 (p.aAddress t j)) false) := by
  have ha := p.aBound t j ht hj
  have hix := p.aEval α (geometry p w) t j s hi hij ht hj
  have hl := matrix_location p t (p.aAddress t j) (geometry p w) ha
  cases hh : p.aHalf <;> simp [loadExpr,hh,convert,evalExpr,hix,hl,hr.1 _ ha,applyUnary]

theorem load_vector (ops : Ops α) (p : Profile) (w t j : Nat) (s : State α)
    (input : Nat → Nat → α) (hr : Reads p input s)
    (hi : s.indices t 0 = some (t : Int)) (hij : s.indices t 1 = some (j : Int))
    (ht : t < p.n) (hj : j < p.k) :
    evalExpr ops (layout p) (geometry p w) t
      (loadExpr p.bHalf 1 p.bIndex) s =
      some (convert p.bHalf ops (input 1 (p.bAddress t j)), record s t (cell 1 (p.bAddress t j)) false) := by
  have ha := p.bBound t j ht hj
  have hneg : ¬ ((p.bAddress t j : Nat) : Int) < 0 := by omega
  have hix := p.bEval α (geometry p w) t j s hi hij ht hj
  have hl : location (layout p) (geometry p w) t .global 1
      ((p.bAddress t j : Nat) : Int) false = some (cell 1 (p.bAddress t j)) := by
    simp [location, layout, cell, hneg, ha]
  cases hh : p.bHalf <;> simp [loadExpr,hh,convert,evalExpr,hix,hl,hr.2 _ ha,applyUnary]

theorem reads_advance (p : Profile) (t pc : Nat) (input : Nat → Nat → α) (s : State α)
    (h : Reads p input s) : Reads p input (advance s t pc) := h

theorem reads_record (p : Profile) (t : Nat) (input : Nat → Nat → α) (s : State α)
    (l : Location) (write : Bool) (h : Reads p input s) :
    Reads p input (record s t l write) := h

theorem eval_accumulate (ops : Ops α) (p : Profile) (w t j : Nat) (s : State α)
    (input : Nat → Nat → α) (acc : α) (hr : Reads p input s)
    (hi : s.indices t 0 = some (t : Int)) (hij : s.indices t 1 = some (j : Int))
    (hacc : s.regs t 0 = some acc) (ht : t < p.n) (hj : j < p.k)
    (hb : p.n < 2147483648 ∧ p.k < 2147483648) :
    evalExpr ops (layout p) (geometry p w) t
      (.bin .add (.reg 0) (.bin .mul
        (loadExpr p.aHalf 0 p.aIndex)
        (loadExpr p.bHalf 1 p.bIndex))) s =
      some (ops.add acc (term ops input p t j),
        record (record s t (cell 0 (p.aAddress t j)) false) t (cell 1 (p.bAddress t j)) false) := by
  have ha := load_matrix ops p w t j s input hr hi hij ht hj hb
  have hbs := load_vector ops p w t j (record s t (cell 0 (p.aAddress t j)) false)
    input hr hi hij ht hj
  have hm := eval_bin_of ops (layout p) (geometry p w) t .mul _ _ _ _ _ _ _ ha hbs
  have hreg : evalExpr ops (layout p) (geometry p w) t (.reg 0) s = some (acc, s) := by
    simp [evalExpr, hacc]
  exact eval_bin_of ops (layout p) (geometry p w) t .add _ _ _ _ _ _ _ hreg hm

theorem branch_true (ops : Ops α) (p : Profile) (w t j : Nat) (s : State α)
    (hp : s.pc t = 3) (hij : s.indices t 1 = some (j : Int))
    (hj : j < p.k) (hk : p.k < 2147483648) :
    execute ops (layout p) (geometry p w) t
      (.branch (.lt (.ivar 1) (.const (p.k : Int))) 7) s = some (advance s t 4) := by
  have he := predicate_lt_of (geometry p w) t s (.ivar 1) (.const (p.k : Int))
    (j : Int) (p.k : Int) hij (int32_cast p.k hk) (by omega)
  simp only [execute, he, bind, pure, Option.bind, hp]
  rfl

theorem execute_accumulate (ops : Ops α) (p : Profile) (w t j : Nat) (s : State α)
    (input : Nat → Nat → α) (acc : α) (hr : Reads p input s)
    (hi : s.indices t 0 = some (t : Int)) (hij : s.indices t 1 = some (j : Int))
    (hacc : s.regs t 0 = some acc) (hp : s.pc t = 4)
    (ht : t < p.n) (hj : j < p.k) (hb : p.n < 2147483648 ∧ p.k < 2147483648) :
    execute ops (layout p) (geometry p w) t
      (.assign 0 (.bin .add (.reg 0) (.bin .mul
        (loadExpr p.aHalf 0 p.aIndex)
        (loadExpr p.bHalf 1 p.bIndex)))) s =
      some (setReg (record (record s t (cell 0 (p.aAddress t j)) false) t (cell 1 (p.bAddress t j)) false)
        t 0 (ops.add acc (term ops input p t j)) 5) := by
  have he := eval_accumulate ops p w t j s input acc hr hi hij hacc ht hj hb
  simp only [execute, he, bind, pure, Option.bind, hp]
  rfl

theorem execute_counter (ops : Ops α) (p : Profile) (w t j : Nat) (s : State α)
    (hij : s.indices t 1 = some (j : Int)) (hp : s.pc t = 5)
    (hj : j+1 < 2147483648) :
    execute ops (layout p) (geometry p w) t
      (.index 1 (.add (.ivar 1) (.const 1))) s =
      some (setIndex s t 1 ((j+1 : Nat) : Int) 6) := by
  have hi : evalIndex (geometry p w) t s (.add (.ivar 1) (.const 1)) =
      some ((j+1 : Nat) : Int) :=
    eval_add_of (geometry p w) t s _ _ (j : Int) 1 ((j+1 : Nat) : Int) hij
      (by rfl) (Eq.trans (congrArg int32 (Int.natCast_add j 1).symm) (int32_cast (j+1) hj))
  simp only [execute, hi, hp, bind, pure, Option.bind]
  rfl

theorem loop_step (ops : Ops α) (p : Profile) (w t j f : Nat) (s : State α)
    (input : Nat → Nat → α) (acc : α) (hr : Reads p input s)
    (hi : s.indices t 0 = some (t : Int)) (hij : s.indices t 1 = some (j : Int))
    (hacc : s.regs t 0 = some acc) (hp : s.pc t = 3)
    (ht : t < p.n) (hj : j < p.k) (hb : p.n < 2147483648 ∧ p.k < 2147483648) :
    runLane ops (layout p) (geometry p w) (program p) t (f+4) s =
      runLane ops (layout p) (geometry p w) (program p) t f
        (next ops input p t j acc s) := by
  let s1 := advance s t 4
  let s2 := setReg (record (record s1 t (cell 0 (p.aAddress t j)) false) t (cell 1 (p.bAddress t j)) false)
    t 0 (ops.add acc (term ops input p t j)) 5
  let s3 := setIndex s2 t 1 ((j+1 : Nat) : Int) 6
  have hk := hb.2
  have h1 := branch_true ops p w t j s hp hij hj hk
  have h2 := execute_accumulate ops p w t j s1 input acc hr hi hij hacc
    (by simp [s1, advance]) ht hj hb
  change execute ops (layout p) (geometry p w) t _ s1 = some s2 at h2
  have h3 := execute_counter ops p w t j s2
    (by simpa [s2, setReg, record, s1, advance] using hij)
    (by simp [s2, setReg, advance]) (by omega)
  change execute ops (layout p) (geometry p w) t _ s2 = some s3 at h3
  have h4 : execute ops (layout p) (geometry p w) t (.jump 3) s3 =
      some (next ops input p t j acc s) := by rfl
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

theorem execute_store (ops : Ops α) (p : Profile) (w t : Nat) (s : State α) (acc : α)
    (hi : s.indices t 0 = some (t : Int)) (hacc : s.regs t 0 = some acc)
    (hp : s.pc t = 7) (ht : t < p.n) :
    execute ops (layout p) (geometry p w) t
      (.store .global 2 (.ivar 0) (LarkPointwise.lower p.post)) s = some (stored ops p t acc s) := by
  have hneg : ¬ (t : Int) < 0 := by omega
  have hrole : (Role.output == Role.input) = false := by decide
  have hl : location (layout p) (geometry p w) t .global 2 (t : Int) true =
      some (cell 2 t) := by simp [location, layout, cell, hneg, ht, hrole]
  have he : evalExpr ops (layout p) (geometry p w) t (LarkPointwise.lower p.post) s =
      some (LarkPointwise.value ops acc p.post,s) :=
    LarkPointwise.eval_lower ops _ _ t s acc p.post p.validPost hacc

  simp only [execute, evalIndex, hi, bind, pure, Option.bind, hl, he, hp]
  rfl

theorem loop_done (ops : Ops α) (p : Profile) (w t : Nat) (s : State α) (acc : α)
    (hi : s.indices t 0 = some (t : Int)) (hij : s.indices t 1 = some (p.k : Int))
    (hacc : s.regs t 0 = some acc) (hp : s.pc t = 3)
    (ht : t < p.n) (hk : p.k < 2147483648) :
    runLane ops (layout p) (geometry p w) (program p) t 3 s =
      some (stored ops p t acc (advance s t 7)) := by
  have hg := predicate_nlt_of (geometry p w) t s (.ivar 1) (.const (p.k : Int))
    (p.k : Int) (p.k : Int) hij (int32_cast p.k hk) (by omega)
  have h1 : execute ops (layout p) (geometry p w) t
      (.branch (.lt (.ivar 1) (.const (p.k : Int))) 7) s = some (advance s t 7) := by
    simp only [execute, hg, bind, pure, Option.bind]
    rfl
  have h2 := execute_store ops p w t (advance s t 7) acc hi hacc
    (by simp [advance]) ht
  rw [LarkPointwise.lane_step ops _ _ _ _ _ _ _ _
    (by simp [parked, program, hp]) (by simp [program, hp]) h1]
  rw [LarkPointwise.lane_step ops _ _ _ _ _ _ _ _
    (by simp [parked, program, advance]) (by simp [program, advance]) h2]
  simp [runLane, parked, program, stored, advance]

theorem loop_eq (ops : Ops α) (p : Profile) (w t r : Nat) (j : Nat) (s : State α)
    (input : Nat → Nat → α) (acc : α) (hr : Reads p input s)
    (hi : s.indices t 0 = some (t : Int)) (hij : s.indices t 1 = some (j : Int))
    (hacc : s.regs t 0 = some acc) (hp : s.pc t = 3)
    (ht : t < p.n) (hcount : j+r=p.k) (hb : p.n < 2147483648 ∧ p.k < 2147483648) :
    runLane ops (layout p) (geometry p w) (program p) t (4*r+3) s =
      some (iterate ops input p t j r acc s) := by
  induction r generalizing j acc s with
  | zero =>
      have hj : j=p.k := by omega
      subst j
      simpa [iterate] using loop_done ops p w t s acc hi hij hacc hp ht
        (hb.2)
  | succ r ih =>
      have hlt : j<p.k := by omega
      have hf : 4*(r+1)+3 = (4*r+3)+4 := by omega
      rw [hf, loop_step ops p w t j (4*r+3) s input acc hr hi hij hacc hp ht hlt hb]
      change _ = some (iterate ops input p t (j+1) r _ _)
      apply ih
      · exact hr
      · simpa [next, setIndex, setReg, advance, record] using hi
      · simp [next, setIndex, setReg, advance, record]
      · simp [next, setIndex, setReg, advance, record]
      · simp [next, advance]
      · omega

theorem iterate_memory (ops : Ops α) (input : Nat → Nat → α) (p : Profile) (t r j : Nat)
    (acc : α) (s : State α) (l : Location) :
    (iterate ops input p t j r acc s).memory l =
      if l = cell 2 t then some (LarkPointwise.value ops (folded ops input p t j r acc) p.post) else s.memory l := by
  induction r generalizing j acc s with
  | zero => rfl
  | succ r ih =>
      change (iterate ops input p t (j+1) r _ _).memory l = _
      exact ih (j+1) (ops.add acc (term ops input p t j)) (next ops input p t j acc s)

theorem iterate_pc (ops : Ops α) (input : Nat → Nat → α) (p : Profile) (t r j : Nat)
    (acc : α) (s : State α) (u : Nat) :
    (iterate ops input p t j r acc s).pc u = if u=t then 8 else s.pc u := by
  induction r generalizing j acc s with
  | zero =>
      by_cases hu : u=t <;> simp [iterate, stored, advance, record, hu]
  | succ r ih =>
      change (iterate ops input p t (j+1) r _ _).pc u = _
      rw [ih]
      by_cases hu : u=t <;>
        simp [next, setIndex, setReg, record, advance, hu]

theorem iterate_reads (ops : Ops α) (input : Nat → Nat → α) (p : Profile) (t r j : Nat)
    (acc : α) (s : State α) (hr : Reads p input s) :
    Reads p input (iterate ops input p t j r acc s) := by
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

theorem next_owned (ops : Ops α) (input : Nat → Nat → α) (p : Profile) (t j : Nat)
    (acc : α) (s : State α) (h : Owned s.trace) :
    Owned (next ops input p t j acc s).trace := by
  exact owned_read _ (owned_read _ h t 0 (p.aAddress t j) (s.epochs t) (by decide))
    t 1 (p.bAddress t j) (s.epochs t) (by decide)

theorem iterate_owned (ops : Ops α) (input : Nat → Nat → α) (p : Profile) (t r j : Nat)
    (acc : α) (s : State α) (h : Owned s.trace) :
    Owned (iterate ops input p t j r acc s).trace := by
  induction r generalizing j acc s with
  | zero => exact owned_write _ h t (s.epochs t)
  | succ r ih => exact ih (j+1) _ _ (next_owned ops input p t j acc s h)

theorem initialize_eq (ops : Ops α) (p : Profile) (w t f : Nat) (s : State α)
    (hp : s.pc t = 0) (ht : t < 2147483648) :
    runLane ops (layout p) (geometry p w) (program p) t (f+3) s =
      runLane ops (layout p) (geometry p w) (program p) t f (initialized ops t s) := by
  let s1 := setIndex s t 0 (t : Int) 1
  let s2 := setReg s1 t 0 (ops.literal 0 1) 2
  have hi := bid_index p.n w t s ht
  have h1 : execute ops (layout p) (geometry p w) t (.index 0 .bid) s = some s1 :=
    execute_index_of ops (layout p) (geometry p w) t 0 1 .bid s (t : Int) hi (by omega)
  have hpc1 : s1.pc t = 1 := by simp [s1, setIndex, advance]
  have he : evalExpr ops (layout p) (geometry p w) t (.lit 0 1) s1 =
      some (ops.literal 0 1, s1) := by rfl
  have h2 : execute ops (layout p) (geometry p w) t (.assign 0 (.lit 0 1)) s1 =
      some s2 :=
    execute_pure_of ops (layout p) (geometry p w) t 0 2 (.lit 0 1) s1
      (ops.literal 0 1) he (by omega)
  have hpc2 : s2.pc t = 2 := by simp [s2, setReg, advance]
  have hz : evalIndex (geometry p w) t s2 (.const 0) = some 0 := by rfl
  have h3 : execute ops (layout p) (geometry p w) t (.index 1 (.const 0)) s2 =
      some (initialized ops t s) :=
    execute_index_of ops (layout p) (geometry p w) t 1 3 (.const 0) s2 0 hz (by omega)
  rw [LarkPointwise.lane_step ops _ _ _ _ _ _ _ _
    (by simp [parked, program, hp]) (by simp [program, hp]) h1]
  rw [LarkPointwise.lane_step ops _ _ _ _ _ _ _ _
    (by simp [parked, program, hpc1]) (by simp [program, hpc1]) h2]
  rw [LarkPointwise.lane_step ops _ _ _ _ _ _ _ _
    (by simp [parked, program, hpc2]) (by simp [program, hpc2]) h3]

theorem lane_eq (ops : Ops α) (input : Nat → Nat → α) (p : Profile) (w t : Nat) (s : State α)
    (hp : s.pc t = 0) (hr : Reads p input s)
    (ht : t < p.n) (_hk : 0 < p.k) (hb : p.n < 2147483648 ∧ p.k < 2147483648) :
    runLane ops (layout p) (geometry p w) (program p) t (4*p.k+6) s =
      some (finished ops input p t s) := by
  have htb : t < 2147483648 := by omega
  have hf : 4*p.k+6 = (4*p.k+3)+3 := by omega
  rw [hf, initialize_eq ops p w t (4*p.k+3) s hp htb]
  apply loop_eq ops p w t p.k 0 (initialized ops t s) input (ops.literal 0 1)
  · exact hr
  · simp [initialized, setIndex, setReg, advance]
  · simp [initialized, setIndex, setReg, advance]
  · simp [initialized, setIndex, setReg, advance]
  · simp [initialized, setIndex, advance]
  · exact ht
  · omega
  · exact hb

theorem finished_memory (ops : Ops α) (input : Nat → Nat → α) (p : Profile) (t : Nat)
    (s : State α) (l : Location) :
    (finished ops input p t s).memory l =
      if l = cell 2 t then some (result ops input p t) else s.memory l := by
  exact iterate_memory ops input p t p.k 0 (ops.literal 0 1) (initialized ops t s) l

theorem finished_pc (ops : Ops α) (input : Nat → Nat → α) (p : Profile) (t : Nat)
    (s : State α) (u : Nat) :
    (finished ops input p t s).pc u = if u=t then 8 else s.pc u := by
  unfold finished
  rw [iterate_pc]
  by_cases hu : u=t <;> simp [initialized, setIndex, setReg, advance, hu]

theorem finished_reads (ops : Ops α) (input : Nat → Nat → α) (p : Profile) (t : Nat)
    (s : State α) (hr : Reads p input s) : Reads p input (finished ops input p t s) :=
  iterate_reads ops input p t p.k 0 (ops.literal 0 1) (initialized ops t s) hr

theorem finished_owned (ops : Ops α) (input : Nat → Nat → α) (p : Profile) (t : Nat)
    (s : State α) (h : Owned s.trace) : Owned (finished ops input p t s).trace :=
  iterate_owned ops input p t p.k 0 (ops.literal 0 1) (initialized ops t s) h

def partialState (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α)
    (p : Profile) : Nat → State α
  | 0 => initial (layout p) input outside
  | q+1 => finished ops input p q (partialState ops input outside p q)

theorem partialState_pc (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (p : Profile) (q t : Nat) :
    (partialState ops input outside p q).pc t = if t<q then 8 else 0 := by
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
    (outside : Location → Option α) (p : Profile) (q : Nat) :
    Reads p input (partialState ops input outside p q) := by
  induction q with
  | zero =>
      constructor
      · intro i hi
        simp [partialState, initial, layout, cell, hi]
      · intro j hj
        simp [partialState, initial, layout, cell, hj]
  | succ q ih => exact finished_reads ops input p q _ ih

theorem partialState_output (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (p : Profile) (q t : Nat) (ht : t<q) :
    (partialState ops input outside p q).memory (cell 2 t) = some (result ops input p t) := by
  induction q with
  | zero => omega
  | succ q ih =>
      simp only [partialState, finished_memory, cell, Location.mk.injEq,
        and_self_left, true_and]
      by_cases h : t=q
      · simp [h]
      · simpa [h, cell] using ih (by omega)

theorem partialState_owned (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (p : Profile) (q : Nat) :
    Owned (partialState ops input outside p q).trace := by
  induction q with
  | zero => simp [Owned, partialState, initial]
  | succ q ih => exact finished_owned ops input p q _ ih

def fuel (p : Profile) : Fuel := ⟨4*p.k+6, 1, 1, 1⟩
def spec (ops : Ops α) (p : Profile) (input : Nat → Nat → α) : List α :=
  (List.range p.n).map (fun t => result ops input p t)

theorem converged_done (p : Profile) (s : State α) (ts : List Nat)
    (hne : ts ≠ []) (hp : ∀ t ∈ ts, s.pc t = 8) :
    converged (program p) ts s = some .halt := by
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
    (p : Profile) (w t : Nat) (ht : t<p.n) (hk : 0<p.k) (hb : p.n < 2147483648 ∧ p.k < 2147483648) (hw : 0<w) :
    runBlock ops (layout p) (geometry p w) (fuel p) (program p) t (fuel p).block
      (partialState ops input outside p t) =
      some (partialState ops input outside p (t+1)) := by
  have hl := lane_eq ops input p w t (partialState ops input outside p t)
    (by simp [partialState_pc]) (partialState_reads ops input outside p t) ht hk hb
  change runLane ops (layout p) (geometry p w) (program p) t (fuel p).lane
    (partialState ops input outside p t) =
    some (partialState ops input outside p (t+1)) at hl
  have hd : (1+w-1)/w = 1 := by
    have he : 1+w-1=w := by omega
    rw [he, Nat.div_self (by omega)]
  have hwne : w ≠ 0 := by omega
  have hwarp : warpThreads (geometry p w) t 0 = [t] := by
    simp [warpThreads, geometry, LarkPointwise.geometry, List.range_succ, hwne]
  have hblock : blockThreads (geometry p w) t = [t] := by
    simp [blockThreads, geometry, LarkPointwise.geometry, List.range_succ]
  have hc : converged (program p) [t] (partialState ops input outside p (t+1)) =
      some .halt := by
    apply converged_done
    · simp
    · intro u hu
      simp only [List.mem_singleton] at hu
      subst u
      simp [partialState_pc]
  have hr : runWarp ops (layout p) (geometry p w) (fuel p) (program p) [t] (fuel p).warp
      (partialState ops input outside p t) =
      some (partialState ops input outside p (t+1)) := by
    change runWarp ops (layout p) (geometry p w) (fuel p) (program p) [t] 1 _ = _
    rw [runWarp]
    simp only [List.foldlM_cons, List.foldlM_nil, bind, pure, Option.bind, hl, hc]
    rfl
  have hws : List.range (((geometry p w).block + (geometry p w).warp - 1) /
      (geometry p w).warp) = [0] := by
    simp [geometry, LarkPointwise.geometry, hd, List.range_succ]
  change runBlock ops (layout p) (geometry p w) (fuel p) (program p) t 1 _ = _
  rw [runBlock, hws]
  simp only [List.foldlM_cons, List.foldlM_nil, hwarp, hr, bind, pure, Option.bind,
    hblock, hc]
  rfl

theorem blocks_eq (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α)
    (p : Profile) (w q : Nat) (hq : q≤p.n) (hk : 0<p.k) (hb : p.n < 2147483648 ∧ p.k < 2147483648) (hw : 0<w) :
    (List.range q).foldlM (fun s t =>
      runBlock ops (layout p) (geometry p w) (fuel p) (program p) t (fuel p).block s)
      (initial (layout p) input outside) = some (partialState ops input outside p q) := by
  induction q with
  | zero => rfl
  | succ q ih =>
      rw [List.range_succ, List.foldlM_append, ih (by omega)]
      simp [block_eq ops input outside p w q (by omega) hk hb hw]

theorem launch_eq (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α)
    (p : Profile) (w : Nat) (hn : 0<p.n) (hk : 0<p.k) (hb : p.n < 2147483648 ∧ p.k < 2147483648) (hw : 0<w) :
    runLaunch ops (layout p) (geometry p w) (fuel p) (program p)
      (initial (layout p) input outside) = some (partialState ops input outside p p.n) := by
  have hfold := blocks_eq ops input outside p w p.n (by omega) hk hb hw
  have hne : List.range p.n ≠ [] := by
    intro he
    have hh := congrArg List.length he
    simp at hh
    omega
  have hc := converged_done p (partialState ops input outside p p.n) (List.range p.n) hne
    (by intro t ht; simp [partialState_pc, List.mem_range.mp ht])
  simp only [runLaunch, geometry, LarkPointwise.geometry, show p.n ≠ 0 by omega,
    show w ≠ 0 by omega, or_false, false_or, reduceCtorEq, ↓reduceIte, fuel, runGrid]
  change ((List.range p.n).foldlM (fun s t =>
    runBlock ops (layout p) (geometry p w) (fuel p) (program p) t (fuel p).block s)
      (initial (layout p) input outside)).bind _ = _
  rw [hfold]
  simp only [bind, pure, Option.bind, Nat.mul_one, hc]
  rfl

theorem extract_eq (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α)
    (p : Profile) :
    extract (layout p) (partialState ops input outside p p.n) = some (spec ops p input) := by
  simp only [extract, layout, List.zipIdx_cons, List.zipIdx_nil, List.flatMap_cons,
    List.flatMap_nil, List.nil_append]
  simp only [List.map_cons, List.map_nil, show Role.input ≠ Role.output by decide,
    ↓reduceIte, List.nil_append, List.append_nil]
  change (((List.range p.n).map (fun i => (2, i))).mapM
    (fun bi => (partialState ops input outside p p.n).memory (cell bi.1 bi.2)) :
      Option (List α)) = _
  rw [LarkPointwise.mapM_map]
  exact LarkPointwise.mapM_some (List.range p.n) _ _ (by
    intro i hi
    exact partialState_output ops input outside p p.n i (List.mem_range.mp hi))

/-- Whole launch of the real scalar machine, not an assumed loop summary. -/
theorem correct (ops : Ops α) (p : Profile) (w : Nat)
    (hn : 0<p.n) (hk : 0<p.k) (hb : p.n < 2147483648 ∧ p.k < 2147483648) (hw : 0<w) :
    Correct ops (layout p) (geometry p w) (fuel p) (program p) (spec ops p) := by
  intro input outside
  refine ⟨partialState ops input outside p p.n,
    launch_eq ops input outside p w hn hk hb hw, ?_, extract_eq ops input outside p⟩
  exact owned_raceFree (geometry p w) _ (partialState_owned ops input outside p p.n)

/-- Tensor-level left-fold dot product, independent of PCs and machine state. -/
def dotSpec (ops : Ops α) (input : Nat → Nat → α) (p : Profile) (t : Nat) : α :=
  (List.range p.k).foldl (fun acc j => ops.add acc (term ops input p t j)) (ops.literal 0 1)

def matrixSpec (ops : Ops α) (p : Profile) (input : Nat → Nat → α) : List α :=
  (List.range p.n).map (fun t => LarkPointwise.value ops (dotSpec ops input p t) p.post)

theorem folded_eq_list (ops : Ops α) (input : Nat → Nat → α) (p : Profile) (t r j : Nat) (acc : α) :
    folded ops input p t j r acc =
      (List.range' j r).foldl (fun acc z => ops.add acc (term ops input p t z)) acc := by
  induction r generalizing j acc with
  | zero => rfl
  | succ r ih =>
      rw [folded, List.range'_succ, List.foldl_cons]
      exact ih (j+1) _

theorem result_eq_dot (ops : Ops α) (input : Nat → Nat → α) (p : Profile) (t : Nat) :
    result ops input p t = LarkPointwise.value ops (dotSpec ops input p t) p.post := by
  unfold result dotSpec
  rw [folded_eq_list, List.range_eq_range']

theorem spec_eq_matrixSpec (ops : Ops α) (p : Profile) (input : Nat → Nat → α) :
    spec ops p input = matrixSpec ops p input := by
  simp only [spec, matrixSpec, result_eq_dot]

theorem matrix_correct (ops : Ops α) (p : Profile) (w : Nat)
    (hn : 0<p.n) (hk : 0<p.k) (hb : p.n < 2147483648 ∧ p.k < 2147483648) (hw : 0<w) :
    Correct ops (layout p) (geometry p w) (fuel p) (program p) (matrixSpec ops p) := by
  have hs : spec ops p = matrixSpec ops p := by
    funext input
    exact spec_eq_matrixSpec ops p input
  rw [← hs]
  exact correct ops p w hn hk hb hw

#print axioms loop_step
#print axioms loop_eq
#print axioms lane_eq
#print axioms correct
#print axioms matrix_correct

end LarkDotMap
