import Std

/-!
Pinned, dependency-free machine model for the bounded scalar profile.
Scalar arithmetic is universally quantified: the certificate holds for EVERY
interpretation of scalar operations and explicit half conversions.
This extends Model.lean; operation-to-hardware correspondence remains trusted.
Addresses and control depend only on exact integer index expressions.
-/
namespace LarkNonlinear

structure Ops (α : Type) where
  literal : Int → Nat → α
  add : α → α → α
  sub : α → α → α
  mul : α → α → α
  max : α → α → α
  div : α → α → α
  exp : α → α
  tanh : α → α
  rsqrt : α → α
  fromHalf : α → α
  toHalf : α → α

inductive Space where
  | global | shared | local
  deriving DecidableEq, Repr, BEq

structure Location where
  space : Space
  owner : Nat
  buffer : Nat
  offset : Nat
  deriving DecidableEq, Repr, BEq

inductive Role where
  | input | output | scratch
  deriving DecidableEq, Repr, BEq

structure Buffer where
  role : Role
  size : Nat
  deriving DecidableEq, Repr

structure Layout where
  global : List Buffer
  shared : List Nat := []
  locals : List Nat := []
  deriving DecidableEq, Repr

structure Geometry where
  grid : Nat
  block : Nat
  warp : Nat
  deriving DecidableEq, Repr

structure Fuel where
  lane : Nat
  warp : Nat
  block : Nat
  grid : Nat
  deriving DecidableEq, Repr

inductive Index where
  | const : Int → Index
  | tid | bid | bdim
  | ivar : Nat → Index
  | add : Index → Index → Index
  | sub : Index → Index → Index
  | mul : Index → Index → Index
  | div : Index → Index → Index
  | mod : Index → Index → Index
  deriving DecidableEq, Repr

inductive Predicate where
  | lt : Index → Index → Predicate
  | le : Index → Index → Predicate
  | eq : Index → Index → Predicate
  | ne : Index → Index → Predicate
  deriving DecidableEq, Repr

inductive Binary where
  | add | sub | mul | max | div
  deriving DecidableEq, Repr

inductive Unary where
  | exp | tanh | rsqrt | fromHalf | toHalf
  deriving DecidableEq, Repr

inductive Expr where
  | lit : Int → Nat → Expr
  | reg : Nat → Expr
  | load : Space → Nat → Index → Expr
  | bin : Binary → Expr → Expr → Expr
  | un : Unary → Expr → Expr
  deriving DecidableEq, Repr

inductive Cut where
  | warp | block | grid | halt
  deriving DecidableEq, Repr, BEq

inductive Instr where
  | index : Nat → Index → Instr
  | assign : Nat → Expr → Instr
  | store : Space → Nat → Index → Expr → Instr
  | branch : Predicate → Nat → Instr -- false target; true falls through
  | jump : Nat → Instr
  | barrier : Cut → Instr
  | halt
  deriving DecidableEq, Repr

structure Epoch where
  grid : Nat := 0
  block : Nat := 0
  warp : Nat := 0
  deriving DecidableEq, Repr

structure Access where
  thread : Nat
  location : Location
  write : Bool
  epoch : Epoch
  deriving DecidableEq, Repr

structure State (α : Type) where
  pc : Nat → Nat
  indices : Nat → Nat → Option Int
  regs : Nat → Nat → Option α
  memory : Location → Option α
  epochs : Nat → Epoch
  trace : List Access

def initial (layout : Layout) (input : Nat → Nat → α)
    (outside : Location → Option α) : State α where
  pc := fun _ => 0
  indices := fun _ _ => none
  regs := fun _ _ => none
  epochs := fun _ => {}
  trace := []
  memory := fun l =>
    if l.space = .global ∧ l.owner = 0 then
      match layout.global[l.buffer]? with
      | some b => if b.role = .input ∧ l.offset < b.size
                  then some (input l.buffer l.offset) else outside l
      | none => outside l
    else outside l

/-- The fixed interface is satisfiable for every input, without a kernel premise. -/
theorem initial_exists (layout : Layout) (input : Nat → Nat → α) :
    ∃ s : State α, s = initial layout input (fun _ => none) := ⟨_, rfl⟩

def StdPre (layout : Layout) (input : Nat → Nat → α) (s : State α) : Prop :=
  ∃ outside, s = initial layout input outside

theorem pre_satisfiable (layout : Layout) (input : Nat → Nat → α) :
    ∃ s, StdPre layout input s := ⟨_, (fun _ => none), rfl⟩

theorem initial_places (layout : Layout) (input : Nat → Nat → α)
    (outside : Location → Option α) (b i : Nat) (buf : Buffer)
    (hb : layout.global[b]? = some buf) (hr : buf.role = .input) (hi : i < buf.size) :
    (initial layout input outside).memory ⟨.global, 0, b, i⟩ = some (input b i) := by
  simp [initial, hb, hr, hi]

def int32 (n : Int) : Option Int :=
  if 0 ≤ n ∧ n < 2147483648 then some n else none

def evalIndex (g : Geometry) (t : Nat) (s : State α) : Index → Option Int
  | .const n => int32 n
  | .tid => int32 (Int.ofNat (t % g.block))
  | .bid => int32 (Int.ofNat (t / g.block))
  | .bdim => int32 (Int.ofNat g.block)
  | .ivar r => s.indices t r
  | .add a b => do int32 ((← evalIndex g t s a) + (← evalIndex g t s b))
  | .sub a b => do int32 ((← evalIndex g t s a) - (← evalIndex g t s b))
  | .mul a b => do int32 ((← evalIndex g t s a) * (← evalIndex g t s b))
  | .div a b => do
      let x ← evalIndex g t s a
      let y ← evalIndex g t s b
      if y = 0 ∨ x < 0 ∨ y < 0 then none else some (x / y)
  | .mod a b => do
      let x ← evalIndex g t s a
      let y ← evalIndex g t s b
      if y = 0 ∨ x < 0 ∨ y < 0 then none else some (x % y)

def evalPredicate (g : Geometry) (t : Nat) (s : State α) : Predicate → Option Bool
  | .lt a b => return (← evalIndex g t s a) < (← evalIndex g t s b)
  | .le a b => return (← evalIndex g t s a) ≤ (← evalIndex g t s b)
  | .eq a b => return (← evalIndex g t s a) = (← evalIndex g t s b)
  | .ne a b => return (← evalIndex g t s a) ≠ (← evalIndex g t s b)

def location (layout : Layout) (g : Geometry) (t : Nat) (space : Space)
    (buffer : Nat) (index : Int) (write : Bool) : Option Location := do
  if index < 0 then none else do
    let bounds : Option (Nat × Nat) := match space with
      | .global => do
          let b ← layout.global[buffer]?
          if write && b.role == .input then none else some (0, b.size)
      | .shared => do pure (t / g.block, ← layout.shared[buffer]?)
      | .local => do pure (t, ← layout.locals[buffer]?)
    let (owner, size) ← bounds
    if index.toNat < size then some ⟨space, owner, buffer, index.toNat⟩ else none

def record (s : State α) (t : Nat) (l : Location) (write : Bool) : State α :=
  { s with trace := ⟨t, l, write, s.epochs t⟩ :: s.trace }

def applyBinary (ops : Ops α) : Binary → α → α → α
  | .add => ops.add
  | .sub => ops.sub
  | .mul => ops.mul
  | .max => ops.max
  | .div => ops.div

def applyUnary (ops : Ops α) : Unary → α → α
  | .exp => ops.exp
  | .tanh => ops.tanh
  | .rsqrt => ops.rsqrt
  | .fromHalf => ops.fromHalf
  | .toHalf => ops.toHalf

def evalExpr (ops : Ops α) (layout : Layout) (g : Geometry) (t : Nat) :
    Expr → State α → Option (α × State α)
  | .lit n d, s => if d = 0 then none else some (ops.literal n d, s)
  | .reg r, s => return (← s.regs t r, s)
  | .load space b ix, s => do
      let i ← evalIndex g t s ix
      let l ← location layout g t space b i false
      let v ← s.memory l
      return (v, record s t l false)
  | .bin op a b, s => do
      let (x, s) ← evalExpr ops layout g t a s
      let (y, s) ← evalExpr ops layout g t b s
      return (applyBinary ops op x y, s)
  | .un op a, s => do
      let (x, s) ← evalExpr ops layout g t a s
      return (applyUnary ops op x, s)

def advance (s : State α) (t : Nat) (pc : Nat) : State α :=
  { s with pc := fun u => if u = t then pc else s.pc u }

def execute (ops : Ops α) (layout : Layout) (g : Geometry) (t : Nat)
    (i : Instr) (s : State α) : Option (State α) := do
  let next := s.pc t + 1
  match i with
  | .index r ix =>
      let v ← evalIndex g t s ix
      return advance { s with indices := fun u q =>
        if u = t ∧ q = r then some v else s.indices u q } t next
  | .assign r e =>
      let (v, s) ← evalExpr ops layout g t e s
      return advance { s with regs := fun u q =>
        if u = t ∧ q = r then some v else s.regs u q } t next
  | .store space b ix e =>
      let index ← evalIndex g t s ix
      let loc ← location layout g t space b index true
      let (v, s) ← evalExpr ops layout g t e s
      let s := record s t loc true
      let updated : State α := { s with memory := fun cell =>
        (if cell = loc then some v else s.memory cell) }
      return advance updated t next
  | .branch p target =>
      let yes ← evalPredicate g t s p
      return advance s t (if yes then next else target)
  | .jump target => return advance s t target
  | .barrier _ | .halt => none

def parked (p : List Instr) (s : State α) (t : Nat) : Option Cut :=
  match p[s.pc t]? with
  | some (.barrier c) => some c
  | some .halt => some .halt
  | _ => none

def runLane (ops : Ops α) (layout : Layout) (g : Geometry) (p : List Instr)
    (t : Nat) : Nat → State α → Option (State α)
  | 0, _ => none
  | n + 1, s =>
      match parked p s t with
      | some _ => some s
      | none => do
          let i ← p[s.pc t]?
          let s ← execute ops layout g t i s
          runLane ops layout g p t n s

def converged (p : List Instr) (ts : List Nat) (s : State α) : Option Cut := do
  let t ← ts.head?
  if ts.all (fun u => s.pc u == s.pc t) then parked p s t else none

def bumpEpoch (e : Epoch) : Cut → Epoch
  | .warp => { e with warp := e.warp + 1 }
  | .block => { e with block := e.block + 1 }
  | .grid => { e with grid := e.grid + 1 }
  | .halt => e

def resume (ts : List Nat) (c : Cut) (s : State α) : State α :=
  { s with
    pc := fun t => if ts.contains t then s.pc t + 1 else s.pc t
    epochs := fun t => if ts.contains t then bumpEpoch (s.epochs t) c else s.epochs t }

def warpThreads (g : Geometry) (b w : Nat) : List Nat :=
  ((List.range g.block).filter (fun t => t / g.warp == w)).map (b * g.block + ·)

def blockThreads (g : Geometry) (b : Nat) : List Nat :=
  (List.range g.block).map (b * g.block + ·)

def runWarp (ops : Ops α) (layout : Layout) (g : Geometry) (f : Fuel)
    (p : List Instr) (ts : List Nat) : Nat → State α → Option (State α)
  | 0, _ => none
  | n + 1, s => do
      let s ← ts.foldlM (fun s t => runLane ops layout g p t f.lane s) s
      let c ← converged p ts s
      if c = .warp then runWarp ops layout g f p ts n (resume ts c s) else some s

def runBlock (ops : Ops α) (layout : Layout) (g : Geometry) (f : Fuel)
    (p : List Instr) (b : Nat) : Nat → State α → Option (State α)
  | 0, _ => none
  | n + 1, s => do
      let ws := List.range ((g.block + g.warp - 1) / g.warp)
      let s ← ws.foldlM (fun s w =>
        runWarp ops layout g f p (warpThreads g b w) f.warp s) s
      let ts := blockThreads g b
      let c ← converged p ts s
      if c = .block then runBlock ops layout g f p b n (resume ts c s) else
        if c = .grid ∨ c = .halt then some s else none

def runGrid (ops : Ops α) (layout : Layout) (g : Geometry) (f : Fuel)
    (p : List Instr) : Nat → State α → Option (State α)
  | 0, _ => none
  | n + 1, s => do
      let s ← (List.range g.grid).foldlM (fun s b =>
        runBlock ops layout g f p b f.block s) s
      let ts := List.range (g.grid * g.block)
      let c ← converged p ts s
      if c = .grid then runGrid ops layout g f p n (resume ts c s) else
        if c = .halt then some s else none

def runLaunch (ops : Ops α) (layout : Layout) (g : Geometry) (f : Fuel)
    (p : List Instr) (s : State α) : Option (State α) :=
  if g.grid = 0 ∨ g.block = 0 ∨ g.warp = 0 then none
  else runGrid ops layout g f p f.grid s

/-- Only a synchronization scope shared by BOTH threads orders two accesses. -/
def ordered (g : Geometry) (a b : Access) : Bool :=
  a.epoch.grid != b.epoch.grid ||
  (a.thread / g.block == b.thread / g.block &&
    (a.epoch.block != b.epoch.block ||
      ((a.thread % g.block) / g.warp == (b.thread % g.block) / g.warp &&
        a.epoch.warp != b.epoch.warp)))

def sameLocation (a b : Location) : Bool :=
  decide (a.space = b.space) && a.owner == b.owner &&
    a.buffer == b.buffer && a.offset == b.offset

def conflict (g : Geometry) (a b : Access) : Bool :=
  a.thread != b.thread && sameLocation a.location b.location &&
    (a.write || b.write) && !(ordered g a b)

def raceFree (g : Geometry) (trace : List Access) : Bool :=
  trace.all (fun a => trace.all (fun b => !(conflict g a b)))

def extract (layout : Layout) (s : State α) : Option (List α) := do
  let cells := (layout.global.zipIdx).flatMap fun (b, id) =>
    if b.role = .output then (List.range b.size).map (id, ·) else []
  cells.mapM fun (b, i) => s.memory ⟨.global, 0, b, i⟩

inductive Segment where
  | op : Instr → Segment
  | seq : List Segment → Segment
  | repeat : Nat → List Instr → Segment
  deriving Repr

def flattenSegment : Segment → List Instr
  | .op i => [i]
  | .seq ss => ss.flatMap flattenSegment
  | .repeat n body => (List.replicate n body).flatten

def flatten (ss : List Segment) : List Instr := ss.flatMap flattenSegment

/-- The final statement fixes its program and specification before any proof proposal. -/
def Correct (ops : Ops α) (layout : Layout) (g : Geometry) (f : Fuel)
    (p : List Instr) (spec : (Nat → Nat → α) → List α) : Prop :=
  ∀ input outside, ∃ final,
    runLaunch ops layout g f p (initial layout input outside) = some final ∧
    raceFree g final.trace = true ∧ extract layout final = some (spec input)

theorem correct_from_pre (ops : Ops α) (layout : Layout) (g : Geometry) (f : Fuel)
    (p : List Instr) (spec : (Nat → Nat → α) → List α)
    (h : Correct ops layout g f p spec) (input : Nat → Nat → α) (s : State α)
    (pre : StdPre layout input s) :
    ∃ final, runLaunch ops layout g f p s = some final ∧
      raceFree g final.trace = true ∧ extract layout final = some (spec input) := by
  obtain ⟨outside, rfl⟩ := pre
  exact h input outside

theorem assemble (ops : Ops α) (layout : Layout) (g : Geometry) (f : Fuel)
    (p : List Instr) (segments : List Segment)
    (spec : (Nat → Nat → α) → List α)
    (seg : flatten segments = p)
    (eqv : Correct ops layout g f (flatten segments) spec) :
    Correct ops layout g f p spec := by
  rw [← seg]
  exact eqv

end LarkNonlinear


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


/-! Grid assembly for checked scalar lanes with one read-only input/output array. -/
namespace LarkUnaryMap
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 20000000

def layout (n : Nat) : Layout := ⟨[⟨.input,n⟩,⟨.output,n⟩],[],[]⟩
def geometry (n w : Nat) : Geometry := LarkPointwise.geometry n w
def cell (b i : Nat) : Location := ⟨.global,0,b,i⟩
def Reads (n : Nat) (input : Nat → Nat → α) (s : State α) : Prop :=
  ∀ i, i<n → s.memory (cell 0 i)=some (input 0 i)
def Owned (tr : List Access) : Prop :=
  ∀ a ∈ tr, if a.write then a.location=cell 1 a.thread else a.location.buffer<1

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
      if l=cell 1 t then some (value α ops input t) else s.memory l
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
  | zero => intro i hi; simp [partialState,initial,layout,cell,hi]
  | succ q ih =>
    intro i hi
    simpa [partialState,p.afterMemory,cell] using ih i hi

theorem partialState_output (p : Profile) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (q t : Nat) (ht : t<q) :
    (partialState p ops input outside q).memory (cell 1 t)=some (p.value α ops input t) := by
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
  | zero => simp [Owned,partialState,initial]
  | succ q ih => exact p.afterOwned α ops input q _ ih

theorem owned_raceFree (g : Geometry) (tr : List Access) (h : Owned tr) : raceFree g tr=true := by
  apply List.all_eq_true.mpr
  intro a ha
  apply List.all_eq_true.mpr
  intro b hb
  have hx:=h a ha
  have hy:=h b hb
  by_cases ht : a.thread=b.thread
  · simp [conflict,ht]
  · cases haw : a.write <;> cases hbw : b.write
    · simp [conflict,haw,hbw]
    · simp only [haw,hbw,Bool.false_eq_true,↓reduceIte] at hx hy
      have hbeq : (a.location.buffer==1)=false := by simp [show a.location.buffer≠1 by omega]
      simp [conflict,sameLocation,haw,hbw,hy,cell,hbeq]
    · simp only [haw,hbw,Bool.false_eq_true,↓reduceIte] at hx hy
      have hbeq : (1==b.location.buffer)=false := by simp [show 1≠b.location.buffer by omega]
      simp [conflict,sameLocation,haw,hbw,hx,cell,hbeq]
    · simp only [haw,hbw,Bool.false_eq_true,↓reduceIte] at hx hy
      have hbeq : (a.thread==b.thread)=false := by simp [ht]
      simp [conflict,sameLocation,haw,hbw,hx,hy,cell,hbeq]

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
  change (((List.range p.n).map (fun i=>(1,i))).mapM
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
end LarkUnaryMap


/-! A checked five-instruction reduction cycle over one read-only FP16 array. -/
namespace LarkFoldPhase
open LarkNonlinear LarkReduction
set_option maxRecDepth 10000
set_option maxHeartbeats 20000000

inductive Term where
  | input | context | accumulator
  | lit : Int → Nat → Term
  | bin : Binary → Term → Term → Term
  | un : Unary → Term → Term
  deriving Repr

def lower : Term → Expr
  | .input => .reg 2
  | .context => .reg 1
  | .accumulator => .reg 0
  | .lit n d => .lit n d
  | .bin op a b => .bin op (lower a) (lower b)
  | .un op a => .un op (lower a)
def Valid : Term → Prop
  | .input | .context | .accumulator => True
  | .lit _ d => d≠0
  | .bin _ a b => Valid a ∧ Valid b
  | .un _ a => Valid a
def value (ops : Ops α) (x ctx acc : α) : Term → α
  | .input => x
  | .context => ctx
  | .accumulator => acc
  | .lit n d => ops.literal n d
  | .bin op a b => applyBinary ops op (value ops x ctx acc a) (value ops x ctx acc b)
  | .un op a => applyUnary ops op (value ops x ctx acc a)

theorem eval_lower (ops : Ops α) (l : Layout) (g : Geometry) (t : Nat) (s : State α)
    (x ctx acc : α) (e : Term) (hv : Valid e)
    (hx : s.regs t 2=some x) (hc : s.regs t 1=some ctx) (ha : s.regs t 0=some acc) :
    evalExpr ops l g t (lower e) s=some (value ops x ctx acc e,s) := by
  induction e with
  | input => simp [lower,value,evalExpr,hx]
  | context => simp [lower,value,evalExpr,hc]
  | accumulator => simp [lower,value,evalExpr,ha]
  | lit n d => simp [lower,value,evalExpr,Valid] at hv ⊢;exact hv
  | bin op a b ia ib =>
    simp only [Valid] at hv
    simp [lower,value,evalExpr,ia hv.1,ib hv.2]
  | un op a ia => simp [lower,value,evalExpr,ia hv]

structure Phase where
  n : Nat
  header : Nat
  exitPc : Nat
  reducer : Binary
  term : Term
  valid : Valid term
  program : List Instr
  atHeader : program[header]?=some (.branch (.lt (.ivar 1) (.const (n : Int))) exitPc)
  atLoad : program[header+1]?=some (.assign 2 (.un .fromHalf (.load .global 0 (.ivar 1))))
  atAcc : program[header+2]?=some (.assign 0 (.bin reducer (.reg 0) (lower term)))
  atCounter : program[header+3]?=some (.index 1 (.add (.ivar 1) (.const 1)))
  atJump : program[header+4]?=some (.jump header)

def updated (p : Phase) (ops : Ops α) (input : Nat → Nat → α) (ctx acc : α) (j : Nat) : α :=
  applyBinary ops p.reducer acc (value ops (ops.fromHalf (input 0 j)) ctx acc p.term)

def stepState (p : Phase) (ops : Ops α) (input : Nat → Nat → α) (ctx acc : α)
    (t j : Nat) (s : State α) : State α :=
  let s:=advance s t (p.header+1)
  let s:=setReg (record s t (LarkUnaryMap.cell 0 j) false) t 2
    (ops.fromHalf (input 0 j)) (p.header+2)
  let s:=setReg s t 0 (updated p ops input ctx acc j) (p.header+3)
  let s:=setIndex s t 1 ((j+1 : Nat) : Int) (p.header+4)
  advance s t p.header

theorem load_eq (ops : Ops α) (n w t j : Nat) (s : State α) (input : Nat → Nat → α)
    (hr : LarkUnaryMap.Reads n input s) (hj : s.indices t 1=some (j : Int)) (hb : j<n) :
    evalExpr ops (LarkUnaryMap.layout n) (LarkUnaryMap.geometry n w) t
      (.un .fromHalf (.load .global 0 (.ivar 1))) s=
      some (ops.fromHalf (input 0 j),record s t (LarkUnaryMap.cell 0 j) false) := by
  have hneg : ¬ (j : Int)<0 := by omega
  have hl : location (LarkUnaryMap.layout n) (LarkUnaryMap.geometry n w) t .global 0
      (j : Int) false=some (LarkUnaryMap.cell 0 j) := by
    simp [location,LarkUnaryMap.layout,LarkUnaryMap.cell,hneg,hb]
  simp only [evalExpr,evalIndex,hj,bind,pure,Option.bind,hl,hr j hb]
  rfl

theorem cycle (p : Phase) (ops : Ops α) (w t j f : Nat) (s : State α)
    (input : Nat → Nat → α) (ctx acc : α)
    (hr : LarkUnaryMap.Reads p.n input s) (hi : s.indices t 1=some (j : Int))
    (hc : s.regs t 1=some ctx) (ha : s.regs t 0=some acc)
    (hp : s.pc t=p.header) (hj : j<p.n) (hb : p.n<2147483648) :
    runLane ops (LarkUnaryMap.layout p.n) (LarkUnaryMap.geometry p.n w) p.program t (f+5) s=
      runLane ops (LarkUnaryMap.layout p.n) (LarkUnaryMap.geometry p.n w) p.program t f
        (stepState p ops input ctx acc t j s) := by
  let s1:=advance s t (p.header+1)
  let s2:=setReg (record s1 t (LarkUnaryMap.cell 0 j) false) t 2
    (ops.fromHalf (input 0 j)) (p.header+2)
  let s3:=setReg s2 t 0 (updated p ops input ctx acc j) (p.header+3)
  let s4:=setIndex s3 t 1 ((j+1 : Nat) : Int) (p.header+4)
  have hg:=predicate_lt_of (LarkUnaryMap.geometry p.n w) t s (.ivar 1) (.const (p.n : Int))
    (j : Int) (p.n : Int) hi (int32_cast p.n hb) (by omega)
  have h1 : execute ops (LarkUnaryMap.layout p.n) (LarkUnaryMap.geometry p.n w) t
      (.branch (.lt (.ivar 1) (.const (p.n : Int))) p.exitPc) s=some s1 := by
    simp only [execute,hg,bind,pure,Option.bind,hp];rfl
  have he2:=load_eq ops p.n w t j s1 input hr hi hj
  have h2 : execute ops (LarkUnaryMap.layout p.n) (LarkUnaryMap.geometry p.n w) t
      (.assign 2 (.un .fromHalf (.load .global 0 (.ivar 1)))) s1=some s2 := by
    simp only [execute,he2,bind,pure,Option.bind]
    have hh : s1.pc t+1=p.header+2 := by simp [s1,advance]
    rw [hh]
    rfl
  have he3:=eval_bin_of ops (LarkUnaryMap.layout p.n) (LarkUnaryMap.geometry p.n w) t
    p.reducer (.reg 0) (lower p.term) s2 s2 s2 acc
    (value ops (ops.fromHalf (input 0 j)) ctx acc p.term)
    (by simp [evalExpr,s2,setReg,record,s1,advance,ha])
    (eval_lower ops _ _ t s2 _ ctx acc p.term p.valid
      (by simp [s2,setReg,advance])
      (by simpa [s2,setReg,record,s1,advance] using hc)
      (by simpa [s2,setReg,record,s1,advance] using ha))
  have h3 : execute ops (LarkUnaryMap.layout p.n) (LarkUnaryMap.geometry p.n w) t
      (.assign 0 (.bin p.reducer (.reg 0) (lower p.term))) s2=some s3 := by
    simp only [execute,he3,bind,pure,Option.bind]
    have hh : s2.pc t+1=p.header+3 := by simp [s2,setReg,advance]
    rw [hh]
    rfl
  have he4:=eval_add_of (LarkUnaryMap.geometry p.n w) t s3 (.ivar 1) (.const 1)
    (j : Int) 1 ((j+1 : Nat) : Int) hi (by rfl)
    (Eq.trans (congrArg int32 (Int.natCast_add j 1).symm) (int32_cast (j+1) (by omega)))
  have h4 : execute ops (LarkUnaryMap.layout p.n) (LarkUnaryMap.geometry p.n w) t
      (.index 1 (.add (.ivar 1) (.const 1))) s3=some s4 := by
    simp only [execute,he4,bind,pure,Option.bind]
    have hh : s3.pc t+1=p.header+4 := by simp [s3,setReg,advance]
    rw [hh]
    rfl
  have h5 : execute ops (LarkUnaryMap.layout p.n) (LarkUnaryMap.geometry p.n w) t
      (.jump p.header) s4=some (stepState p ops input ctx acc t j s) := by rfl
  rw [LarkPointwise.lane_step ops _ _ _ _ _ _ _ _
    (by simp [parked,hp,p.atHeader]) (by simp [hp,p.atHeader]) h1]
  rw [LarkPointwise.lane_step ops _ _ _ _ _ _ _ _
    (by simp [parked,s1,advance,p.atLoad]) (by simp [s1,advance,p.atLoad]) h2]
  rw [LarkPointwise.lane_step ops _ _ _ _ _ _ _ _
    (by simp [parked,s2,setReg,advance,p.atAcc]) (by simp [s2,setReg,advance,p.atAcc]) h3]
  rw [LarkPointwise.lane_step ops _ _ _ _ _ _ _ _
    (by simp [parked,s3,setReg,advance,p.atCounter]) (by simp [s3,setReg,advance,p.atCounter]) h4]
  rw [LarkPointwise.lane_step ops _ _ _ _ _ _ _ _
    (by simp [parked,s4,setIndex,advance,p.atJump]) (by simp [s4,setIndex,advance,p.atJump]) h5]

def iterate (p : Phase) (ops : Ops α) (input : Nat → Nat → α) (ctx : α) (t : Nat) :
    Nat → Nat → α → State α → State α
  | _,0,_,s => advance s t p.exitPc
  | j,r+1,acc,s => iterate p ops input ctx t (j+1) r (updated p ops input ctx acc j)
      (stepState p ops input ctx acc t j s)

def folded (p : Phase) (ops : Ops α) (input : Nat → Nat → α) (ctx : α) : Nat → Nat → α → α
  | _,0,acc => acc
  | j,r+1,acc => folded p ops input ctx (j+1) r (updated p ops input ctx acc j)

theorem exit (p : Phase) (ops : Ops α) (w t f : Nat) (s : State α)
    (hi : s.indices t 1=some (p.n : Int)) (hp : s.pc t=p.header) (hb : p.n<2147483648) :
    runLane ops (LarkUnaryMap.layout p.n) (LarkUnaryMap.geometry p.n w) p.program t (f+1) s=
      runLane ops (LarkUnaryMap.layout p.n) (LarkUnaryMap.geometry p.n w) p.program t f
        (advance s t p.exitPc) := by
  have hg:=predicate_nlt_of (LarkUnaryMap.geometry p.n w) t s (.ivar 1) (.const (p.n : Int))
    (p.n : Int) (p.n : Int) hi (int32_cast p.n hb) (by omega)
  have he : execute ops (LarkUnaryMap.layout p.n) (LarkUnaryMap.geometry p.n w) t
      (.branch (.lt (.ivar 1) (.const (p.n : Int))) p.exitPc) s=some (advance s t p.exitPc) := by
    simp only [execute,hg,bind,pure,Option.bind];rfl
  exact LarkPointwise.lane_step ops _ _ _ _ _ _ _ _
    (by simp [parked,hp,p.atHeader]) (by simp [hp,p.atHeader]) he

theorem run_eq (p : Phase) (ops : Ops α) (input : Nat → Nat → α) (ctx acc : α)
    (w t r j f : Nat) (s : State α)
    (hr : LarkUnaryMap.Reads p.n input s) (hi : s.indices t 1=some (j : Int))
    (hc : s.regs t 1=some ctx) (ha : s.regs t 0=some acc) (hp : s.pc t=p.header)
    (hcount : j+r=p.n) (hb : p.n<2147483648) :
    runLane ops (LarkUnaryMap.layout p.n) (LarkUnaryMap.geometry p.n w) p.program t (f+5*r+1) s=
      runLane ops (LarkUnaryMap.layout p.n) (LarkUnaryMap.geometry p.n w) p.program t f
        (iterate p ops input ctx t j r acc s) := by
  induction r generalizing j acc s with
  | zero =>
    have hj : j=p.n := by omega
    subst j
    simpa [iterate] using exit p ops w t f s hi hp hb
  | succ r ih =>
    have hh : j<p.n := by omega
    have hf : f+5*(r+1)+1=(f+5*r+1)+5 := by omega
    rw [hf,cycle p ops w t j (f+5*r+1) s input ctx acc hr hi hc ha hp hh hb]
    change _=runLane _ _ _ _ _ _ (iterate p ops input ctx t (j+1) r _ _)
    apply ih
    · exact hr
    · simp [stepState,setIndex,setReg,record,advance]
    · simpa [stepState,setIndex,setReg,record,advance] using hc
    · simp [stepState,setIndex,setReg,record,advance]
    · simp [stepState,advance]
    · omega

theorem iterate_memory (p : Phase) (ops : Ops α) (input : Nat → Nat → α) (ctx acc : α)
    (t r j : Nat) (s : State α) :
    (iterate p ops input ctx t j r acc s).memory=s.memory := by
  induction r generalizing j acc s with
  | zero => rfl
  | succ r ih => exact ih (updated p ops input ctx acc j) (j+1) _

theorem iterate_pc (p : Phase) (ops : Ops α) (input : Nat → Nat → α) (ctx acc : α)
    (t r j u : Nat) (s : State α) :
    (iterate p ops input ctx t j r acc s).pc u=if u=t then p.exitPc else s.pc u := by
  induction r generalizing j acc s with
  | zero => rfl
  | succ r ih =>
    simp only [iterate,ih]
    by_cases h : u=t <;> simp [stepState,setIndex,setReg,record,advance,h]

theorem iterate_index0 (p : Phase) (ops : Ops α) (input : Nat → Nat → α) (ctx acc : α)
    (t r j : Nat) (s : State α) :
    (iterate p ops input ctx t j r acc s).indices t 0=s.indices t 0 := by
  induction r generalizing j acc s with
  | zero => rfl
  | succ r ih =>
    simpa [iterate,stepState,setIndex,setReg,record,advance] using
      ih (updated p ops input ctx acc j) (j+1) (stepState p ops input ctx acc t j s)

theorem iterate_context (p : Phase) (ops : Ops α) (input : Nat → Nat → α) (ctx acc : α)
    (t r j : Nat) (s : State α) :
    (iterate p ops input ctx t j r acc s).regs t 1=s.regs t 1 := by
  induction r generalizing j acc s with
  | zero => rfl
  | succ r ih =>
    simpa [iterate,stepState,setIndex,setReg,record,advance] using
      ih (updated p ops input ctx acc j) (j+1) (stepState p ops input ctx acc t j s)

theorem iterate_acc (p : Phase) (ops : Ops α) (input : Nat → Nat → α) (ctx acc : α)
    (t r j : Nat) (s : State α) (ha : s.regs t 0=some acc) :
    (iterate p ops input ctx t j r acc s).regs t 0=some (folded p ops input ctx j r acc) := by
  induction r generalizing j acc s with
  | zero => exact ha
  | succ r ih =>
    change (iterate p ops input ctx t (j+1) r _ _).regs t 0=_
    apply ih
    simp [stepState,setIndex,setReg,advance]

theorem owned_read (tr : List Access) (h : LarkUnaryMap.Owned tr) (t j : Nat) (e : Epoch) :
    LarkUnaryMap.Owned (⟨t,LarkUnaryMap.cell 0 j,false,e⟩::tr) := by
  intro a ha
  simp only [List.mem_cons] at ha
  rcases ha with rfl|ha
  · simp [LarkUnaryMap.cell]
  · exact h a ha

theorem iterate_owned (p : Phase) (ops : Ops α) (input : Nat → Nat → α) (ctx acc : α)
    (t r j : Nat) (s : State α) (h : LarkUnaryMap.Owned s.trace) :
    LarkUnaryMap.Owned (iterate p ops input ctx t j r acc s).trace := by
  induction r generalizing j acc s with
  | zero => exact h
  | succ r ih =>
    apply ih
    exact owned_read s.trace h t j (s.epochs t)

#print axioms cycle
#print axioms run_eq
end LarkFoldPhase


/-! Scalar FP16 RMSNorm, LayerNorm and stable Softmax, by actual-machine induction. -/
namespace LarkNormalization
open LarkNonlinear LarkFoldPhase
open LarkReduction (setIndex setReg int32_cast execute_index_of execute_pure_of)
set_option maxRecDepth 10000
set_option maxHeartbeats 20000000

inductive Kind where
  | rms | layer | softmax
  deriving Repr, DecidableEq

def firstStart (kind : Kind) : Nat := if kind=.softmax then 1 else 0
def secondStart (kind : Kind) (n : Nat) : Nat := if kind=.rms then n else 0
def firstTerm : Kind → Term
  | .rms => .bin .mul .input .input
  | _ => .input
def secondTerm : Kind → Term
  | .layer => .bin .mul (.bin .sub .input .context) (.bin .sub .input .context)
  | .softmax => .un .exp (.bin .sub .input .context)
  | .rms => .input
def firstOp (kind : Kind) : Binary := if kind=.softmax then .max else .add
def mean (n : Nat) : Term := .bin .div .accumulator (.lit (n : Int) 1)
def epilogue (kind : Kind) (n : Nat) : Term :=
  let eps : Term:=.lit 1 100000
  match kind with
  | .rms => .bin .mul .input (.un .rsqrt (.bin .add .context eps))
  | .layer => .bin .mul (.bin .sub .input .context)
      (.un .rsqrt (.bin .add (mean n) eps))
  | .softmax => .bin .div (.un .exp (.bin .sub .input .context)) .accumulator
def seedExpr (kind : Kind) : Expr :=
  if kind=.softmax then .un .fromHalf (.load .global 0 (.const 0)) else .lit 0 1
def middleExpr (kind : Kind) (n : Nat) : Expr :=
  if kind=.softmax then .reg 0 else .bin .div (.reg 0) (.lit (n : Int) 1)
def program (kind : Kind) (n : Nat) : List Instr :=
  [.index 0 .bid, .assign 0 (seedExpr kind), .assign 1 (.lit 0 1), .assign 2 (.lit 0 1),
   .index 1 (.const (firstStart kind : Int)),
   .branch (.lt (.ivar 1) (.const (n : Int))) 10,
   .assign 2 (.un .fromHalf (.load .global 0 (.ivar 1))),
   .assign 0 (.bin (firstOp kind) (.reg 0) (lower (firstTerm kind))),
   .index 1 (.add (.ivar 1) (.const 1)), .jump 5,
   .assign 1 (middleExpr kind n), .assign 0 (.lit 0 1),
   .index 1 (.const (secondStart kind n : Int)),
   .branch (.lt (.ivar 1) (.const (n : Int))) 18,
   .assign 2 (.un .fromHalf (.load .global 0 (.ivar 1))),
   .assign 0 (.bin .add (.reg 0) (lower (secondTerm kind))),
   .index 1 (.add (.ivar 1) (.const 1)), .jump 13,
   .assign 2 (.un .fromHalf (.load .global 0 (.ivar 0))),
   .store .global 1 (.ivar 0) (.un .toHalf (lower (epilogue kind n))), .halt]

def phase1 (kind : Kind) (n : Nat) : Phase :=
  ⟨n,5,10,firstOp kind,firstTerm kind,by cases kind <;> simp [firstTerm,Valid],
   program kind n,rfl,rfl,rfl,rfl,rfl⟩
def phase2 (kind : Kind) (n : Nat) : Phase :=
  ⟨n,13,18,.add,secondTerm kind,by cases kind <;> simp [secondTerm,Valid],
   program kind n,rfl,rfl,rfl,rfl,rfl⟩
def seed (kind : Kind) (ops : Ops α) (input : Nat → Nat → α) : α :=
  if kind=.softmax then ops.fromHalf (input 0 0) else ops.literal 0 1
def context (kind : Kind) (ops : Ops α) (n : Nat) (acc : α) : α :=
  if kind=.softmax then acc else ops.div acc (ops.literal (n : Int) 1)
def firstSum (kind : Kind) (ops : Ops α) (input : Nat → Nat → α) (n : Nat) : α :=
  folded (phase1 kind n) ops input (ops.literal 0 1)
    (firstStart kind) (n-firstStart kind) (seed kind ops input)
def ctx (kind : Kind) (ops : Ops α) (input : Nat → Nat → α) (n : Nat) : α :=
  context kind ops n (firstSum kind ops input n)
def secondSum (kind : Kind) (ops : Ops α) (input : Nat → Nat → α) (n : Nat) : α :=
  folded (phase2 kind n) ops input (ctx kind ops input n)
    (secondStart kind n) (n-secondStart kind n) (ops.literal 0 1)
def result (kind : Kind) (ops : Ops α) (input : Nat → Nat → α) (n t : Nat) : α :=
  ops.toHalf (value ops (ops.fromHalf (input 0 t)) (ctx kind ops input n)
    (secondSum kind ops input n) (epilogue kind n))

def initialized (kind : Kind) (ops : Ops α) (input : Nat → Nat → α) (t : Nat)
    (s : State α) : State α :=
  let s:=setIndex s t 0 (t : Int) 1
  let s:=if kind=.softmax then record s t (LarkUnaryMap.cell 0 0) false else s
  let s:=setReg s t 0 (seed kind ops input) 2
  let s:=setReg s t 1 (ops.literal 0 1) 3
  let s:=setReg s t 2 (ops.literal 0 1) 4
  setIndex s t 1 (firstStart kind : Int) 5
def firstState (kind : Kind) (ops : Ops α) (input : Nat → Nat → α) (n t : Nat)
    (s : State α) : State α :=
  iterate (phase1 kind n) ops input (ops.literal 0 1) t
    (firstStart kind) (n-firstStart kind) (seed kind ops input) (initialized kind ops input t s)
def middle (kind : Kind) (ops : Ops α) (input : Nat → Nat → α) (n t : Nat)
    (s : State α) : State α :=
  let s:=setReg s t 1 (ctx kind ops input n) 11
  let s:=setReg s t 0 (ops.literal 0 1) 12
  setIndex s t 1 (secondStart kind n : Int) 13
def secondState (kind : Kind) (ops : Ops α) (input : Nat → Nat → α) (n t : Nat)
    (s : State α) : State α :=
  iterate (phase2 kind n) ops input (ctx kind ops input n) t
    (secondStart kind n) (n-secondStart kind n) (ops.literal 0 1)
    (middle kind ops input n t (firstState kind ops input n t s))
def after (kind : Kind) (ops : Ops α) (input : Nat → Nat → α) (n t : Nat)
    (s : State α) : State α :=
  let s:=setReg (record (secondState kind ops input n t s) t (LarkUnaryMap.cell 0 t) false)
    t 2 (ops.fromHalf (input 0 t)) 19
  advance {record s t (LarkUnaryMap.cell 1 t) true with
    memory:=fun l=>if l=LarkUnaryMap.cell 1 t then some (result kind ops input n t) else s.memory l}
    t 20
def laneFuel (kind : Kind) (n : Nat) : Nat :=
  5*(n-firstStart kind)+5*(n-secondStart kind n)+13

theorem initialized_eq (kind : Kind) (ops : Ops α) (input : Nat → Nat → α)
    (n w t f : Nat) (s : State α) (hn : 0<n) (ht : t<2147483648)
    (hr : LarkUnaryMap.Reads n input s) (hp : s.pc t=0) :
    runLane ops (LarkUnaryMap.layout n) (LarkUnaryMap.geometry n w) (program kind n) t (f+5) s=
      runLane ops (LarkUnaryMap.layout n) (LarkUnaryMap.geometry n w) (program kind n) t f
        (initialized kind ops input t s) := by
  let s1:=setIndex s t 0 (t : Int) 1
  let loaded:=if kind=.softmax then record s1 t (LarkUnaryMap.cell 0 0) false else s1
  let s2:=setReg loaded t 0 (seed kind ops input) 2
  let s3:=setReg s2 t 1 (ops.literal 0 1) 3
  let s4:=setReg s3 t 2 (ops.literal 0 1) 4
  have h1:=execute_index_of ops (LarkUnaryMap.layout n) (LarkUnaryMap.geometry n w) t 0 1 .bid s
    (t : Int) (by simpa [LarkUnaryMap.geometry,LarkPointwise.geometry,evalIndex] using int32_cast t ht)
    (by omega)
  change execute _ _ _ _ _ s=some s1 at h1
  have hseed : evalExpr ops (LarkUnaryMap.layout n) (LarkUnaryMap.geometry n w) t (seedExpr kind) s1=
      some (seed kind ops input,loaded) := by
    have hr0 : s.memory ⟨.global,0,0,0⟩=some (input 0 0) := hr 0 hn
    cases kind <;> simp [seedExpr,seed,loaded,evalExpr,evalIndex,int32,applyUnary,location,
      LarkUnaryMap.layout,LarkUnaryMap.cell,s1,setIndex,advance,hr0,hn]
  have h2 : execute ops (LarkUnaryMap.layout n) (LarkUnaryMap.geometry n w) t
      (.assign 0 (seedExpr kind)) s1=some s2 := by
    simp only [execute,hseed,bind,pure,Option.bind]
    have hh : s1.pc t+1=2 := by simp [s1,setIndex,advance]
    rw [hh];rfl
  have h3:=execute_pure_of ops (LarkUnaryMap.layout n) (LarkUnaryMap.geometry n w) t 1 3
    (.lit 0 1) s2 (ops.literal 0 1) (by simp [evalExpr]) (by simp [s2,setReg,advance])
  change execute _ _ _ _ _ s2=some s3 at h3
  have h4:=execute_pure_of ops (LarkUnaryMap.layout n) (LarkUnaryMap.geometry n w) t 2 4
    (.lit 0 1) s3 (ops.literal 0 1) (by simp [evalExpr]) (by simp [s3,setReg,advance])
  change execute _ _ _ _ _ s3=some s4 at h4
  have hstart : evalIndex (LarkUnaryMap.geometry n w) t s4 (.const (firstStart kind : Int))=
      some (firstStart kind : Int) := by cases kind <;> rfl
  have h5:=execute_index_of ops (LarkUnaryMap.layout n) (LarkUnaryMap.geometry n w) t 1 5
    (.const (firstStart kind : Int)) s4 (firstStart kind : Int) hstart (by simp [s4,setReg,advance])
  change execute _ _ _ _ _ s4=some (initialized kind ops input t s) at h5
  rw [LarkPointwise.lane_step ops _ _ _ _ _ _ _ _
    (by simp [parked,program,hp]) (by simp [program,hp]) h1]
  rw [LarkPointwise.lane_step ops _ _ _ _ _ _ _ _
    (by simp [parked,program,s1,setIndex,advance]) (by simp [program,s1,setIndex,advance]) h2]
  rw [LarkPointwise.lane_step ops _ _ _ _ _ _ _ _
    (by simp [parked,program,s2,setReg,advance]) (by simp [program,s2,setReg,advance]) h3]
  rw [LarkPointwise.lane_step ops _ _ _ _ _ _ _ _
    (by simp [parked,program,s3,setReg,advance]) (by simp [program,s3,setReg,advance]) h4]
  rw [LarkPointwise.lane_step ops _ _ _ _ _ _ _ _
    (by simp [parked,program,s4,setReg,advance]) (by simp [program,s4,setReg,advance]) h5]

theorem first_memory (kind : Kind) (ops : Ops α) (input : Nat → Nat → α) (n t : Nat)
    (s : State α) : (firstState kind ops input n t s).memory=s.memory := by
  simp only [firstState,iterate_memory]
  cases kind <;> rfl

theorem first_pc (kind : Kind) (ops : Ops α) (input : Nat → Nat → α) (n t u : Nat)
    (s : State α) : (firstState kind ops input n t s).pc u=if u=t then 10 else s.pc u := by
  simp only [firstState,iterate_pc]
  by_cases h : u=t <;> cases kind <;>
    simp [phase1,initialized,setIndex,setReg,record,advance,h]

theorem first_index (kind : Kind) (ops : Ops α) (input : Nat → Nat → α) (n t : Nat)
    (s : State α) : (firstState kind ops input n t s).indices t 0=some (t : Int) := by
  simp only [firstState,iterate_index0]
  cases kind <;> simp [initialized,setIndex,setReg,advance,record]

theorem first_acc (kind : Kind) (ops : Ops α) (input : Nat → Nat → α) (n t : Nat)
    (s : State α) : (firstState kind ops input n t s).regs t 0=some (firstSum kind ops input n) := by
  apply iterate_acc
  cases kind <;> simp [initialized,setIndex,setReg,advance,record]

theorem middle_eq (kind : Kind) (ops : Ops α) (input : Nat → Nat → α)
    (n w t f : Nat) (s : State α) (hb : n<2147483648)
    (hp : s.pc t=10) (ha : s.regs t 0=some (firstSum kind ops input n)) :
    runLane ops (LarkUnaryMap.layout n) (LarkUnaryMap.geometry n w) (program kind n) t (f+3) s=
      runLane ops (LarkUnaryMap.layout n) (LarkUnaryMap.geometry n w) (program kind n) t f
        (middle kind ops input n t s) := by
  let s1:=setReg s t 1 (ctx kind ops input n) 11
  let s2:=setReg s1 t 0 (ops.literal 0 1) 12
  have he : evalExpr ops (LarkUnaryMap.layout n) (LarkUnaryMap.geometry n w) t
      (middleExpr kind n) s=some (ctx kind ops input n,s) := by
    cases kind <;> simp [middleExpr,ctx,context,evalExpr,ha,applyBinary]
  have h1:=execute_pure_of ops (LarkUnaryMap.layout n) (LarkUnaryMap.geometry n w) t 1 11
    (middleExpr kind n) s (ctx kind ops input n) he (by omega)
  change execute _ _ _ _ _ s=some s1 at h1
  have h2:=execute_pure_of ops (LarkUnaryMap.layout n) (LarkUnaryMap.geometry n w) t 0 12
    (.lit 0 1) s1 (ops.literal 0 1) (by simp [evalExpr]) (by simp [s1,setReg,advance])
  change execute _ _ _ _ _ s1=some s2 at h2
  have hs : evalIndex (LarkUnaryMap.geometry n w) t s2 (.const (secondStart kind n : Int))=
      some (secondStart kind n : Int) := by
    exact int32_cast (secondStart kind n) (by cases kind <;> simp [secondStart];exact hb)
  have h3:=execute_index_of ops (LarkUnaryMap.layout n) (LarkUnaryMap.geometry n w) t 1 13
    (.const (secondStart kind n : Int)) s2 (secondStart kind n : Int) hs
    (by simp [s2,setReg,advance])
  rw [LarkPointwise.lane_step ops _ _ _ _ _ _ _ _
    (by simp [parked,program,hp]) (by simp [program,hp]) h1]
  rw [LarkPointwise.lane_step ops _ _ _ _ _ _ _ _
    (by simp [parked,program,s1,setReg,advance]) (by simp [program,s1,setReg,advance]) h2]
  rw [LarkPointwise.lane_step ops _ _ _ _ _ _ _ _
    (by simp [parked,program,s2,setReg,advance]) (by simp [program,s2,setReg,advance]) h3]
  rfl

theorem second_memory (kind : Kind) (ops : Ops α) (input : Nat → Nat → α) (n t : Nat)
    (s : State α) : (secondState kind ops input n t s).memory=s.memory := by
  simp [secondState,iterate_memory,middle,setIndex,setReg,advance,first_memory]

theorem second_pc (kind : Kind) (ops : Ops α) (input : Nat → Nat → α) (n t u : Nat)
    (s : State α) : (secondState kind ops input n t s).pc u=if u=t then 18 else s.pc u := by
  simp only [secondState,iterate_pc]
  by_cases h : u=t <;> simp [phase2,middle,setIndex,setReg,advance,first_pc,h]

theorem second_index (kind : Kind) (ops : Ops α) (input : Nat → Nat → α) (n t : Nat)
    (s : State α) : (secondState kind ops input n t s).indices t 0=some (t : Int) := by
  simp [secondState,iterate_index0,middle,setIndex,setReg,advance,first_index]

theorem second_context (kind : Kind) (ops : Ops α) (input : Nat → Nat → α) (n t : Nat)
    (s : State α) : (secondState kind ops input n t s).regs t 1=some (ctx kind ops input n) := by
  simp [secondState,iterate_context,middle,setIndex,setReg,advance]

theorem second_acc (kind : Kind) (ops : Ops α) (input : Nat → Nat → α) (n t : Nat)
    (s : State α) : (secondState kind ops input n t s).regs t 0=some (secondSum kind ops input n) := by
  apply iterate_acc
  simp [middle,setIndex,setReg,advance]

theorem lane_eq (kind : Kind) (ops : Ops α) (input : Nat → Nat → α)
    (n w t : Nat) (s : State α) (ht : t<n) (hb : n<2147483648)
    (hp : s.pc t=0) (hr : LarkUnaryMap.Reads n input s) :
    runLane ops (LarkUnaryMap.layout n) (LarkUnaryMap.geometry n w) (program kind n) t
      (laneFuel kind n) s=some (after kind ops input n t s) := by
  have hn : 0<n := by omega
  have hf : laneFuel kind n=(5*(n-firstStart kind)+5*(n-secondStart kind n)+8)+5 := by
    unfold laneFuel;omega
  rw [hf,initialized_eq kind ops input n w t _ s hn (by omega) hr hp]
  have hf1 : 5*(n-firstStart kind)+5*(n-secondStart kind n)+8=
      (5*(n-secondStart kind n)+7)+5*(n-firstStart kind)+1 := by omega
  rw [hf1]
  have h1:=LarkFoldPhase.run_eq (phase1 kind n) ops input (ops.literal 0 1) (seed kind ops input)
    w t (n-firstStart kind) (firstStart kind) (5*(n-secondStart kind n)+7)
    (initialized kind ops input t s)
    (by cases kind <;> exact hr)
    (by cases kind <;> simp [initialized,setIndex,setReg,record,advance])
    (by cases kind <;> simp [initialized,setIndex,setReg,record,advance])
    (by cases kind <;> simp [initialized,setIndex,setReg,record,advance])
    (by simp [initialized,setIndex,advance,phase1])
    (by cases kind <;> simp [phase1,firstStart];omega) hb
  change runLane ops (LarkUnaryMap.layout n) (LarkUnaryMap.geometry n w) (program kind n) t _ _=
    runLane ops (LarkUnaryMap.layout n) (LarkUnaryMap.geometry n w) (program kind n) t _
      (firstState kind ops input n t s) at h1
  rw [h1]
  have hfm : 5*(n-secondStart kind n)+7=(5*(n-secondStart kind n)+4)+3 := by omega
  rw [hfm,middle_eq kind ops input n w t _ _ hb (by simp [first_pc]) (first_acc kind ops input n t s)]
  have hf2 : 5*(n-secondStart kind n)+4=3+5*(n-secondStart kind n)+1 := by omega
  rw [hf2]
  have h2:=LarkFoldPhase.run_eq (phase2 kind n) ops input (ctx kind ops input n) (ops.literal 0 1)
    w t (n-secondStart kind n) (secondStart kind n) 3
    (middle kind ops input n t (firstState kind ops input n t s))
    (by simpa [LarkUnaryMap.Reads,middle,setIndex,setReg,advance,first_memory] using hr)
    (by simp [middle,setIndex,advance])
    (by simp [middle,setIndex,setReg,advance])
    (by simp [middle,setIndex,setReg,advance])
    (by simp [middle,setIndex,advance,phase2])
    (by cases kind <;> simp [phase2,secondStart]) hb
  change runLane ops (LarkUnaryMap.layout n) (LarkUnaryMap.geometry n w) (program kind n) t _ _=
    runLane ops (LarkUnaryMap.layout n) (LarkUnaryMap.geometry n w) (program kind n) t _
      (secondState kind ops input n t s) at h2
  rw [h2]
  let s1:=secondState kind ops input n t s
  let s2:=setReg (record s1 t (LarkUnaryMap.cell 0 t) false) t 2 (ops.fromHalf (input 0 t)) 19
  have hm : s1.memory (LarkUnaryMap.cell 0 t)=some (input 0 t) := by rw [second_memory];exact hr t ht
  have hl : location (LarkUnaryMap.layout n) (LarkUnaryMap.geometry n w) t .global 0 (t : Int) false=
      some (LarkUnaryMap.cell 0 t) := by
    have hneg : ¬(t : Int)<0 := by omega
    simp [location,LarkUnaryMap.layout,LarkUnaryMap.cell,hneg,ht]
  have he : evalExpr ops (LarkUnaryMap.layout n) (LarkUnaryMap.geometry n w) t
      (.un .fromHalf (.load .global 0 (.ivar 0))) s1=
      some (ops.fromHalf (input 0 t),record s1 t (LarkUnaryMap.cell 0 t) false) := by
    simp [evalExpr,evalIndex,s1,second_index,hl,hm,applyUnary]
  have he1 : execute ops (LarkUnaryMap.layout n) (LarkUnaryMap.geometry n w) t
      (.assign 2 (.un .fromHalf (.load .global 0 (.ivar 0)))) s1=some s2 := by
    simp only [execute,he,bind,pure,Option.bind]
    have hh : s1.pc t+1=19 := by simp [s1,second_pc]
    rw [hh];rfl
  have hv : Valid (epilogue kind n) := by cases kind <;> simp [epilogue,mean,Valid]
  have hev:=eval_lower ops (LarkUnaryMap.layout n) (LarkUnaryMap.geometry n w) t s2
    (ops.fromHalf (input 0 t)) (ctx kind ops input n) (secondSum kind ops input n) (epilogue kind n) hv
    (by simp [s2,setReg,advance])
    (by simp [s2,setReg,record,advance,s1,second_context])
    (by simp [s2,setReg,record,advance,s1,second_acc])
  have hrole : (Role.output==Role.input)=false := by decide
  have hloc : location (LarkUnaryMap.layout n) (LarkUnaryMap.geometry n w) t .global 1 (t : Int) true=
      some (LarkUnaryMap.cell 1 t) := by
    have hneg : ¬(t : Int)<0 := by omega
    simp [location,LarkUnaryMap.layout,LarkUnaryMap.cell,hneg,ht,hrole]
  have he2 : execute ops (LarkUnaryMap.layout n) (LarkUnaryMap.geometry n w) t
      (.store .global 1 (.ivar 0) (.un .toHalf (lower (epilogue kind n)))) s2=
      some (after kind ops input n t s) := by
    have hi2 : s2.indices t 0=some (t : Int) := by simp [s2,setReg,record,advance,s1,second_index]
    simp only [execute,evalIndex,hi2,bind,pure,Option.bind,hloc]
    simp only [evalExpr,hev,bind,pure,Option.bind,applyUnary]
    have hh : s2.pc t+1=20 := by simp [s2,setReg,advance]
    rw [hh]
    rfl
  rw [LarkPointwise.lane_step ops _ _ _ _ _ _ _ _
    (by simp [parked,program,s1,second_pc]) (by simp [program,s1,second_pc]) he1]
  rw [LarkPointwise.lane_step ops _ _ _ _ _ _ _ _
    (by simp [parked,program,s2,setReg,advance]) (by simp [program,s2,setReg,advance]) he2]
  simp [runLane,parked,program,after,advance]

theorem after_memory (kind : Kind) (ops : Ops α) (input : Nat → Nat → α) (n t : Nat)
    (s : State α) (l : Location) :
    (after kind ops input n t s).memory l=
      if l=LarkUnaryMap.cell 1 t then some (result kind ops input n t) else s.memory l := by
  simp [after,setReg,advance,record,second_memory]

theorem after_pc (kind : Kind) (ops : Ops α) (input : Nat → Nat → α) (n t : Nat)
    (s : State α) (u : Nat) :
    (after kind ops input n t s).pc u=if u=t then 20 else s.pc u := by
  by_cases h : u=t <;> simp [after,setReg,advance,record,second_pc,h]

theorem first_owned (kind : Kind) (ops : Ops α) (input : Nat → Nat → α) (n t : Nat)
    (s : State α) (h : LarkUnaryMap.Owned s.trace) :
    LarkUnaryMap.Owned (firstState kind ops input n t s).trace := by
  apply iterate_owned
  cases kind with
  | rms => exact h
  | layer => exact h
  | softmax => exact owned_read s.trace h t 0 (s.epochs t)

theorem second_owned (kind : Kind) (ops : Ops α) (input : Nat → Nat → α) (n t : Nat)
    (s : State α) (h : LarkUnaryMap.Owned s.trace) :
    LarkUnaryMap.Owned (secondState kind ops input n t s).trace := by
  apply iterate_owned
  exact first_owned kind ops input n t s h

theorem after_owned (kind : Kind) (ops : Ops α) (input : Nat → Nat → α) (n t : Nat)
    (s : State α) (h : LarkUnaryMap.Owned s.trace) :
    LarkUnaryMap.Owned (after kind ops input n t s).trace := by
  have hh:=owned_read _ (second_owned kind ops input n t s h) t t
    ((secondState kind ops input n t s).epochs t)
  intro a ha
  simp only [after,advance,record,setReg,List.mem_cons] at ha
  rcases ha with rfl | ha
  · rfl
  · exact hh a (List.mem_cons.mpr ha)

def profile (kind : Kind) (n : Nat) : LarkUnaryMap.Profile where
  n:=n
  program:=program kind n
  laneFuel:=laneFuel kind n
  haltPc:=20
  halt:=rfl
  value:=fun _ ops input t=>result kind ops input n t
  after:=fun _ ops input t s=>after kind ops input n t s
  afterMemory:=fun _ ops input t s l=>after_memory kind ops input n t s l
  afterPc:=fun _ ops input t s u=>after_pc kind ops input n t s u
  afterOwned:=fun _ ops input t s h=>after_owned kind ops input n t s h
  laneEq:=fun _ ops w t s input ht hb hp hr=>lane_eq kind ops input n w t s ht hb hp hr

theorem correct (kind : Kind) (ops : Ops α) (n w : Nat) (hn : 0<n)
    (hb : n<2147483648) (hw : 0<w) :
    Correct ops (LarkUnaryMap.layout n) (LarkUnaryMap.geometry n w)
      (LarkUnaryMap.fuel (profile kind n)) (program kind n) (LarkUnaryMap.spec (profile kind n) ops) :=
  LarkUnaryMap.correct (profile kind n) ops w hn hb hw

#print axioms lane_eq
#print axioms correct
end LarkNormalization

namespace LarkCertificate
open LarkNonlinear
def profile : LarkUnaryMap.Profile := LarkNormalization.profile .softmax 16384
def layout : Layout := LarkUnaryMap.layout 16384
def geometry : Geometry := LarkUnaryMap.geometry 16384 64
def fuel : Fuel := LarkUnaryMap.fuel profile
def program : List Instr := [(.index 0 .bid), (.assign 0 (.un .fromHalf (.load .global 0 (.const (0))))), (.assign 1 (.lit (0) 1)), (.assign 2 (.lit (0) 1)), (.index 1 (.const (1))), (.branch (.lt (.ivar (1)) (.const (16384))) 10), (.assign 2 (.un .fromHalf (.load .global 0 (.ivar (1))))), (.assign 0 (.bin .max (.reg (0)) (.reg (2)))), (.index 1 (.add (.ivar (1)) (.const (1)))), (.jump 5), (.assign 1 (.reg (0))), (.assign 0 (.lit (0) 1)), (.index 1 (.const (0))), (.branch (.lt (.ivar (1)) (.const (16384))) 18), (.assign 2 (.un .fromHalf (.load .global 0 (.ivar (1))))), (.assign 0 (.bin .add (.reg (0)) (.un .exp (.bin .sub (.reg (2)) (.reg (1)))))), (.index 1 (.add (.ivar (1)) (.const (1)))), (.jump 13), (.assign 2 (.un .fromHalf (.load .global 0 (.ivar (0))))), (.store .global 1 (.ivar (0)) (.un .toHalf (.bin .div (.un .exp (.bin .sub (.reg (2)) (.reg (1)))) (.reg (0))))), .halt]
def spec (ops : Ops α) (input : Nat → Nat → α) : List α := LarkUnaryMap.spec profile ops input
def finalState (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) : State α := LarkUnaryMap.partialState profile ops input outside 16384
theorem segmentation_data : program=LarkNormalization.program .softmax 16384 := by rfl
theorem segmentation (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) :
    runLaunch ops layout geometry fuel program (initial layout input outside)=some (finalState ops input outside) := by
  rw [segmentation_data]
  exact LarkUnaryMap.launch_eq profile ops input outside 64 (by decide) (by decide) (by decide)
theorem race_free (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) :
    raceFree geometry (finalState ops input outside).trace=true := by
  exact LarkUnaryMap.owned_raceFree geometry _ (LarkUnaryMap.partialState_owned profile ops input outside 16384)
theorem segment_equivalence (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) :
    extract layout (finalState ops input outside)=some (spec ops input) := by
  exact LarkUnaryMap.extract_eq profile ops input outside
theorem kernel_eq_spec (ops : Ops α) : Correct ops layout geometry fuel program (spec ops) := by
  intro input outside
  exact ⟨finalState ops input outside,segmentation ops input outside,race_free ops input outside,segment_equivalence ops input outside⟩
theorem kernel_eq_spec_pre (ops : Ops α) (input : Nat → Nat → α) (s : State α) (pre : StdPre layout input s) :
    ∃ final,runLaunch ops layout geometry fuel program s=some final ∧ raceFree geometry final.trace=true ∧ extract layout final=some (spec ops input) := by
  exact correct_from_pre ops layout geometry fuel program (spec ops) (kernel_eq_spec ops) input s pre
#print axioms segmentation_data
#print axioms segmentation
#print axioms race_free
#print axioms segment_equivalence
#print axioms kernel_eq_spec
#print axioms kernel_eq_spec_pre
end LarkCertificate
