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


/-!
Induction for the actual scalar machine's counted dot-product loop and grid.
Profiles supply only input address functions, bounds, and primitive index-evaluation
proofs. No assumed loop summary, execution equality or correctness field is used.
The machine model is unchanged. The conclusion is its existing Correct predicate,
including completion, race freedom and every output, for all inputs/outside memory.
-/
namespace LarkDot
open LarkNonlinear
open LarkReduction
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

structure Profile where
  n : Nat
  k : Nat
  aSize : Nat
  bSize : Nat
  aIndex : Index
  bIndex : Index
  aAddress : Nat → Nat → Nat
  bAddress : Nat → Nat → Nat
  aBound : ∀ t j, t < n → j < k → aAddress t j < aSize
  bBound : ∀ t j, t < n → j < k → bAddress t j < bSize
  aEval : ∀ (α : Type) (g : Geometry) (t j : Nat) (s : State α),
    s.indices t 0 = some (t : Int) → s.indices t 1 = some (j : Int) →
    t < n → j < k → evalIndex g t s aIndex = some ((aAddress t j : Nat) : Int)
  bEval : ∀ (α : Type) (g : Geometry) (t j : Nat) (s : State α),
    s.indices t 0 = some (t : Int) → s.indices t 1 = some (j : Int) →
    t < n → j < k → evalIndex g t s bIndex = some ((bAddress t j : Nat) : Int)

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
     (.un .fromHalf (.load .global 0 p.aIndex))
     (.un .fromHalf (.load .global 1 p.bIndex)))),
   .index 1 (.add (.ivar 1) (.const 1)),
   .jump 3,
   .store .global 2 (.ivar 0) (.un .toHalf (.reg 0)),
   .halt]

def Reads (p : Profile) (input : Nat → Nat → α) (s : State α) : Prop :=
  (∀ i, i < p.aSize → s.memory (cell 0 i) = some (input 0 i)) ∧
  (∀ j, j < p.bSize → s.memory (cell 1 j) = some (input 1 j))

def setIndex (s : State α) (t r : Nat) (v : Int) (pc : Nat) : State α :=
  advance { s with indices := fun u q => if u = t ∧ q = r then some v else s.indices u q } t pc
def setReg (s : State α) (t r : Nat) (v : α) (pc : Nat) : State α :=
  advance { s with regs := fun u q => if u = t ∧ q = r then some v else s.regs u q } t pc

def term (ops : Ops α) (input : Nat → Nat → α) (p : Profile) (t j : Nat) : α :=
  ops.mul (ops.fromHalf (input 0 (p.aAddress t j))) (ops.fromHalf (input 1 (p.bAddress t j)))

def next (ops : Ops α) (input : Nat → Nat → α) (p : Profile) (t j : Nat) (acc : α)
    (s : State α) : State α :=
  let s := advance s t 4
  let s := record (record s t (cell 0 (p.aAddress t j)) false) t (cell 1 (p.bAddress t j)) false
  let s := setReg s t 0 (ops.add acc (term ops input p t j)) 5
  let s := setIndex s t 1 ((j+1 : Nat) : Int) 6
  advance s t 3

def stored (ops : Ops α) (t : Nat) (acc : α) (s : State α) : State α :=
  advance { record s t (cell 2 t) true with
    memory := fun l => if l = cell 2 t then some (ops.toHalf acc) else s.memory l } t 8

def iterate (ops : Ops α) (input : Nat → Nat → α) (p : Profile) (t : Nat) :
    Nat → Nat → α → State α → State α
  | _, 0, acc, s => stored ops t acc (advance s t 7)
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
  ops.toHalf (folded ops input p t 0 p.k (ops.literal 0 1))

theorem matrix_location (p : Profile) (t i : Nat) (g : Geometry) (hi : i < p.aSize) :
    location (layout p) g t .global 0 (i : Int) false = some (cell 0 i) := by
  have hneg : ¬ (i : Int) < 0 := by omega
  simp [location, layout, cell, hneg, hi]

theorem load_matrix (ops : Ops α) (p : Profile) (w t j : Nat) (s : State α)
    (input : Nat → Nat → α) (hr : Reads p input s)
    (hi : s.indices t 0 = some (t : Int)) (hij : s.indices t 1 = some (j : Int))
    (ht : t < p.n) (hj : j < p.k) (_hb : p.n < 2147483648 ∧ p.k < 2147483648) :
    evalExpr ops (layout p) (geometry p w) t
      (.un .fromHalf (.load .global 0 p.aIndex)) s =
      some (ops.fromHalf (input 0 (p.aAddress t j)), record s t (cell 0 (p.aAddress t j)) false) := by
  have ha := p.aBound t j ht hj
  have hix := p.aEval α (geometry p w) t j s hi hij ht hj
  have hl := matrix_location p t (p.aAddress t j) (geometry p w) ha
  simp only [evalExpr, hix, bind, pure, Option.bind, hl, hr.1 _ ha]
  rfl

theorem load_vector (ops : Ops α) (p : Profile) (w t j : Nat) (s : State α)
    (input : Nat → Nat → α) (hr : Reads p input s)
    (hi : s.indices t 0 = some (t : Int)) (hij : s.indices t 1 = some (j : Int))
    (ht : t < p.n) (hj : j < p.k) :
    evalExpr ops (layout p) (geometry p w) t
      (.un .fromHalf (.load .global 1 p.bIndex)) s =
      some (ops.fromHalf (input 1 (p.bAddress t j)), record s t (cell 1 (p.bAddress t j)) false) := by
  have ha := p.bBound t j ht hj
  have hneg : ¬ ((p.bAddress t j : Nat) : Int) < 0 := by omega
  have hix := p.bEval α (geometry p w) t j s hi hij ht hj
  have hl : location (layout p) (geometry p w) t .global 1
      ((p.bAddress t j : Nat) : Int) false = some (cell 1 (p.bAddress t j)) := by
    simp [location, layout, cell, hneg, ha]
  simp only [evalExpr, hix, bind, pure, Option.bind, hl, hr.2 _ ha]
  rfl

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
        (.un .fromHalf (.load .global 0 p.aIndex))
        (.un .fromHalf (.load .global 1 p.bIndex)))) s =
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
        (.un .fromHalf (.load .global 0 p.aIndex))
        (.un .fromHalf (.load .global 1 p.bIndex))))) s =
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
      (.store .global 2 (.ivar 0) (.un .toHalf (.reg 0))) s = some (stored ops t acc s) := by
  have hneg : ¬ (t : Int) < 0 := by omega
  have hrole : (Role.output == Role.input) = false := by decide
  have hl : location (layout p) (geometry p w) t .global 2 (t : Int) true =
      some (cell 2 t) := by simp [location, layout, cell, hneg, ht, hrole]
  have he : evalExpr ops (layout p) (geometry p w) t (.un .toHalf (.reg 0)) s =
      some (ops.toHalf acc, s) := by simp [evalExpr, hacc, applyUnary]
  simp only [execute, evalIndex, hi, bind, pure, Option.bind, hl, he, hp]
  rfl

theorem loop_done (ops : Ops α) (p : Profile) (w t : Nat) (s : State α) (acc : α)
    (hi : s.indices t 0 = some (t : Int)) (hij : s.indices t 1 = some (p.k : Int))
    (hacc : s.regs t 0 = some acc) (hp : s.pc t = 3)
    (ht : t < p.n) (hk : p.k < 2147483648) :
    runLane ops (layout p) (geometry p w) (program p) t 3 s =
      some (stored ops t acc (advance s t 7)) := by
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
      if l = cell 2 t then some (ops.toHalf (folded ops input p t j r acc)) else s.memory l := by
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
  (List.range p.n).map (fun t => ops.toHalf (dotSpec ops input p t))

theorem folded_eq_list (ops : Ops α) (input : Nat → Nat → α) (p : Profile) (t r j : Nat) (acc : α) :
    folded ops input p t j r acc =
      (List.range' j r).foldl (fun acc z => ops.add acc (term ops input p t z)) acc := by
  induction r generalizing j acc with
  | zero => rfl
  | succ r ih =>
      rw [folded, List.range'_succ, List.foldl_cons]
      exact ih (j+1) _

theorem result_eq_dot (ops : Ops α) (input : Nat → Nat → α) (p : Profile) (t : Nat) :
    result ops input p t = ops.toHalf (dotSpec ops input p t) := by
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

end LarkDot


/-! Row-major scalar GEMM: index/address proofs instantiate the real counted loop. -/
namespace LarkMatrix
open LarkNonlinear LarkReduction
set_option maxRecDepth 4000
set_option maxHeartbeats 20000000

def leftIndex (n k : Nat) : Index :=
  .add (.mul (.div (.ivar 0) (.const (n : Int))) (.const (k : Int))) (.ivar 1)
def rightIndex (n : Nat) : Index :=
  .add (.mul (.ivar 1) (.const (n : Int))) (.mod (.ivar 0) (.const (n : Int)))
def leftAddress (n k t j : Nat) : Nat := (t/n)*k+j
def rightAddress (n t j : Nat) : Nat := j*n+t%n

theorem left_bound (m n k t j : Nat) (hn : 0<n) (ht : t<m*n) (hj : j<k) :
    leftAddress n k t j < m*k := by
  have hrow : t/n<m := (Nat.div_lt_iff_lt_mul hn).mpr ht
  exact address_bound m k (t/n) j hrow hj

theorem right_bound (n k t j : Nat) (hn : 0<n) (hj : j<k) :
    rightAddress n t j < k*n := by
  exact address_bound k n j (t%n) hj (Nat.mod_lt t hn)

theorem eval_div_nat (g : Geometry) (t : Nat) (s : State α) (a b : Index)
    (x y : Nat) (ha : evalIndex g t s a = some (x : Int))
    (hb : evalIndex g t s b = some (y : Int)) (hy : 0<y) :
    evalIndex g t s (.div a b) = some ((x/y : Nat) : Int) := by
  have h0 : ¬ ((y : Int)=0 ∨ (x : Int)<0 ∨ (y : Int)<0) := by omega
  simp only [evalIndex, ha, hb, bind, pure, Option.bind, h0, ↓reduceIte]
  exact congrArg some (Int.ofNat_ediv x y).symm

theorem eval_mod_nat (g : Geometry) (t : Nat) (s : State α) (a b : Index)
    (x y : Nat) (ha : evalIndex g t s a = some (x : Int))
    (hb : evalIndex g t s b = some (y : Int)) (hy : 0<y) :
    evalIndex g t s (.mod a b) = some ((x%y : Nat) : Int) := by
  have h0 : ¬ ((y : Int)=0 ∨ (x : Int)<0 ∨ (y : Int)<0) := by omega
  simp only [evalIndex, ha, hb, bind, pure, Option.bind, h0, ↓reduceIte]
  exact congrArg some (Int.ofNat_emod x y).symm

theorem left_eval (g : Geometry) (m n k t j : Nat) (s : State α)
    (hi : s.indices t 0 = some (t : Int)) (hij : s.indices t 1 = some (j : Int))
    (hm : 0<m) (hn : 0<n) (ht : t<m*n) (hj : j<k)
    (hnb : n<2147483648) (hb : m*k<2147483648) :
    evalIndex g t s (leftIndex n k) = some ((leftAddress n k t j : Nat) : Int) := by
  have ha := left_bound m n k t j hn ht hj
  have hk := k_bound m k hm hb
  have hdiv := eval_div_nat g t s (.ivar 0) (.const (n : Int)) t n hi
    (int32_cast n hnb) hn
  have hmul : evalIndex g t s (.mul (.div (.ivar 0) (.const (n : Int)))
      (.const (k : Int))) = some (((t/n)*k : Nat) : Int) :=
    eval_mul_of g t s _ _ ((t/n : Nat) : Int) (k : Int) (((t/n)*k : Nat) : Int)
      hdiv (int32_cast k hk) (Eq.trans
        (congrArg int32 (Int.natCast_mul (t/n) k).symm)
        (int32_cast ((t/n)*k) (by unfold leftAddress at ha; omega)))
  exact eval_add_of g t s _ _ (((t/n)*k : Nat) : Int) (j : Int)
    ((leftAddress n k t j : Nat) : Int) hmul hij (Eq.trans
      (congrArg int32 (Int.natCast_add ((t/n)*k) j).symm)
      (int32_cast (leftAddress n k t j) (by omega)))

theorem right_eval (g : Geometry) (n k t j : Nat) (s : State α)
    (hi : s.indices t 0 = some (t : Int)) (hij : s.indices t 1 = some (j : Int))
    (hn : 0<n) (hj : j<k) (hnb : n<2147483648) (hb : k*n<2147483648) :
    evalIndex g t s (rightIndex n) = some ((rightAddress n t j : Nat) : Int) := by
  have ha := right_bound n k t j hn hj
  have hmod := eval_mod_nat g t s (.ivar 0) (.const (n : Int)) t n hi
    (int32_cast n hnb) hn
  have hmul : evalIndex g t s (.mul (.ivar 1) (.const (n : Int))) =
      some ((j*n : Nat) : Int) :=
    eval_mul_of g t s _ _ (j : Int) (n : Int) ((j*n : Nat) : Int) hij
      (int32_cast n hnb) (Eq.trans (congrArg int32 (Int.natCast_mul j n).symm)
        (int32_cast (j*n) (by unfold rightAddress at ha; omega)))
  exact eval_add_of g t s _ _ ((j*n : Nat) : Int) ((t%n : Nat) : Int)
    ((rightAddress n t j : Nat) : Int) hmul hmod (Eq.trans
      (congrArg int32 (Int.natCast_add (j*n) (t%n)).symm)
      (int32_cast (rightAddress n t j) (by omega)))

def profile (m n k : Nat) (hm : 0<m) (hn : 0<n)
    (hnb : n<2147483648) (ha : m*k<2147483648) (hb : k*n<2147483648) : LarkDot.Profile :=
  { n := m*n, k := k, aSize := m*k, bSize := k*n,
    aIndex := leftIndex n k, bIndex := rightIndex n,
    aAddress := leftAddress n k, bAddress := rightAddress n,
    aBound := fun t j ht hj => left_bound m n k t j hn ht hj,
    bBound := fun t j _ hj => right_bound n k t j hn hj,
    aEval := fun _ g t j s hi hij ht hj => left_eval g m n k t j s hi hij hm hn ht hj hnb ha,
    bEval := fun _ g t j s hi hij _ hj => right_eval g n k t j s hi hij hn hj hnb hb }

theorem correct (ops : Ops α) (m n k w : Nat) (hm : 0<m) (hn : 0<n) (hk : 0<k)
    (hnb : n<2147483648) (ha : m*k<2147483648) (hb : k*n<2147483648)
    (hc : m*n<2147483648) (hw : 0<w) :
    let p := profile m n k hm hn hnb ha hb
    Correct ops (LarkDot.layout p) (LarkDot.geometry p w) (LarkDot.fuel p)
      (LarkDot.program p) (LarkDot.matrixSpec ops p) := by
  exact LarkDot.matrix_correct ops (profile m n k hm hn hnb ha hb) w
    (Nat.mul_pos hm hn) hk ⟨hc, k_bound m k hm ha⟩ hw

def batchLeftIndex (m n k : Nat) : Index :=
  .add (.mul (.div (.ivar 0) (.const ((m*n : Nat) : Int))) (.const ((m*k : Nat) : Int)))
    (.add (.mul (.mod (.div (.ivar 0) (.const (n : Int))) (.const (m : Int)))
      (.const (k : Int))) (.ivar 1))
def batchRightIndex (m n k : Nat) : Index :=
  .add (.mul (.div (.ivar 0) (.const ((m*n : Nat) : Int))) (.const ((k*n : Nat) : Int)))
    (rightIndex n)
def batchLeftAddress (m n k t j : Nat) : Nat := (t/(m*n))*(m*k)+((t/n)%m)*k+j
def batchRightAddress (m n k t j : Nat) : Nat := (t/(m*n))*(k*n)+(j*n+t%n)

theorem batch_left_bound (b m n k t j : Nat) (hm : 0<m) (hn : 0<n)
    (ht : t<b*(m*n)) (hj : j<k) : batchLeftAddress m n k t j < b*(m*k) := by
  have hbatch : t/(m*n)<b := (Nat.div_lt_iff_lt_mul (Nat.mul_pos hm hn)).mpr ht
  have hrow := Nat.mod_lt (t/n) hm
  have hinner := address_bound m k ((t/n)%m) j hrow hj
  have houter := address_bound b (m*k) (t/(m*n)) (((t/n)%m)*k+j) hbatch hinner
  simpa [batchLeftAddress, Nat.add_assoc] using houter

theorem batch_right_bound (b m n k t j : Nat) (hm : 0<m) (hn : 0<n)
    (ht : t<b*(m*n)) (hj : j<k) : batchRightAddress m n k t j < b*(k*n) := by
  have hbatch : t/(m*n)<b := (Nat.div_lt_iff_lt_mul (Nat.mul_pos hm hn)).mpr ht
  have hinner : j*n+t%n<k*n := right_bound n k t j hn hj
  change (t/(m*n))*(k*n)+(j*n+t%n)<b*(k*n)
  exact address_bound b (k*n) (t/(m*n)) (j*n+t%n) hbatch hinner

theorem eval_mul_nat (g : Geometry) (t : Nat) (s : State α) (a b : Index)
    (x y : Nat) (ha : evalIndex g t s a = some (x : Int))
    (hb : evalIndex g t s b = some (y : Int)) (hxy : x*y<2147483648) :
    evalIndex g t s (.mul a b) = some ((x*y : Nat) : Int) :=
  eval_mul_of g t s a b (x : Int) (y : Int) ((x*y : Nat) : Int) ha hb
    (Eq.trans (congrArg int32 (Int.natCast_mul x y).symm) (int32_cast (x*y) hxy))

theorem eval_add_nat (g : Geometry) (t : Nat) (s : State α) (a b : Index)
    (x y : Nat) (ha : evalIndex g t s a = some (x : Int))
    (hb : evalIndex g t s b = some (y : Int)) (hxy : x+y<2147483648) :
    evalIndex g t s (.add a b) = some ((x+y : Nat) : Int) :=
  eval_add_of g t s a b (x : Int) (y : Int) ((x+y : Nat) : Int) ha hb
    (Eq.trans (congrArg int32 (Int.natCast_add x y).symm) (int32_cast (x+y) hxy))

theorem batch_left_eval (g : Geometry) (b m n k t j : Nat) (s : State α)
    (hi : s.indices t 0 = some (t : Int)) (hij : s.indices t 1 = some (j : Int))
    (hb : 0<b) (hm : 0<m) (hn : 0<n) (ht : t<b*(m*n)) (hj : j<k)
    (hc : b*(m*n)<2147483648) (ha : b*(m*k)<2147483648) :
    evalIndex g t s (batchLeftIndex m n k) =
      some ((batchLeftAddress m n k t j : Nat) : Int) := by
  have hmn := k_bound b (m*n) hb hc
  have hmk := k_bound b (m*k) hb ha
  have hmb := k_bound n m hn (by simpa [Nat.mul_comm] using hmn)
  have hnb := k_bound m n hm hmn
  have hkb := k_bound m k hm hmk
  have haddr := batch_left_bound b m n k t j hm hn ht hj
  have hd := eval_div_nat g t s (.ivar 0) (.const ((m*n : Nat) : Int)) t (m*n)
    hi (int32_cast (m*n) hmn) (Nat.mul_pos hm hn)
  have houter := eval_mul_nat g t s _ (.const ((m*k : Nat) : Int)) (t/(m*n)) (m*k) hd (int32_cast (m*k) hmk)
    (by unfold batchLeftAddress at haddr; omega)
  have hr := eval_div_nat g t s (.ivar 0) (.const (n : Int)) t n hi (int32_cast n hnb) hn
  have hrm := eval_mod_nat g t s _ (.const (m : Int)) (t/n) m hr (int32_cast m hmb) hm
  have hinner := address_bound m k ((t/n)%m) j (Nat.mod_lt (t/n) hm) hj
  have hrk := eval_mul_nat g t s _ (.const (k : Int)) ((t/n)%m) k hrm (int32_cast k hkb)
    (by omega)
  have hsum := eval_add_nat g t s _ (.ivar 1) (((t/n)%m)*k) j hrk hij (by omega)
  have h := eval_add_nat g t s _ _ ((t/(m*n))*(m*k)) (((t/n)%m)*k+j) houter hsum
    (by unfold batchLeftAddress at haddr; omega)
  simpa only [batchLeftIndex, batchLeftAddress, Nat.add_assoc] using h

theorem batch_right_eval (g : Geometry) (b m n k t j : Nat) (s : State α)
    (hi : s.indices t 0 = some (t : Int)) (hij : s.indices t 1 = some (j : Int))
    (hb : 0<b) (hm : 0<m) (hn : 0<n) (ht : t<b*(m*n)) (hj : j<k)
    (hc : b*(m*n)<2147483648) (hba : b*(k*n)<2147483648) :
    evalIndex g t s (batchRightIndex m n k) =
      some ((batchRightAddress m n k t j : Nat) : Int) := by
  have hmn := k_bound b (m*n) hb hc
  have hkn := k_bound b (k*n) hb hba
  have hnb := k_bound m n hm hmn
  have haddr := batch_right_bound b m n k t j hm hn ht hj
  have hd := eval_div_nat g t s (.ivar 0) (.const ((m*n : Nat) : Int)) t (m*n)
    hi (int32_cast (m*n) hmn) (Nat.mul_pos hm hn)
  have houter := eval_mul_nat g t s _ (.const ((k*n : Nat) : Int)) (t/(m*n)) (k*n) hd (int32_cast (k*n) hkn)
    (by unfold batchRightAddress at haddr; omega)
  have hr := right_eval g n k t j s hi hij hn hj hnb hkn
  exact eval_add_nat g t s _ _ ((t/(m*n))*(k*n)) (j*n+t%n) houter hr (by unfold batchRightAddress at haddr; omega)

def batchProfile (b m n k : Nat) (hb : 0<b) (hm : 0<m) (hn : 0<n)
    (hc : b*(m*n)<2147483648) (ha : b*(m*k)<2147483648)
    (hba : b*(k*n)<2147483648) : LarkDot.Profile :=
  { n := b*(m*n), k := k, aSize := b*(m*k), bSize := b*(k*n),
    aIndex := batchLeftIndex m n k, bIndex := batchRightIndex m n k,
    aAddress := batchLeftAddress m n k, bAddress := batchRightAddress m n k,
    aBound := fun t j ht hj => batch_left_bound b m n k t j hm hn ht hj,
    bBound := fun t j ht hj => batch_right_bound b m n k t j hm hn ht hj,
    aEval := fun _ g t j s hi hij ht hj => batch_left_eval g b m n k t j s hi hij hb hm hn ht hj hc ha,
    bEval := fun _ g t j s hi hij ht hj => batch_right_eval g b m n k t j s hi hij hb hm hn ht hj hc hba }

#print axioms left_eval
#print axioms right_eval
#print axioms correct
#print axioms batch_left_eval
#print axioms batch_right_eval
end LarkMatrix


/-!
The actual lane/warp/block/grid folds for a launch whose lanes independently
finish at one halt. A kernel supplies a proved lane simulation and invariant;
this library composes them over every thread, including partial final warps.
It does not assume race freedom, output correctness, or the lane simulation.
-/
namespace LarkScalarLaunch
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 20000000

def fuel (lane : Nat) : Fuel := ⟨lane, 1, 1, 1⟩

def DonePreserved (halt : Nat) (before after : State α) : Prop :=
  ∀ t, before.pc t = halt → after.pc t = halt

theorem fold_progress (xs : List ι) (step : State α → ι → Option (State α))
    (post : State α → ι → State α) (targets : ι → List Nat)
    (I : State α → Prop) (halt : Nat) (s : State α) (hs : I s)
    (contract : ∀ k ∈ xs, ∀ st, I st →
      step st k = some (post st k) ∧ I (post st k) ∧
      (∀ t ∈ targets k, (post st k).pc t = halt) ∧
      DonePreserved halt st (post st k)) :
    xs.foldlM step s = some (xs.foldl post s) ∧ I (xs.foldl post s) ∧
    (∀ k ∈ xs, ∀ t ∈ targets k, (xs.foldl post s).pc t = halt) ∧
    DonePreserved halt s (xs.foldl post s) := by
  induction xs generalizing s with
  | nil => exact ⟨rfl, hs, by simp, by intro t ht; exact ht⟩
  | cons k ks ih =>
    obtain ⟨he, hi, hd, hm⟩ := contract k (by simp) s hs
    have tail := ih (post s k) hi (by
      intro j hj st hst
      exact contract j (by simp [hj]) st hst)
    refine ⟨?_, tail.2.1, ?_, ?_⟩
    · simpa only [List.foldlM_cons, he, Option.some_bind, List.foldl_cons] using tail.1
    · intro j hj t ht
      rcases List.mem_cons.mp hj with rfl | hj
      · exact tail.2.2.2 t (hd t ht)
      · exact tail.2.2.1 j hj t ht
    · intro t ht
      exact tail.2.2.2 t (hm t ht)

theorem converged_halt (p : List Instr) (halt : Nat) (ts : List Nat) (s : State α)
    (stop : p[halt]? = some .halt) (hne : ts ≠ [])
    (done : ∀ t ∈ ts, s.pc t = halt) : converged p ts s = some .halt := by
  cases ts with
  | nil => contradiction
  | cons t ts =>
    have ht := done t (by simp)
    have hall : (t :: ts).all (fun u => s.pc u == s.pc t) = true := by
      apply List.all_eq_true.mpr
      intro u hu
      simp [done u hu, ht]
    have hall' : (t :: ts).all (fun u => s.pc u == halt) = true := by simpa [ht] using hall
    simp only [converged, List.head?_cons, bind, pure, Option.bind, hall, ↓reduceIte,
      parked, ht, stop, hall']

theorem warpCount_member (block width j : Nat) (hw : 0 < width) (hj : j < block) :
    j / width < (block + width - 1) / width := by
  have hmul := Nat.div_mul_le_self j width
  have hle : (j / width + 1) * width ≤ block + width - 1 := by
    simp only [Nat.add_mul, Nat.one_mul]
    omega
  have hq := (Nat.le_div_iff_mul_le hw).mpr hle
  omega

theorem warpStart_bound (block width w : Nat) (hw : 0 < width)
    (hh : w < (block + width - 1) / width) : w * width < block := by
  have hle : w + 1 ≤ (block + width - 1) / width := by omega
  have hm := (Nat.le_div_iff_mul_le hw).mp hle
  simp only [Nat.add_mul, Nat.one_mul] at hm
  omega

theorem warpThreads_ne (g : Geometry) (b w : Nat) (hw : 0 < g.warp)
    (hh : w < (g.block + g.warp - 1) / g.warp) : warpThreads g b w ≠ [] := by
  have hb := warpStart_bound g.block g.warp w hw hh
  have hm : b * g.block + w * g.warp ∈ warpThreads g b w := by
    apply List.mem_map.mpr
    refine ⟨w * g.warp, ?_, rfl⟩
    apply List.mem_filter.mpr
    exact ⟨List.mem_range.mpr hb, by simp [Nat.mul_div_cancel w hw]⟩
  intro he
  simp [he] at hm

theorem blockThreads_ne (g : Geometry) (b : Nat) (hb : 0 < g.block) :
    blockThreads g b ≠ [] := by
  have hm : b * g.block + 0 ∈ blockThreads g b := by
    exact List.mem_map.mpr ⟨0, List.mem_range.mpr hb, rfl⟩
  intro he
  simp [he] at hm

theorem warpThreads_subset (g : Geometry) (b w t : Nat)
    (ht : t ∈ warpThreads g b w) : t ∈ blockThreads g b := by
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ht
  exact List.mem_map.mpr ⟨j, (List.mem_filter.mp hj).1, rfl⟩

theorem blockThreads_bound (g : Geometry) (b t : Nat) (hb : b < g.grid)
    (ht : t ∈ blockThreads g b) : t < g.grid * g.block := by
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ht
  have hj' := List.mem_range.mp hj
  have hm := Nat.mul_le_mul_right g.block (show b + 1 ≤ g.grid by omega)
  simp only [Nat.add_mul, Nat.one_mul] at hm
  omega

theorem blockThreads_covered (g : Geometry) (b t : Nat) (hw : 0 < g.warp)
    (ht : t ∈ blockThreads g b) :
    ∃ w ∈ List.range ((g.block + g.warp - 1) / g.warp), t ∈ warpThreads g b w := by
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ht
  refine ⟨j / g.warp, List.mem_range.mpr (warpCount_member _ _ _ hw (List.mem_range.mp hj)), ?_⟩
  apply List.mem_map.mpr
  exact ⟨j, List.mem_filter.mpr ⟨hj, by simp⟩, rfl⟩

theorem launchThreads_covered (g : Geometry) (t : Nat) (hb : 0 < g.block)
    (ht : t < g.grid * g.block) :
    ∃ b ∈ List.range g.grid, t ∈ blockThreads g b := by
  have hd : t / g.block < g.grid := (Nat.div_lt_iff_lt_mul hb).mpr ht
  refine ⟨t / g.block, List.mem_range.mpr hd, ?_⟩
  apply List.mem_map.mpr
  refine ⟨t % g.block, List.mem_range.mpr (Nat.mod_lt t hb), ?_⟩
  simpa [Nat.mul_comm] using Nat.div_add_mod t g.block

def LaneContract (ops : Ops α) (l : Layout) (g : Geometry) (lane halt : Nat)
    (p : List Instr) (post : State α → Nat → State α) (I : State α → Prop) : Prop :=
  ∀ s, I s → ∀ t, t < g.grid * g.block →
    runLane ops l g p t lane s = some (post s t) ∧ I (post s t) ∧
    (post s t).pc t = halt ∧ DonePreserved halt s (post s t)

def warpPost (g : Geometry) (post : State α → Nat → State α) (b w : Nat)
    (s : State α) : State α := (warpThreads g b w).foldl post s
def blockPost (g : Geometry) (post : State α → Nat → State α) (b : Nat)
    (s : State α) : State α :=
  (List.range ((g.block + g.warp - 1) / g.warp)).foldl
    (fun s w => warpPost g post b w s) s
def launchPost (g : Geometry) (post : State α → Nat → State α) (s : State α) : State α :=
  (List.range g.grid).foldl (fun s b => blockPost g post b s) s

theorem warp_simulation (ops : Ops α) (l : Layout) (g : Geometry) (lane halt : Nat)
    (p : List Instr) (post : State α → Nat → State α) (I : State α → Prop)
    (stop : p[halt]? = some .halt) (contract : LaneContract ops l g lane halt p post I)
    (s : State α) (hs : I s) (ts : List Nat) (hne : ts ≠ [])
    (bound : ∀ t ∈ ts, t < g.grid * g.block) :
    runWarp ops l g (fuel lane) p ts 1 s = some (ts.foldl post s) ∧
    I (ts.foldl post s) ∧ (∀ t ∈ ts, (ts.foldl post s).pc t = halt) ∧
    DonePreserved halt s (ts.foldl post s) := by
  have hf := fold_progress ts (fun s t => runLane ops l g p t lane s) post
    (fun t => [t]) I halt s hs (by
      intro t ht st hst
      obtain ⟨he, hi, hd, hm⟩ := contract st hst t (bound t ht)
      exact ⟨he, hi, by simpa using hd, hm⟩)
  have hd : ∀ t ∈ ts, (ts.foldl post s).pc t = halt := by
    intro t ht
    exact hf.2.2.1 t ht t (by simp)
  refine ⟨?_, hf.2.1, hd, hf.2.2.2⟩
  simp only [runWarp, fuel, hf.1, bind, pure, Option.bind,
    converged_halt p halt ts _ stop hne hd]
  rfl

theorem block_simulation (ops : Ops α) (l : Layout) (g : Geometry) (lane halt : Nat)
    (p : List Instr) (post : State α → Nat → State α) (I : State α → Prop)
    (stop : p[halt]? = some .halt) (contract : LaneContract ops l g lane halt p post I)
    (hbpos : 0 < g.block) (hw : 0 < g.warp) (b : Nat) (hb : b < g.grid)
    (s : State α) (hs : I s) :
    runBlock ops l g (fuel lane) p b 1 s = some (blockPost g post b s) ∧
    I (blockPost g post b s) ∧ (∀ t ∈ blockThreads g b, (blockPost g post b s).pc t = halt) ∧
    DonePreserved halt s (blockPost g post b s) := by
  have hf := fold_progress (List.range ((g.block + g.warp - 1) / g.warp))
    (fun s w => runWarp ops l g (fuel lane) p (warpThreads g b w) 1 s)
    (fun s w => warpPost g post b w s) (warpThreads g b) I halt s hs (by
      intro w hw' st hst
      exact warp_simulation ops l g lane halt p post I stop contract st hst
        (warpThreads g b w) (warpThreads_ne g b w hw (List.mem_range.mp hw'))
        (by intro t ht; exact blockThreads_bound g b t hb (warpThreads_subset g b w t ht)))
  have hd : ∀ t ∈ blockThreads g b, (blockPost g post b s).pc t = halt := by
    intro t ht
    obtain ⟨w, hw', hwt⟩ := blockThreads_covered g b t hw ht
    exact hf.2.2.1 w hw' t hwt
  refine ⟨?_, hf.2.1, hd, hf.2.2.2⟩
  have he : (List.range ((g.block + g.warp - 1) / g.warp)).foldlM
      (fun s w => runWarp ops l g (fuel lane) p (warpThreads g b w) 1 s) s =
      some (blockPost g post b s) := hf.1
  simp only [fuel] at he
  simp only [runBlock, fuel, he, bind, pure, Option.bind,
    converged_halt p halt (blockThreads g b) _ stop (blockThreads_ne g b hbpos) hd]
  rfl

theorem launch_simulation (ops : Ops α) (l : Layout) (g : Geometry) (lane halt : Nat)
    (p : List Instr) (post : State α → Nat → State α) (I : State α → Prop)
    (stop : p[halt]? = some .halt) (contract : LaneContract ops l g lane halt p post I)
    (hg : 0 < g.grid) (hb : 0 < g.block) (hw : 0 < g.warp)
    (s : State α) (hs : I s) :
    runLaunch ops l g (fuel lane) p s = some (launchPost g post s) ∧
    I (launchPost g post s) ∧ (∀ t, t < g.grid * g.block → (launchPost g post s).pc t = halt) := by
  have hf := fold_progress (List.range g.grid)
    (fun s b => runBlock ops l g (fuel lane) p b 1 s)
    (fun s b => blockPost g post b s) (blockThreads g) I halt s hs (by
      intro b hb' st hst
      exact block_simulation ops l g lane halt p post I stop contract hb hw b
        (List.mem_range.mp hb') st hst)
  have hd : ∀ t, t < g.grid * g.block → (launchPost g post s).pc t = halt := by
    intro t ht
    obtain ⟨b, hb', hbt⟩ := launchThreads_covered g t hb ht
    exact hf.2.2.1 b hb' t hbt
  have hne : List.range (g.grid * g.block) ≠ [] := by
    intro he
    have hh := congrArg List.length he
    simp at hh
    have := Nat.mul_pos hg hb
    omega
  refine ⟨?_, hf.2.1, hd⟩
  have he : (List.range g.grid).foldlM
      (fun s b => runBlock ops l g (fuel lane) p b 1 s) s =
      some (launchPost g post s) := hf.1
  simp only [fuel] at he
  simp only [runLaunch, show g.grid ≠ 0 by omega, show g.block ≠ 0 by omega,
    show g.warp ≠ 0 by omega, false_or, ↓reduceIte, fuel, runGrid, he,
    bind, pure, Option.bind,
    converged_halt p halt (List.range (g.grid * g.block)) _ stop hne
      (by intro t ht; exact hd t (List.mem_range.mp ht))]
  rfl

#print axioms launch_simulation
end LarkScalarLaunch


/-! Scalar SiLU-and-mul with the upstream row/block/strided-loop organization. -/
namespace LarkSilu
open LarkNonlinear LarkReduction
set_option maxRecDepth 10000
set_option maxHeartbeats 20000000

structure Shape where
  rows : Nat
  width : Nat
  block : Nat
  warp : Nat
  rowsPos : 0 < rows
  widthPos : 0 < width
  blockPos : 0 < block
  warpPos : 0 < warp
  blockLe : block ≤ width
  dataBound : rows * (2 * width) < 2147483648

def layout (p : Shape) : Layout :=
  ⟨[⟨.output, p.rows * p.width⟩, ⟨.input, p.rows * (2 * p.width)⟩], [], []⟩
def geometry (p : Shape) : Geometry := ⟨p.rows, p.block, p.warp⟩
def fuel (p : Shape) : Fuel := LarkScalarLaunch.fuel (7 * p.width + 4)
def cell (b i : Nat) : Location := ⟨.global, 0, b, i⟩
def aAddress (p : Shape) (row col : Nat) : Nat := (row * 2) * p.width + col
def bAddress (p : Shape) (row col : Nat) : Nat := aAddress p row col + p.width
def oAddress (p : Shape) (row col : Nat) : Nat := row * p.width + col
def owner (p : Shape) (row col : Nat) : Nat := row * p.block + col % p.block
def aIndex (p : Shape) : Index :=
  .add (.mul (.mul (.ivar 0) (.const 2)) (.const (p.width : Int))) (.ivar 1)
def bIndex (p : Shape) : Index := .add (aIndex p) (.const (p.width : Int))
def oIndex (p : Shape) : Index :=
  .add (.mul (.ivar 0) (.const (p.width : Int))) (.ivar 1)
def activationExpr : Expr :=
  .un .fromHalf (.un .toHalf (.bin .div (.reg 0)
    (.bin .add (.lit 1 1) (.un .exp (.bin .mul
      (.bin .sub (.lit 0 1) (.reg 0)) (.lit 1 1))))))
def outputExpr : Expr := .un .toHalf (.bin .mul (.reg 2) (.bin .add (.reg 1) (.lit 0 1)))
def program (p : Shape) : List Instr :=
  [.index 0 .bid, .index 1 .tid,
   .branch (.lt (.ivar 1) (.const (p.width : Int))) 9,
   .assign 0 (.un .fromHalf (.load .global 1 (aIndex p))),
   .assign 1 (.un .fromHalf (.load .global 1 (bIndex p))),
   .assign 2 activationExpr,
   .store .global 0 (oIndex p) outputExpr,
   .index 1 (.add (.ivar 1) .bdim), .jump 2, .halt]

def activation (ops : Ops α) (x : α) : α :=
  ops.fromHalf (ops.toHalf (ops.div x (ops.add (ops.literal 1 1)
    (ops.exp (ops.mul (ops.sub (ops.literal 0 1) x) (ops.literal 1 1))))))
def result (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row col : Nat) : α :=
  ops.toHalf (ops.mul (activation ops (ops.fromHalf (input 1 (aAddress p row col))))
    (ops.add (ops.fromHalf (input 1 (bAddress p row col))) (ops.literal 0 1)))
def Reads (p : Shape) (input : Nat → Nat → α) (s : State α) : Prop :=
  ∀ i, i < p.rows * (2 * p.width) → s.memory (cell 1 i) = some (input 1 i)

def initialized (p : Shape) (t : Nat) (s : State α) : State α :=
  setIndex (setIndex s t 0 ((t / p.block : Nat) : Int) 1)
    t 1 ((t % p.block : Nat) : Int) 2
def cycleState (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t row col : Nat) (s : State α) : State α :=
  let s := advance s t 3
  let s := setReg (record s t (cell 1 (aAddress p row col)) false) t 0
    (ops.fromHalf (input 1 (aAddress p row col))) 4
  let s := setReg (record s t (cell 1 (bAddress p row col)) false) t 1
    (ops.fromHalf (input 1 (bAddress p row col))) 5
  let s := setReg s t 2 (activation ops (ops.fromHalf (input 1 (aAddress p row col)))) 6
  let s := advance { record s t (cell 0 (oAddress p row col)) true with
    memory := fun l => if l = cell 0 (oAddress p row col)
      then some (result p ops input row col) else s.memory l } t 7
  advance (setIndex s t 1 (((col + p.block : Nat)) : Int) 8) t 2

def iterate (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (t row : Nat) :
    Nat → Nat → State α → State α
  | 0, _, s => advance s t 9
  | k + 1, col, s => if col < p.width
      then iterate p ops input t row k (col + p.block) (cycleState p ops input t row col s)
      else advance s t 9
def finished (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (t : Nat)
    (s : State α) : State α :=
  iterate p ops input t (t / p.block) p.width (t % p.block) (initialized p t s)
def post (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (s : State α) (t : Nat) : State α :=
  if s.pc t = 9 then s else finished p ops input t s

theorem width_bound (p : Shape) : 2 * p.width < 2147483648 := by
  have hh := Nat.mul_le_mul_right (2 * p.width) (show 1 ≤ p.rows by have := p.rowsPos; omega)
  simp only [Nat.one_mul] at hh
  have := p.dataBound
  omega
theorem rows_bound (p : Shape) : p.rows < 2147483648 := by
  have hh := Nat.mul_le_mul_left p.rows (show 1 ≤ 2 * p.width by have := p.widthPos; omega)
  simp only [Nat.mul_one] at hh
  have := p.dataBound
  omega
theorem addresses_bound (p : Shape) (row col : Nat) (hr : row < p.rows) (hc : col < p.width) :
    aAddress p row col < p.rows * (2 * p.width) ∧
    bAddress p row col < p.rows * (2 * p.width) ∧ oAddress p row col < p.rows * p.width := by
  have ha := address_bound p.rows (2 * p.width) row col hr (by omega)
  have hb := address_bound p.rows (2 * p.width) row (col + p.width) hr (by omega)
  have ho := address_bound p.rows p.width row col hr hc
  simpa [aAddress, bAddress, oAddress, Nat.mul_assoc, Nat.add_assoc] using ⟨ha, hb, ho⟩

theorem stride_gap (j col block : Nat) (hb : 0 < block) (hj : j < col)
    (hm : j % block = col % block) : j + block ≤ col := by
  have hd : j / block ≤ col / block :=
    (Nat.le_div_iff_mul_le hb).mpr (Nat.le_trans (Nat.div_mul_le_self j block) (by omega))
  have hne : j / block ≠ col / block := by
    intro he
    have h1 := Nat.mod_add_div j block
    have h2 := Nat.mod_add_div col block
    rw [hm, he] at h1
    omega
  have hq : j / block + 1 ≤ col / block := by omega
  have hmul := Nat.mul_le_mul_left block hq
  simp only [Nat.mul_add, Nat.mul_one] at hmul
  have h1 := Nat.mod_add_div j block
  have h2 := Nat.mod_add_div col block
  rw [hm] at h1
  omega

theorem owner_row (p : Shape) (row col : Nat) : owner p row col / p.block = row := by
  have hm := Nat.mod_lt col p.blockPos
  simpa [owner, Nat.mul_comm, Nat.add_comm, Nat.div_eq_of_lt hm] using
    Nat.add_mul_div_left (col % p.block) row p.blockPos
theorem owner_lane (p : Shape) (row col : Nat) : owner p row col % p.block = col % p.block := by
  simp [owner, Nat.add_mod, Nat.mul_mod]
theorem owner_bound (p : Shape) (row col : Nat) (hr : row < p.rows) :
    owner p row col < p.rows * p.block := by
  exact address_bound p.rows p.block row (col % p.block) hr (Nat.mod_lt col p.blockPos)

theorem output_row (p : Shape) (row col : Nat) (hc : col < p.width) :
    oAddress p row col / p.width = row := by
  simpa [oAddress, Nat.mul_comm, Nat.add_comm, Nat.div_eq_of_lt hc] using
    Nat.add_mul_div_left col row p.widthPos
theorem output_col (p : Shape) (row col : Nat) (hc : col < p.width) :
    oAddress p row col % p.width = col := by simp [oAddress, Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt hc]
theorem output_injective (p : Shape) (r c r' c' : Nat) (hc : c < p.width) (hc' : c' < p.width)
    (he : oAddress p r c = oAddress p r' c') : r = r' ∧ c = c' := by
  have hr := congrArg (fun n => n / p.width) he
  have hh := congrArg (fun n => n % p.width) he
  simpa only [output_row p r c hc, output_row p r' c' hc', output_col p r c hc,
    output_col p r' c' hc'] using And.intro hr hh

theorem a_index_eval (p : Shape) (g : Geometry) (t row col : Nat) (s : State α)
    (hr : row < p.rows) (hc : col < p.width)
    (hi : s.indices t 0 = some (row : Int)) (hj : s.indices t 1 = some (col : Int)) :
    evalIndex g t s (aIndex p) = some ((aAddress p row col : Nat) : Int) := by
  have ha := (addresses_bound p row col hr hc).1
  have hbound := p.dataBound
  have hw := p.widthPos
  have hmul : (row * 2) * p.width < 2147483648 := by unfold aAddress at ha; omega
  have hrow2 : row * 2 < 2147483648 := by
    have he := Nat.mul_le_mul_left (row * 2) (show 1 ≤ p.width by omega)
    simp only [Nat.mul_one] at he
    omega
  have hd := width_bound p
  have h1 := LarkMatrix.eval_mul_nat g t s (.ivar 0) (.const 2) row 2 hi (by rfl) hrow2
  have h2 := LarkMatrix.eval_mul_nat g t s (.mul (.ivar 0) (.const 2))
    (.const (p.width : Int)) (row * 2) p.width h1 (int32_cast _ (by omega)) hmul
  exact LarkMatrix.eval_add_nat g t s _ _ ((row * 2) * p.width) col h2 hj (by
    unfold aAddress at ha
    omega)

theorem b_index_eval (p : Shape) (g : Geometry) (t row col : Nat) (s : State α)
    (hr : row < p.rows) (hc : col < p.width)
    (hi : s.indices t 0 = some (row : Int)) (hj : s.indices t 1 = some (col : Int)) :
    evalIndex g t s (bIndex p) = some ((bAddress p row col : Nat) : Int) := by
  have hb := (addresses_bound p row col hr hc).2.1
  have hbound := p.dataBound
  have hd := width_bound p
  exact LarkMatrix.eval_add_nat g t s _ _ (aAddress p row col) p.width
    (a_index_eval p g t row col s hr hc hi hj) (int32_cast _ (by omega)) (by
      unfold bAddress at hb
      omega)

theorem o_index_eval (p : Shape) (g : Geometry) (t row col : Nat) (s : State α)
    (hr : row < p.rows) (hc : col < p.width)
    (hi : s.indices t 0 = some (row : Int)) (hj : s.indices t 1 = some (col : Int)) :
    evalIndex g t s (oIndex p) = some ((oAddress p row col : Nat) : Int) := by
  have ho := (addresses_bound p row col hr hc).2.2
  have hspan : p.rows * p.width ≤ p.rows * (2 * p.width) :=
    Nat.mul_le_mul_left p.rows (by omega)
  have hbound := p.dataBound
  have hd := width_bound p
  have h1 := LarkMatrix.eval_mul_nat g t s (.ivar 0) (.const (p.width : Int)) row p.width
    hi (int32_cast _ (by omega)) (by unfold oAddress at ho; omega)
  exact LarkMatrix.eval_add_nat g t s _ _ (row * p.width) col h1 hj (by
    unfold oAddress at ho
    omega)

theorem load_of (p : Shape) (ops : Ops α) (g : Geometry) (t i : Nat) (ix : Index)
    (s : State α) (input : Nat → Nat → α) (hr : Reads p input s)
    (hb : i < p.rows * (2 * p.width)) (he : evalIndex g t s ix = some (i : Int)) :
    evalExpr ops (layout p) g t (.un .fromHalf (.load .global 1 ix)) s =
      some (ops.fromHalf (input 1 i), record s t (cell 1 i) false) := by
  have hneg : ¬ (i : Int) < 0 := by omega
  have hl : location (layout p) g t .global 1 (i : Int) false = some (cell 1 i) := by
    simp [location, layout, cell, hneg, hb]
  simp only [evalExpr, he, bind, pure, Option.bind, hl, hr i hb]
  rfl

theorem cycle (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t row col f : Nat) (s : State α) (reads : Reads p input s)
    (hr : row < p.rows) (hc : col < p.width)
    (hi : s.indices t 0 = some (row : Int)) (hj : s.indices t 1 = some (col : Int))
    (hp : s.pc t = 2) :
    runLane ops (layout p) (geometry p) (program p) t (f + 7) s =
      runLane ops (layout p) (geometry p) (program p) t f (cycleState p ops input t row col s) := by
  let s1 := advance s t 3
  let s2 := setReg (record s1 t (cell 1 (aAddress p row col)) false) t 0
    (ops.fromHalf (input 1 (aAddress p row col))) 4
  let s3 := setReg (record s2 t (cell 1 (bAddress p row col)) false) t 1
    (ops.fromHalf (input 1 (bAddress p row col))) 5
  let s4 := setReg s3 t 2 (activation ops (ops.fromHalf (input 1 (aAddress p row col)))) 6
  let s5 := advance { record s4 t (cell 0 (oAddress p row col)) true with
    memory := fun l => if l = cell 0 (oAddress p row col)
      then some (result p ops input row col) else s4.memory l } t 7
  let s6 := setIndex s5 t 1 (((col + p.block : Nat)) : Int) 8
  have hd := width_bound p
  have hblock := p.blockLe
  have hg := predicate_lt_of (geometry p) t s (.ivar 1) (.const (p.width : Int))
    (col : Int) (p.width : Int) hj (int32_cast _ (by omega)) (by omega)
  have h1 : execute ops (layout p) (geometry p) t
      (.branch (.lt (.ivar 1) (.const (p.width : Int))) 9) s = some s1 := by
    simp only [execute, hg, hp, bind, pure, Option.bind]
    rfl
  have bounds := addresses_bound p row col hr hc
  have he2 := load_of p ops (geometry p) t (aAddress p row col) (aIndex p) s1 input
    reads bounds.1 (a_index_eval p _ t row col s1 hr hc hi hj)
  have h2 : execute ops (layout p) (geometry p) t
      (.assign 0 (.un .fromHalf (.load .global 1 (aIndex p)))) s1 = some s2 := by
    simp only [execute, he2, bind, pure, Option.bind]
    simp [s2, s1, setReg, advance]
  have he3 := load_of p ops (geometry p) t (bAddress p row col) (bIndex p) s2 input
    reads bounds.2.1 (b_index_eval p _ t row col s2 hr hc hi hj)
  have h3 : execute ops (layout p) (geometry p) t
      (.assign 1 (.un .fromHalf (.load .global 1 (bIndex p)))) s2 = some s3 := by
    simp only [execute, he3, bind, pure, Option.bind]
    simp [s3, s2, setReg, advance]
  have ha : evalExpr ops (layout p) (geometry p) t activationExpr s3 =
      some (activation ops (ops.fromHalf (input 1 (aAddress p row col))), s3) := by
    simp [activationExpr, evalExpr, s3, s2, setReg, advance, record, activation, applyUnary, applyBinary]
  have h4 : execute ops (layout p) (geometry p) t (.assign 2 activationExpr) s3 = some s4 :=
    execute_pure_of ops _ _ t 2 6 _ s3 _ ha (by simp [s3, setReg, advance])
  have he5 : evalExpr ops (layout p) (geometry p) t outputExpr s4 =
      some (result p ops input row col, s4) := by
    simp [outputExpr, evalExpr, s4, s3, setReg, advance, result, applyUnary, applyBinary]
  have hix := o_index_eval p (geometry p) t row col s4 hr hc hi hj
  have hlo : location (layout p) (geometry p) t .global 0 (oAddress p row col : Int) true =
      some (cell 0 (oAddress p row col)) := by
    have hn : ¬ (oAddress p row col : Int) < 0 := by omega
    have hrole : (Role.output == Role.input) = false := by decide
    simp [location, layout, cell, hn, bounds.2.2, hrole]
  have h5 : execute ops (layout p) (geometry p) t (.store .global 0 (oIndex p) outputExpr) s4 =
      some s5 := by
    simp only [execute, hix, hlo, he5, bind, pure, Option.bind]
    simp [s5, s4, setReg, advance, record]
  have hbd : evalIndex (geometry p) t s5 .bdim = some (p.block : Int) := by
    change int32 (p.block : Int) = some (p.block : Int)
    exact int32_cast p.block (by omega)
  have he6 := LarkMatrix.eval_add_nat (geometry p) t s5 (.ivar 1) .bdim col p.block
    hj hbd (by omega)
  have h6 : execute ops (layout p) (geometry p) t (.index 1 (.add (.ivar 1) .bdim)) s5 =
      some s6 := execute_index_of ops _ _ t 1 8 _ s5 _ he6 (by simp [s5, advance])
  have h7 : execute ops (layout p) (geometry p) t (.jump 2) s6 =
      some (cycleState p ops input t row col s) := by rfl
  rewrite [LarkPointwise.lane_step ops _ _ _ _ _ _ _ _
    (by simp [parked, program, hp]) (by simp [program, hp]) h1]
  rewrite [LarkPointwise.lane_step ops _ _ _ _ _ _ _ _
    (by simp [parked, program, s1, advance]) (by simp [program, s1, advance]) h2]
  rewrite [LarkPointwise.lane_step ops _ _ _ _ _ _ _ _
    (by simp [parked, program, s2, setReg, advance]) (by simp [program, s2, setReg, advance]) h3]
  rewrite [LarkPointwise.lane_step ops _ _ _ _ _ _ _ _
    (by simp [parked, program, s3, setReg, advance]) (by simp [program, s3, setReg, advance]) h4]
  rewrite [LarkPointwise.lane_step ops _ _ _ _ _ _ _ _
    (by simp [parked, program, s4, setReg, advance]) (by simp [program, s4, setReg, advance]) h5]
  rewrite [LarkPointwise.lane_step ops _ _ _ _ _ _ _ _
    (by simp [parked, program, s5, advance]) (by simp [program, s5, advance]) h6]
  rewrite [LarkPointwise.lane_step ops _ _ _ _ _ _ _ _
    (by simp [parked, program, s6, setIndex, advance]) (by simp [program, s6, setIndex, advance]) h7]
  rfl

theorem cycle_memory (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t row col : Nat) (s : State α) (l : Location) :
    (cycleState p ops input t row col s).memory l =
      if l = cell 0 (oAddress p row col) then some (result p ops input row col) else s.memory l := by rfl

theorem cycle_pc (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t row col u : Nat) (s : State α) :
    (cycleState p ops input t row col s).pc u = if u = t then 2 else s.pc u := by
  by_cases h : u = t <;> simp [cycleState, advance, setReg, setIndex, record, h]

theorem cycle_row_index (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t row col : Nat) (s : State α) :
    (cycleState p ops input t row col s).indices t 0 = s.indices t 0 := by
  simp [cycleState, advance, setReg, setIndex, record]
theorem cycle_col_index (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t row col : Nat) (s : State α) :
    (cycleState p ops input t row col s).indices t 1 = some ((col + p.block : Nat) : Int) := by
  simp [cycleState, advance, setReg, setIndex, record]
theorem cycle_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t row col : Nat) (s : State α) (hr : Reads p input s) :
    Reads p input (cycleState p ops input t row col s) := by
  intro i hi
  rw [cycle_memory]
  simpa [cell] using hr i hi

theorem iterate_pc (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t row k col u : Nat) (s : State α) :
    (iterate p ops input t row k col s).pc u = if u = t then 9 else s.pc u := by
  induction k generalizing col s with
  | zero => simp [iterate, advance]
  | succ k ih =>
    simp only [iterate]
    split
    · rw [ih, cycle_pc]
      by_cases h : u = t <;> simp [h]
    · simp [advance]

theorem iterate_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t row k col : Nat) (s : State α) (hr : Reads p input s) :
    Reads p input (iterate p ops input t row k col s) := by
  induction k generalizing col s with
  | zero => exact hr
  | succ k ih =>
    simp only [iterate]
    split
    · exact ih _ _ (cycle_reads p ops input t row col s hr)
    · exact hr

theorem iterate_memory_preserved (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t row k col : Nat) (s : State α) (l : Location)
    (away : ∀ j, col ≤ j → j < p.width → j % p.block = col % p.block →
      l ≠ cell 0 (oAddress p row j)) :
    (iterate p ops input t row k col s).memory l = s.memory l := by
  induction k generalizing col s with
  | zero => rfl
  | succ k ih =>
    simp only [iterate]
    split
    next hc =>
      have hnext := ih (col + p.block) (cycleState p ops input t row col s) (by
        intro j hj hb hm
        apply away j (by omega) hb
        simpa [Nat.add_mod] using hm)
      rw [hnext, cycle_memory, if_neg (away col (by omega) hc rfl)]
    next => rfl

theorem iterate_writes (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t row k col target : Nat) (s : State α)
    (budget : p.width ≤ col + k) (ht : target < p.width) (hge : col ≤ target)
    (hm : target % p.block = col % p.block) :
    (iterate p ops input t row k col s).memory (cell 0 (oAddress p row target)) =
      some (result p ops input row target) := by
  induction k generalizing col s with
  | zero => omega
  | succ k ih =>
    have hc : col < p.width := by omega
    simp only [iterate, if_pos hc]
    by_cases he : target = col
    · subst target
      have hh := iterate_memory_preserved p ops input t row k (col + p.block)
        (cycleState p ops input t row col s) (cell 0 (oAddress p row col)) (by
          intro j hj _ _ he
          have ho := congrArg Location.offset he
          simp only [cell, oAddress] at ho
          have := p.blockPos
          omega)
      rw [hh, cycle_memory]
      simp
    · have gap := stride_gap col target p.block p.blockPos (by omega) hm.symm
      apply ih (col + p.block) (cycleState p ops input t row col s)
      · have := p.blockPos
        omega
      · exact gap
      · simpa [Nat.add_mod] using hm

theorem halted_lane (p : Shape) (ops : Ops α) (t f : Nat) (s : State α)
    (hp : s.pc t = 9) (hf : 0 < f) :
    runLane ops (layout p) (geometry p) (program p) t f s = some s := by
  cases f with
  | zero => omega
  | succ f => simp [runLane, parked, program, hp]

theorem exit_loop (p : Shape) (ops : Ops α) (t col f : Nat) (s : State α)
    (hj : s.indices t 1 = some (col : Int)) (hp : s.pc t = 2) (hc : p.width ≤ col)
    (hf : 0 < f) :
    runLane ops (layout p) (geometry p) (program p) t (f + 1) s = some (advance s t 9) := by
  have hd := width_bound p
  have hg := predicate_nlt_of (geometry p) t s (.ivar 1) (.const (p.width : Int))
    (col : Int) (p.width : Int) hj (int32_cast _ (by omega)) (by omega)
  have he : execute ops (layout p) (geometry p) t
      (.branch (.lt (.ivar 1) (.const (p.width : Int))) 9) s = some (advance s t 9) := by
    simp only [execute, hg, bind, pure, Option.bind]
    rfl
  rewrite [LarkPointwise.lane_step ops _ _ _ _ _ _ _ _
    (by simp [parked, program, hp]) (by simp [program, hp]) he]
  exact halted_lane p ops t f _ (by simp [advance]) hf

theorem loop_eq (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t row k col : Nat) (s : State α) (reads : Reads p input s)
    (hr : row < p.rows) (hi : s.indices t 0 = some (row : Int))
    (hj : s.indices t 1 = some (col : Int)) (hp : s.pc t = 2)
    (budget : p.width ≤ col + k) :
    runLane ops (layout p) (geometry p) (program p) t (7 * k + 2) s =
      some (iterate p ops input t row k col s) := by
  induction k generalizing col s with
  | zero => simpa [iterate] using exit_loop p ops t col 1 s hj hp (by omega) (by decide)
  | succ k ih =>
    by_cases hc : col < p.width
    · have hf : 7 * (k + 1) + 2 = (7 * k + 2) + 7 := by omega
      rewrite [hf, cycle p ops input t row col (7 * k + 2) s reads hr hc hi hj hp]
      simp only [iterate, if_pos hc]
      apply ih (col + p.block) (cycleState p ops input t row col s)
      · exact cycle_reads p ops input t row col s reads
      · simpa only [cycle_row_index] using hi
      · exact cycle_col_index p ops input t row col s
      · simp [cycle_pc]
      · have := p.blockPos
        omega
    · have hf : 7 * (k + 1) + 2 = (7 * (k + 1) + 1) + 1 := by omega
      rewrite [hf]
      simpa [iterate, hc] using exit_loop p ops t col (7 * (k + 1) + 1) s hj hp
        (by omega) (by omega)

theorem header_eq (p : Shape) (ops : Ops α)
    (t f : Nat) (s : State α) (ht : t < p.rows * p.block) (hp : s.pc t = 0) :
    runLane ops (layout p) (geometry p) (program p) t (f + 2) s =
      runLane ops (layout p) (geometry p) (program p) t f (initialized p t s) := by
  let s1 := setIndex s t 0 ((t / p.block : Nat) : Int) 1
  have hr : t / p.block < p.rows := (Nat.div_lt_iff_lt_mul p.blockPos).mpr ht
  have hrow := rows_bound p
  have hcol := Nat.mod_lt t p.blockPos
  have hblock := p.blockLe
  have hd := width_bound p
  have he1 : evalIndex (geometry p) t s .bid = some ((t / p.block : Nat) : Int) := by
    change int32 ((t / p.block : Nat) : Int) = _
    exact int32_cast _ (by omega)
  have h1 : execute ops (layout p) (geometry p) t (.index 0 .bid) s = some s1 :=
    execute_index_of ops _ _ t 0 1 .bid s _ he1 (by omega)
  have he2 : evalIndex (geometry p) t s1 .tid = some ((t % p.block : Nat) : Int) := by
    change int32 ((t % p.block : Nat) : Int) = _
    exact int32_cast _ (by omega)
  have h2 : execute ops (layout p) (geometry p) t (.index 1 .tid) s1 =
      some (initialized p t s) := execute_index_of ops _ _ t 1 2 .tid s1 _ he2
        (by simp [s1, setIndex, advance])
  rewrite [LarkPointwise.lane_step ops _ _ _ _ _ _ _ _
    (by simp [parked, program, hp]) (by simp [program, hp]) h1]
  rewrite [LarkPointwise.lane_step ops _ _ _ _ _ _ _ _
    (by simp [parked, program, s1, setIndex, advance])
    (by simp [program, s1, setIndex, advance]) h2]
  rfl

theorem lane_eq (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t : Nat) (s : State α) (reads : Reads p input s) (ht : t < p.rows * p.block)
    (hp : s.pc t = 0) :
    runLane ops (layout p) (geometry p) (program p) t (fuel p).lane s =
      some (finished p ops input t s) := by
  have hf : (fuel p).lane = (7 * p.width + 2) + 2 := by rfl
  rewrite [hf, header_eq p ops t (7 * p.width + 2) s ht hp]
  exact loop_eq p ops input t (t / p.block) p.width (t % p.block) (initialized p t s)
    reads ((Nat.div_lt_iff_lt_mul p.blockPos).mpr ht)
    (by simp [initialized, setIndex, advance]) (by simp [initialized, setIndex, advance])
    (by simp [initialized, setIndex, advance]) (by omega)

def Owned (p : Shape) (trace : List Access) : Prop :=
  ∀ a ∈ trace, if a.write then
    ∃ row col, row < p.rows ∧ col < p.width ∧
      a.location = cell 0 (oAddress p row col) ∧ owner p row col = a.thread
  else ∃ i, a.location = cell 1 i

theorem cycle_owned (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t row col : Nat) (s : State α) (hr : row < p.rows) (hc : col < p.width)
    (ho : owner p row col = t) (hs : Owned p s.trace) :
    Owned p (cycleState p ops input t row col s).trace := by
  intro a ha
  simp only [cycleState, advance, setReg, setIndex, record, List.mem_cons] at ha
  rcases ha with rfl | rfl | rfl | ha
  · exact ⟨row, col, hr, hc, rfl, ho⟩
  · exact ⟨bAddress p row col, rfl⟩
  · exact ⟨aAddress p row col, rfl⟩
  · exact hs a ha

theorem iterate_owned (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t row k col : Nat) (s : State α) (hr : row < p.rows)
    (ho : owner p row col = t) (hs : Owned p s.trace) :
    Owned p (iterate p ops input t row k col s).trace := by
  induction k generalizing col s with
  | zero => exact hs
  | succ k ih =>
    simp only [iterate]
    split
    next hc =>
      exact ih (col + p.block) (cycleState p ops input t row col s)
        (by simpa [owner, Nat.add_mod] using ho) (cycle_owned p ops input t row col s hr hc ho hs)
    next => exact hs

theorem owned_raceFree (p : Shape) (g : Geometry) (trace : List Access) (hs : Owned p trace) :
    raceFree g trace = true := by
  apply List.all_eq_true.mpr
  intro a ha
  apply List.all_eq_true.mpr
  intro b hb
  have hla := hs a ha
  have hlb := hs b hb
  by_cases same : a.thread = b.thread
  · simp [conflict, same]
  · cases aw : a.write <;> cases bw : b.write
    · simp [conflict, aw, bw]
    · simp only [aw, Bool.false_eq_true, ↓reduceIte] at hla
      simp only [bw, ↓reduceIte] at hlb
      obtain ⟨i, hi⟩ := hla
      obtain ⟨r, c, _, _, hl, _⟩ := hlb
      simp [conflict, sameLocation, hi, hl, cell]
    · simp only [aw, ↓reduceIte] at hla
      simp only [bw, Bool.false_eq_true, ↓reduceIte] at hlb
      obtain ⟨r, c, _, _, hl, _⟩ := hla
      obtain ⟨i, hi⟩ := hlb
      simp [conflict, sameLocation, hi, hl, cell]
    · simp only [aw, ↓reduceIte] at hla
      simp only [bw, ↓reduceIte] at hlb
      obtain ⟨r, c, _, hc, hloc, howner⟩ := hla
      obtain ⟨r', c', _, hc', hloc', howner'⟩ := hlb
      have hoff : oAddress p r c ≠ oAddress p r' c' := by
        intro he
        obtain ⟨hr, hh⟩ := output_injective p r c r' c' hc hc' he
        have heo : owner p r c = owner p r' c' := by rw [hr, hh]
        exact same (howner.symm.trans (heo.trans howner'))
      simp [conflict, sameLocation, hloc, hloc', cell, hoff]

theorem thread_owner (p : Shape) (t : Nat) : owner p (t / p.block) (t % p.block) = t := by
  simpa [owner, Nat.mul_comm] using Nat.div_add_mod t p.block

theorem finished_pc (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t u : Nat) (s : State α) :
    (finished p ops input t s).pc u = if u = t then 9 else s.pc u := by
  rw [finished, iterate_pc]
  by_cases h : u = t <;> simp [h, initialized, setIndex, advance]

theorem finished_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t : Nat) (s : State α) (hr : Reads p input s) : Reads p input (finished p ops input t s) :=
  iterate_reads p ops input t (t / p.block) p.width (t % p.block) (initialized p t s) hr

theorem finished_owned (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t : Nat) (s : State α) (ht : t < p.rows * p.block) (hs : Owned p s.trace) :
    Owned p (finished p ops input t s).trace := by
  exact iterate_owned p ops input t (t / p.block) p.width (t % p.block) (initialized p t s)
    ((Nat.div_lt_iff_lt_mul p.blockPos).mpr ht) (thread_owner p t) hs

theorem finished_writes (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t row col : Nat) (s : State α) (hc : col < p.width) (ho : owner p row col = t) :
    (finished p ops input t s).memory (cell 0 (oAddress p row col)) =
      some (result p ops input row col) := by
  have hr : row = t / p.block := by
    calc
      row = owner p row col / p.block := (owner_row p row col).symm
      _ = t / p.block := congrArg (fun n => n / p.block) ho
  have hm : col % p.block = t % p.block := by
    calc
      col % p.block = owner p row col % p.block := (owner_lane p row col).symm
      _ = t % p.block := congrArg (fun n => n % p.block) ho
  subst row
  unfold finished
  apply iterate_writes p ops input t (t / p.block) p.width (t % p.block) col
  · omega
  · exact hc
  · rw [← hm]
    exact Nat.mod_le col p.block
  · simpa using hm

theorem finished_other_output (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t row col : Nat) (s : State α) (hc : col < p.width) (ho : owner p row col ≠ t) :
    (finished p ops input t s).memory (cell 0 (oAddress p row col)) =
      s.memory (cell 0 (oAddress p row col)) := by
  unfold finished
  apply iterate_memory_preserved p ops input t (t / p.block) p.width (t % p.block)
    (initialized p t s) (cell 0 (oAddress p row col))
  intro j _ hj hm he
  have ha := congrArg Location.offset he
  have hi := output_injective p row col (t / p.block) j hc hj ha
  have hsame : owner p (t / p.block) j = t := by
    have hh : j % p.block = t % p.block := by simpa using hm
    simpa [owner, hh] using thread_owner p t
  apply ho
  simpa [hi.1, hi.2] using hsame

def Invariant (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (s : State α) : Prop :=
  Reads p input s ∧ Owned p s.trace ∧
  (∀ t, t < p.rows * p.block → s.pc t = 0 ∨ s.pc t = 9) ∧
  (∀ row col, row < p.rows → col < p.width → s.pc (owner p row col) = 9 →
    s.memory (cell 0 (oAddress p row col)) = some (result p ops input row col))

theorem invariant_initial (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) : Invariant p ops input (initial (layout p) input outside) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi
    simp [initial, layout, cell, hi]
  · intro a ha
    simp [initial] at ha
  · intro t _
    exact Or.inl rfl
  · intro row col _ _ hdone
    simp [initial] at hdone

theorem finished_invariant (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t : Nat) (s : State α) (hs : Invariant p ops input s) (ht : t < p.rows * p.block) :
    Invariant p ops input (finished p ops input t s) := by
  refine ⟨finished_reads p ops input t s hs.1, finished_owned p ops input t s ht hs.2.1, ?_, ?_⟩
  · intro u hu
    rw [finished_pc]
    by_cases he : u = t
    · simp [he]
    · simpa [he] using hs.2.2.1 u hu
  · intro row col hr hc hdone
    by_cases he : owner p row col = t
    · exact finished_writes p ops input t row col s hc he
    · rw [finished_other_output p ops input t row col s hc he]
      apply hs.2.2.2 row col hr hc
      simpa [finished_pc, he] using hdone

theorem lane_contract (p : Shape) (ops : Ops α) (input : Nat → Nat → α) :
    LarkScalarLaunch.LaneContract ops (layout p) (geometry p) (fuel p).lane 9 (program p)
      (post p ops input) (Invariant p ops input) := by
  intro s hs t ht
  change t < p.rows * p.block at ht
  by_cases he : s.pc t = 9
  · simp only [post, if_pos he]
    exact ⟨halted_lane p ops t (fuel p).lane s he (by simp [fuel, LarkScalarLaunch.fuel]),
      hs, he, by intro u hu; exact hu⟩
  · simp only [post, if_neg he]
    have hp : s.pc t = 0 := by
      rcases hs.2.2.1 t ht with h0 | h9
      · exact h0
      · contradiction
    refine ⟨lane_eq p ops input t s hs.1 ht hp, finished_invariant p ops input t s hs ht, ?_, ?_⟩
    · simp [finished_pc]
    · intro u hu
      by_cases hh : u = t <;> simp [finished_pc, hh, hu]

def finalState (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) : State α :=
  LarkScalarLaunch.launchPost (geometry p) (post p ops input) (initial (layout p) input outside)

theorem launch_eq (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) :
    runLaunch ops (layout p) (geometry p) (fuel p) (program p) (initial (layout p) input outside) =
      some (finalState p ops input outside) ∧ Invariant p ops input (finalState p ops input outside) ∧
      (∀ t, t < p.rows * p.block → (finalState p ops input outside).pc t = 9) := by
  exact LarkScalarLaunch.launch_simulation ops (layout p) (geometry p) (fuel p).lane 9
    (program p) (post p ops input) (Invariant p ops input) (by rfl) (lane_contract p ops input)
    p.rowsPos p.blockPos p.warpPos (initial (layout p) input outside) (invariant_initial p ops input outside)

def spec (p : Shape) (ops : Ops α) (input : Nat → Nat → α) : List α :=
  (List.range (p.rows * p.width)).map fun i => result p ops input (i / p.width) (i % p.width)

theorem final_output (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (i : Nat) (hi : i < p.rows * p.width) :
    (finalState p ops input outside).memory (cell 0 i) =
      some (result p ops input (i / p.width) (i % p.width)) := by
  have hr : i / p.width < p.rows := (Nat.div_lt_iff_lt_mul p.widthPos).mpr hi
  have hc := Nat.mod_lt i p.widthPos
  have info := launch_eq p ops input outside
  have ho := info.2.1.2.2.2 (i / p.width) (i % p.width) hr hc
    (info.2.2 _ (owner_bound p (i / p.width) (i % p.width) hr))
  have he : oAddress p (i / p.width) (i % p.width) = i := by
    simpa [oAddress, Nat.mul_comm] using Nat.div_add_mod i p.width
  simpa only [he] using ho

theorem extract_final (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) :
    extract (layout p) (finalState p ops input outside) = some (spec p ops input) := by
  simp only [extract, layout, List.zipIdx_cons, List.zipIdx_nil, List.flatMap_cons,
    List.flatMap_nil, List.nil_append]
  simp only [List.map_cons, List.map_nil, show Role.input ≠ Role.output by decide,
    ↓reduceIte, List.nil_append, List.append_nil]
  change (((List.range (p.rows * p.width)).map (fun i => (0, i))).mapM
    (fun bi => (finalState p ops input outside).memory ⟨.global, 0, bi.1, bi.2⟩) : Option (List α)) = _
  rw [LarkPointwise.mapM_map]
  exact LarkPointwise.mapM_some (List.range (p.rows * p.width)) _ _ (by
    intro i hi
    exact final_output p ops input outside i (List.mem_range.mp hi))

theorem correct (p : Shape) (ops : Ops α) :
    Correct ops (layout p) (geometry p) (fuel p) (program p) (spec p ops) := by
  intro input outside
  have info := launch_eq p ops input outside
  exact ⟨finalState p ops input outside, info.1,
    owned_raceFree p (geometry p) _ info.2.1.2.1, extract_final p ops input outside⟩

#print axioms lane_eq
#print axioms owned_raceFree
#print axioms correct
end LarkSilu

namespace LarkCertificate
open LarkNonlinear
def shape : LarkSilu.Shape := {
  rows := 64, width := 4097, block := 1024, warp := 64,
  rowsPos := by decide, widthPos := by decide, blockPos := by decide,
  warpPos := by decide, blockLe := by decide, dataBound := by decide }
def layout : Layout := LarkSilu.layout shape
def geometry : Geometry := LarkSilu.geometry shape
def fuel : Fuel := LarkSilu.fuel shape
def program : List Instr := [(.index 0 .bid), (.index 1 .tid), (.branch (.lt (.ivar (1)) (.const (4097))) 9), (.assign 0 (.un .fromHalf (.load .global 1 (.add (.mul (.mul (.ivar (0)) (.const (2))) (.const (4097))) (.ivar (1)))))), (.assign 1 (.un .fromHalf (.load .global 1 (.add (.add (.mul (.mul (.ivar (0)) (.const (2))) (.const (4097))) (.ivar (1))) (.const (4097)))))), (.assign 2 (.un .fromHalf (.un .toHalf (.bin .div (.reg (0)) (.bin .add (.lit (1) 1) (.un .exp (.bin .mul (.bin .sub (.lit (0) 1) (.reg (0))) (.lit (1) 1)))))))), (.store .global 0 (.add (.mul (.ivar (0)) (.const (4097))) (.ivar (1))) (.un .toHalf (.bin .mul (.reg (2)) (.bin .add (.reg (1)) (.lit (0) 1))))), (.index 1 (.add (.ivar (1)) (.const (1)))), (.jump 2), .halt]
def referenceResult (ops : Ops α) (input : Nat → Nat → α) (row col : Nat) : α :=
  (ops.toHalf (ops.mul (ops.fromHalf (ops.toHalf (ops.div (ops.fromHalf (input 1 (LarkSilu.aAddress shape row col))) (ops.add (ops.literal (1) 1) (ops.exp (ops.mul (ops.sub (ops.literal (0) 1) (ops.fromHalf (input 1 (LarkSilu.aAddress shape row col)))) (ops.literal (1) 1))))))) (ops.add (ops.fromHalf (input 1 (LarkSilu.bAddress shape row col))) (ops.literal (0) 1))))
def spec (ops : Ops α) (input : Nat → Nat → α) : List α :=
  (List.range (shape.rows * shape.width)).map fun i =>
    referenceResult ops input (i / shape.width) (i % shape.width)
def finalState (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) : State α :=
  LarkSilu.finalState shape ops input outside
theorem reference_data (ops : Ops α) (input : Nat → Nat → α) (row col : Nat) :
    referenceResult ops input row col = LarkSilu.result shape ops input row col := by rfl
theorem reference_spec (ops : Ops α) (input : Nat → Nat → α) :
    spec ops input = LarkSilu.spec shape ops input := by
  have he : (fun i => referenceResult ops input (i / shape.width) (i % shape.width)) =
      (fun i => LarkSilu.result shape ops input (i / shape.width) (i % shape.width)) := by
    funext i
    exact reference_data ops input _ _
  exact congrArg (fun f => (List.range (shape.rows * shape.width)).map f) he
theorem segmentation_data : program = LarkSilu.program shape := by rfl
theorem segmentation (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) :
    runLaunch ops layout geometry fuel program (initial layout input outside) =
      some (finalState ops input outside) := by
  rewrite [segmentation_data]
  exact (LarkSilu.launch_eq shape ops input outside).1
theorem race_free (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) :
    raceFree geometry (finalState ops input outside).trace = true := by
  exact LarkSilu.owned_raceFree shape geometry _ (LarkSilu.launch_eq shape ops input outside).2.1.2.1
theorem segment_equivalence (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) :
    extract layout (finalState ops input outside) = some (spec ops input) := by
  rewrite [reference_spec]
  exact LarkSilu.extract_final shape ops input outside
theorem kernel_eq_spec (ops : Ops α) : Correct ops layout geometry fuel program (spec ops) := by
  intro input outside
  exact ⟨finalState ops input outside, segmentation ops input outside,
    race_free ops input outside, segment_equivalence ops input outside⟩
theorem kernel_eq_spec_pre (ops : Ops α) (input : Nat → Nat → α) (s : State α)
    (pre : StdPre layout input s) :
    ∃ final, runLaunch ops layout geometry fuel program s = some final ∧
      raceFree geometry final.trace = true ∧ extract layout final = some (spec ops input) := by
  exact correct_from_pre ops layout geometry fuel program (spec ops) (kernel_eq_spec ops) input s pre
#print axioms segmentation_data
#print axioms segmentation
#print axioms race_free
#print axioms segment_equivalence
#print axioms kernel_eq_spec
#print axioms kernel_eq_spec_pre
end LarkCertificate
