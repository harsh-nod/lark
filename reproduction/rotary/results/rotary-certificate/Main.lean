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
Induction for the actual scalar machine's counted dot-product loop and grid.
Profiles supply only input address functions, bounds, and primitive index-evaluation
proofs. No assumed loop summary, execution equality or correctness field is used.
The machine model is unchanged. The conclusion is its existing Correct predicate,
including completion, race freedom and every output, for all inputs/outside memory.
-/
namespace LarkBias
open LarkNonlinear
open LarkReduction
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

structure Profile extends LarkDot.Profile where
  cSize : Nat
  cIndex : Index
  cAddress : Nat → Nat
  cBound : ∀ t, t < n → cAddress t < cSize
  cEval : ∀ (α : Type) (g : Geometry) (t : Nat) (s : State α),
    s.indices t 0 = some (t : Int) → t < n →
    evalIndex g t s cIndex = some ((cAddress t : Nat) : Int)

def layout (p : Profile) : Layout :=
  ⟨[⟨.input, p.aSize⟩, ⟨.input, p.bSize⟩, ⟨.input, p.cSize⟩, ⟨.output, p.n⟩], [], []⟩
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
   .store .global 3 (.ivar 0) (.un .toHalf (.bin .add (.reg 0) (.un .fromHalf (.load .global 2 p.cIndex)))),
   .halt]

def Reads (p : Profile) (input : Nat → Nat → α) (s : State α) : Prop :=
  (∀ i, i < p.aSize → s.memory (cell 0 i) = some (input 0 i)) ∧
  (∀ j, j < p.bSize → s.memory (cell 1 j) = some (input 1 j)) ∧
  (∀ i, i < p.cSize → s.memory (cell 2 i) = some (input 2 i))

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

def biased (ops : Ops α) (input : Nat → Nat → α) (p : Profile) (t : Nat) (acc : α) : α :=
  ops.toHalf (ops.add acc (ops.fromHalf (input 2 (p.cAddress t))))

def stored (ops : Ops α) (input : Nat → Nat → α) (p : Profile) (t : Nat)
    (acc : α) (s : State α) : State α :=
  let s := record s t (cell 2 (p.cAddress t)) false
  advance { record s t (cell 3 t) true with
    memory := fun l => if l = cell 3 t then some (biased ops input p t acc) else s.memory l } t 8

def iterate (ops : Ops α) (input : Nat → Nat → α) (p : Profile) (t : Nat) :
    Nat → Nat → α → State α → State α
  | _, 0, acc, s => stored ops input p t acc (advance s t 7)
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
  biased ops input p t (folded ops input p t 0 p.k (ops.literal 0 1))

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
  simp only [evalExpr, hix, bind, pure, Option.bind, hl, hr.2.1 _ ha]
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

theorem eval_un_of (ops : Ops α) (l : Layout) (g : Geometry) (t : Nat)
    (op : Unary) (e : Expr) (s s1 : State α) (v : α)
    (he : evalExpr ops l g t e s = some (v,s1)) :
    evalExpr ops l g t (.un op e) s = some (applyUnary ops op v,s1) := by
  change (do let (x, next) ← evalExpr ops l g t e s
             pure (applyUnary ops op x, next)) = _
  rw [he]
  rfl

theorem execute_store (ops : Ops α) (input : Nat → Nat → α) (p : Profile)
    (w t : Nat) (s : State α) (acc : α) (hr : Reads p input s)
    (hi : s.indices t 0 = some (t : Int)) (hacc : s.regs t 0 = some acc)
    (hp : s.pc t = 7) (ht : t < p.n) :
    execute ops (layout p) (geometry p w) t
      (.store .global 3 (.ivar 0) (.un .toHalf (.bin .add (.reg 0)
        (.un .fromHalf (.load .global 2 p.cIndex))))) s =
      some (stored ops input p t acc s) := by
  have hneg : ¬ (t : Int) < 0 := by omega
  have hrole : (Role.output == Role.input) = false := by decide
  have hl : location (layout p) (geometry p w) t .global 3 (t : Int) true =
      some (cell 3 t) := by simp [location, layout, cell, hneg, ht, hrole]
  have hc := p.cBound t ht
  have hcn : ¬ ((p.cAddress t : Nat) : Int)<0 := by omega
  have hcl : location (layout p) (geometry p w) t .global 2
      ((p.cAddress t : Nat) : Int) false = some (cell 2 (p.cAddress t)) := by
    simp [location, layout, cell, hcn, hc]
  have hec := p.cEval α (geometry p w) t s hi ht
  have hload : evalExpr ops (layout p) (geometry p w) t
      (.un .fromHalf (.load .global 2 p.cIndex)) s =
      some (ops.fromHalf (input 2 (p.cAddress t)), record s t (cell 2 (p.cAddress t)) false) := by
    simp only [evalExpr, hec, bind, pure, Option.bind, hcl, hr.2.2 _ hc]
    rfl
  have hreg : evalExpr ops (layout p) (geometry p w) t (.reg 0) s = some (acc,s) := by
    simp [evalExpr, hacc]
  have hadd := eval_bin_of ops (layout p) (geometry p w) t .add _ _ _ _ _ _ _ hreg hload
  have he : evalExpr ops (layout p) (geometry p w) t
      (.un .toHalf (.bin .add (.reg 0) (.un .fromHalf (.load .global 2 p.cIndex)))) s =
      some (biased ops input p t acc, record s t (cell 2 (p.cAddress t)) false) := by
    exact eval_un_of ops (layout p) (geometry p w) t .toHalf _ _ _ _ hadd
  simp only [execute, evalIndex, hi, bind, pure, Option.bind, hl, he, hp]
  rfl

theorem loop_done (ops : Ops α) (input : Nat → Nat → α) (p : Profile) (w t : Nat) (s : State α) (acc : α)
    (hi : s.indices t 0 = some (t : Int)) (hij : s.indices t 1 = some (p.k : Int))
    (hacc : s.regs t 0 = some acc) (hp : s.pc t = 3)
    (ht : t < p.n) (hk : p.k < 2147483648) (hr : Reads p input s) :
    runLane ops (layout p) (geometry p w) (program p) t 3 s =
      some (stored ops input p t acc (advance s t 7)) := by
  have hg := predicate_nlt_of (geometry p w) t s (.ivar 1) (.const (p.k : Int))
    (p.k : Int) (p.k : Int) hij (int32_cast p.k hk) (by omega)
  have h1 : execute ops (layout p) (geometry p w) t
      (.branch (.lt (.ivar 1) (.const (p.k : Int))) 7) s = some (advance s t 7) := by
    simp only [execute, hg, bind, pure, Option.bind]
    rfl
  have h2 := execute_store ops input p w t (advance s t 7) acc hr hi hacc
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
      simpa [iterate] using loop_done ops input p w t s acc hi hij hacc hp ht
        (hb.2) hr
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
      if l = cell 3 t then some (biased ops input p t (folded ops input p t j r acc)) else s.memory l := by
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
  · constructor
    · intro i hi
      simpa [iterate_memory, cell] using hr.2.1 i hi
    · intro i hi
      simpa [iterate_memory, cell] using hr.2.2 i hi

def Owned (tr : List Access) : Prop :=
  ∀ a ∈ tr, if a.write then a.location = cell 3 a.thread else a.location.buffer < 3

theorem owned_read (tr : List Access) (h : Owned tr) (t b i : Nat) (e : Epoch) (hb : b<3) :
    Owned (⟨t, cell b i, false, e⟩ :: tr) := by
  intro a ha
  simp only [List.mem_cons] at ha
  rcases ha with rfl | ha
  · exact hb
  · exact h a ha

theorem owned_write (tr : List Access) (h : Owned tr) (t : Nat) (e : Epoch) :
    Owned (⟨t, cell 3 t, true, e⟩ :: tr) := by
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
  | zero => exact owned_write _ (owned_read _ h t 2 (p.cAddress t) (s.epochs t) (by decide)) t (s.epochs t)
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
      if l = cell 3 t then some (result ops input p t) else s.memory l := by
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
      have hbeq : (a.location.buffer == 3) = false := by
        simp [show a.location.buffer ≠ 3 by omega]
      simp [conflict, sameLocation, haw, hbw, hy, cell, hbeq]
    · simp only [haw, hbw, Bool.false_eq_true, ↓reduceIte] at hx hy
      have hbeq : (3 == b.location.buffer) = false := by
        simp [show 3 ≠ b.location.buffer by omega]
      simp [conflict, sameLocation, haw, hbw, hx, cell, hbeq]
    · simp only [haw, hbw, Bool.false_eq_true, ↓reduceIte] at hx hy
      have hbeq : (a.thread == b.thread) = false := by simp [ht]
      simp [conflict, sameLocation, haw, hbw, hx, hy, cell, hbeq]

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
      · constructor
        · intro j hj
          simp [partialState, initial, layout, cell, hj]
        · intro j hj
          simp [partialState, initial, layout, cell, hj]
  | succ q ih => exact finished_reads ops input p q _ ih

theorem partialState_output (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (p : Profile) (q t : Nat) (ht : t<q) :
    (partialState ops input outside p q).memory (cell 3 t) = some (result ops input p t) := by
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
  change (((List.range p.n).map (fun i => (3, i))).mapM
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
  (List.range p.n).map (fun t => biased ops input p t (dotSpec ops input p t))

theorem folded_eq_list (ops : Ops α) (input : Nat → Nat → α) (p : Profile) (t r j : Nat) (acc : α) :
    folded ops input p t j r acc =
      (List.range' j r).foldl (fun acc z => ops.add acc (term ops input p t z)) acc := by
  induction r generalizing j acc with
  | zero => rfl
  | succ r ih =>
      rw [folded, List.range'_succ, List.foldl_cons]
      exact ih (j+1) _

theorem result_eq_dot (ops : Ops α) (input : Nat → Nat → α) (p : Profile) (t : Nat) :
    result ops input p t = biased ops input p t (dotSpec ops input p t) := by
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

def linearProfile (m n k : Nat) (hm : 0<m) (hn : 0<n)
    (hnb : n<2147483648) (ha : m*k<2147483648) (hb : k*n<2147483648) : Profile :=
  { toProfile := LarkMatrix.profile m n k hm hn hnb ha hb,
    cSize := n, cIndex := .mod (.ivar 0) (.const (n : Int)), cAddress := fun t => t%n,
    cBound := fun t _ => Nat.mod_lt t hn,
    cEval := fun _ g t s hi _ => LarkMatrix.eval_mod_nat g t s (.ivar 0) (.const (n : Int))
      t n hi (int32_cast n hnb) hn }

#print axioms loop_step
#print axioms loop_eq
#print axioms lane_eq
#print axioms correct
#print axioms matrix_correct

end LarkBias


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

namespace LarkCertificate
open LarkNonlinear
def layout : Layout := LarkRotary.layout 16384
def geometry : Geometry := LarkRotary.geometry 16384 64
def fuel : Fuel := LarkRotary.fuel
def program : List Instr := [(.index 0 .bid), (.index 1 (.mul (.div (.ivar (0)) (.const (2))) (.const (2)))), (.assign 0 (.un .fromHalf (.load .global 0 (.ivar (1))))), (.assign 1 (.un .fromHalf (.load .global 0 (.add (.ivar (1)) (.const (1)))))), (.branch (.eq (.mod (.ivar (0)) (.const (2))) (.const (0))) 7), (.store .global 3 (.ivar (0)) (.un .toHalf (.bin .sub (.bin .mul (.reg (0)) (.un .fromHalf (.load .global 1 (.div (.ivar (0)) (.const (2)))))) (.bin .mul (.reg (1)) (.un .fromHalf (.load .global 2 (.div (.ivar (0)) (.const (2))))))))), (.jump 8), (.store .global 3 (.ivar (0)) (.un .toHalf (.bin .add (.bin .mul (.reg (0)) (.un .fromHalf (.load .global 2 (.div (.ivar (0)) (.const (2)))))) (.bin .mul (.reg (1)) (.un .fromHalf (.load .global 1 (.div (.ivar (0)) (.const (2))))))))), .halt]
def spec (ops : Ops α) (input : Nat → Nat → α) : List α :=
  LarkRotary.spec ops 16384 input
def finalState (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) : State α :=
  LarkRotary.partialState ops 16384 input outside 32768
theorem segmentation_data : program = LarkRotary.program := by rfl
theorem segmentation (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) :
    runLaunch ops layout geometry fuel program (initial layout input outside) =
      some (finalState ops input outside) := by
  rw [segmentation_data]
  exact LarkRotary.launch_eq ops 16384 64 input outside
    (by decide) (by decide) (by decide)
theorem race_free (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) :
    raceFree geometry (finalState ops input outside).trace = true := by
  exact LarkBias.owned_raceFree geometry _
    (LarkRotary.partialState_owned ops 16384 input outside 32768)
theorem segment_equivalence (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) :
    extract layout (finalState ops input outside) = some (spec ops input) := by
  exact LarkRotary.partialState_extract ops 16384 input outside
theorem kernel_eq_spec (ops : Ops α) :
    Correct ops layout geometry fuel program (spec ops) := by
  intro input outside
  exact ⟨finalState ops input outside, segmentation ops input outside,
    race_free ops input outside, segment_equivalence ops input outside⟩
theorem kernel_eq_spec_pre (ops : Ops α) (input : Nat → Nat → α) (s : State α)
    (pre : StdPre layout input s) :
    ∃ final, runLaunch ops layout geometry fuel program s = some final ∧
      raceFree geometry final.trace = true ∧ extract layout final = some (spec ops input) := by
  exact correct_from_pre ops layout geometry fuel program (spec ops)
    (kernel_eq_spec ops) input s pre
#print axioms segmentation_data
#print axioms segmentation
#print axioms race_free
#print axioms segment_equivalence
#print axioms kernel_eq_spec
#print axioms kernel_eq_spec_pre
end LarkCertificate
