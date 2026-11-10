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


namespace LarkCertificate
open LarkNonlinear
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def layout : Layout := ⟨[⟨.input, 8⟩, ⟨.input, 8⟩, ⟨.input, 8⟩, ⟨.output, 8⟩], [], []⟩
def geometry : Geometry := ⟨1, 2, 64⟩
def fuel : Fuel := ⟨1024, 16, 16, 16⟩
def program : List Instr := [(.index 0 .tid), (.index 1 (.div (.ivar (0)) (.const (2)))), (.index 2 (.mod (.ivar (0)) (.const (2)))), (.assign 0 (.lit (0) 1)), (.assign 1 (.lit (0) 1)), (.index 3 (.const (0))), (.branch (.lt (.ivar (3)) (.const (4))) 11), (.assign 0 (.bin .add (.reg (0)) (.bin .mul (.un .fromHalf (.load .global 0 (.add (.mul (.add (.mul (.ivar (1)) (.const (2))) (.ivar (2))) (.const (4))) (.ivar (3))))) (.un .fromHalf (.load .global 1 (.ivar (3))))))), (.assign 1 (.bin .add (.reg (1)) (.bin .mul (.un .fromHalf (.load .global 0 (.add (.mul (.add (.mul (.ivar (1)) (.const (2))) (.ivar (2))) (.const (4))) (.ivar (3))))) (.un .fromHalf (.load .global 1 (.add (.const (4)) (.ivar (3)))))))), (.index 3 (.add (.ivar (3)) (.const (1)))), (.jump 6), (.assign 0 (.bin .div (.reg (0)) (.lit (2) 1))), (.assign 1 (.bin .div (.reg (1)) (.lit (2) 1))), (.assign 2 (.bin .max (.reg (0)) (.reg (1)))), (.assign 3 (.un .exp (.bin .sub (.reg (0)) (.reg (2))))), (.assign 4 (.un .exp (.bin .sub (.reg (1)) (.reg (2))))), (.assign 5 (.bin .add (.bin .add (.lit (0) 1) (.reg (3))) (.reg (4)))), (.index 4 (.const (0))), (.branch (.lt (.ivar (4)) (.const (4))) 24), (.assign 6 (.bin .add (.lit (0) 1) (.bin .mul (.bin .div (.reg (3)) (.reg (5))) (.un .fromHalf (.load .global 2 (.ivar (4))))))), (.assign 6 (.bin .add (.reg (6)) (.bin .mul (.bin .div (.reg (4)) (.reg (5))) (.un .fromHalf (.load .global 2 (.add (.const (4)) (.ivar (4)))))))), (.store .global 3 (.add (.mul (.add (.mul (.ivar (1)) (.const (2))) (.ivar (2))) (.const (4))) (.ivar (4))) (.un .toHalf (.reg (6)))), (.index 4 (.add (.ivar (4)) (.const (1)))), (.jump 18), .halt]
def traceData : List Access := [⟨1, ⟨.global, 0, 3, 7⟩, true, ⟨0, 0, 0⟩⟩, ⟨1, ⟨.global, 0, 2, 7⟩, false, ⟨0, 0, 0⟩⟩, ⟨1, ⟨.global, 0, 2, 3⟩, false, ⟨0, 0, 0⟩⟩, ⟨1, ⟨.global, 0, 3, 6⟩, true, ⟨0, 0, 0⟩⟩, ⟨1, ⟨.global, 0, 2, 6⟩, false, ⟨0, 0, 0⟩⟩, ⟨1, ⟨.global, 0, 2, 2⟩, false, ⟨0, 0, 0⟩⟩, ⟨1, ⟨.global, 0, 3, 5⟩, true, ⟨0, 0, 0⟩⟩, ⟨1, ⟨.global, 0, 2, 5⟩, false, ⟨0, 0, 0⟩⟩, ⟨1, ⟨.global, 0, 2, 1⟩, false, ⟨0, 0, 0⟩⟩, ⟨1, ⟨.global, 0, 3, 4⟩, true, ⟨0, 0, 0⟩⟩, ⟨1, ⟨.global, 0, 2, 4⟩, false, ⟨0, 0, 0⟩⟩, ⟨1, ⟨.global, 0, 2, 0⟩, false, ⟨0, 0, 0⟩⟩, ⟨1, ⟨.global, 0, 1, 7⟩, false, ⟨0, 0, 0⟩⟩, ⟨1, ⟨.global, 0, 0, 7⟩, false, ⟨0, 0, 0⟩⟩, ⟨1, ⟨.global, 0, 1, 3⟩, false, ⟨0, 0, 0⟩⟩, ⟨1, ⟨.global, 0, 0, 7⟩, false, ⟨0, 0, 0⟩⟩, ⟨1, ⟨.global, 0, 1, 6⟩, false, ⟨0, 0, 0⟩⟩, ⟨1, ⟨.global, 0, 0, 6⟩, false, ⟨0, 0, 0⟩⟩, ⟨1, ⟨.global, 0, 1, 2⟩, false, ⟨0, 0, 0⟩⟩, ⟨1, ⟨.global, 0, 0, 6⟩, false, ⟨0, 0, 0⟩⟩, ⟨1, ⟨.global, 0, 1, 5⟩, false, ⟨0, 0, 0⟩⟩, ⟨1, ⟨.global, 0, 0, 5⟩, false, ⟨0, 0, 0⟩⟩, ⟨1, ⟨.global, 0, 1, 1⟩, false, ⟨0, 0, 0⟩⟩, ⟨1, ⟨.global, 0, 0, 5⟩, false, ⟨0, 0, 0⟩⟩, ⟨1, ⟨.global, 0, 1, 4⟩, false, ⟨0, 0, 0⟩⟩, ⟨1, ⟨.global, 0, 0, 4⟩, false, ⟨0, 0, 0⟩⟩, ⟨1, ⟨.global, 0, 1, 0⟩, false, ⟨0, 0, 0⟩⟩, ⟨1, ⟨.global, 0, 0, 4⟩, false, ⟨0, 0, 0⟩⟩, ⟨0, ⟨.global, 0, 3, 3⟩, true, ⟨0, 0, 0⟩⟩, ⟨0, ⟨.global, 0, 2, 7⟩, false, ⟨0, 0, 0⟩⟩, ⟨0, ⟨.global, 0, 2, 3⟩, false, ⟨0, 0, 0⟩⟩, ⟨0, ⟨.global, 0, 3, 2⟩, true, ⟨0, 0, 0⟩⟩, ⟨0, ⟨.global, 0, 2, 6⟩, false, ⟨0, 0, 0⟩⟩, ⟨0, ⟨.global, 0, 2, 2⟩, false, ⟨0, 0, 0⟩⟩, ⟨0, ⟨.global, 0, 3, 1⟩, true, ⟨0, 0, 0⟩⟩, ⟨0, ⟨.global, 0, 2, 5⟩, false, ⟨0, 0, 0⟩⟩, ⟨0, ⟨.global, 0, 2, 1⟩, false, ⟨0, 0, 0⟩⟩, ⟨0, ⟨.global, 0, 3, 0⟩, true, ⟨0, 0, 0⟩⟩, ⟨0, ⟨.global, 0, 2, 4⟩, false, ⟨0, 0, 0⟩⟩, ⟨0, ⟨.global, 0, 2, 0⟩, false, ⟨0, 0, 0⟩⟩, ⟨0, ⟨.global, 0, 1, 7⟩, false, ⟨0, 0, 0⟩⟩, ⟨0, ⟨.global, 0, 0, 3⟩, false, ⟨0, 0, 0⟩⟩, ⟨0, ⟨.global, 0, 1, 3⟩, false, ⟨0, 0, 0⟩⟩, ⟨0, ⟨.global, 0, 0, 3⟩, false, ⟨0, 0, 0⟩⟩, ⟨0, ⟨.global, 0, 1, 6⟩, false, ⟨0, 0, 0⟩⟩, ⟨0, ⟨.global, 0, 0, 2⟩, false, ⟨0, 0, 0⟩⟩, ⟨0, ⟨.global, 0, 1, 2⟩, false, ⟨0, 0, 0⟩⟩, ⟨0, ⟨.global, 0, 0, 2⟩, false, ⟨0, 0, 0⟩⟩, ⟨0, ⟨.global, 0, 1, 5⟩, false, ⟨0, 0, 0⟩⟩, ⟨0, ⟨.global, 0, 0, 1⟩, false, ⟨0, 0, 0⟩⟩, ⟨0, ⟨.global, 0, 1, 1⟩, false, ⟨0, 0, 0⟩⟩, ⟨0, ⟨.global, 0, 0, 1⟩, false, ⟨0, 0, 0⟩⟩, ⟨0, ⟨.global, 0, 1, 4⟩, false, ⟨0, 0, 0⟩⟩, ⟨0, ⟨.global, 0, 0, 0⟩, false, ⟨0, 0, 0⟩⟩, ⟨0, ⟨.global, 0, 1, 0⟩, false, ⟨0, 0, 0⟩⟩, ⟨0, ⟨.global, 0, 0, 0⟩, false, ⟨0, 0, 0⟩⟩]
def segments : List Segment := [(.seq [(.op (.index 0 .tid)), (.op (.index 1 (.div (.ivar (0)) (.const (2))))), (.op (.index 2 (.mod (.ivar (0)) (.const (2))))), (.op (.assign 0 (.lit (0) 1))), (.op (.assign 1 (.lit (0) 1))), (.op (.index 3 (.const (0)))), (.op (.branch (.lt (.ivar (3)) (.const (4))) 11)), (.op (.assign 0 (.bin .add (.reg (0)) (.bin .mul (.un .fromHalf (.load .global 0 (.add (.mul (.add (.mul (.ivar (1)) (.const (2))) (.ivar (2))) (.const (4))) (.ivar (3))))) (.un .fromHalf (.load .global 1 (.ivar (3)))))))), (.op (.assign 1 (.bin .add (.reg (1)) (.bin .mul (.un .fromHalf (.load .global 0 (.add (.mul (.add (.mul (.ivar (1)) (.const (2))) (.ivar (2))) (.const (4))) (.ivar (3))))) (.un .fromHalf (.load .global 1 (.add (.const (4)) (.ivar (3))))))))), (.op (.index 3 (.add (.ivar (3)) (.const (1))))), (.op (.jump 6)), (.op (.assign 0 (.bin .div (.reg (0)) (.lit (2) 1)))), (.op (.assign 1 (.bin .div (.reg (1)) (.lit (2) 1)))), (.op (.assign 2 (.bin .max (.reg (0)) (.reg (1))))), (.op (.assign 3 (.un .exp (.bin .sub (.reg (0)) (.reg (2)))))), (.op (.assign 4 (.un .exp (.bin .sub (.reg (1)) (.reg (2)))))), (.op (.assign 5 (.bin .add (.bin .add (.lit (0) 1) (.reg (3))) (.reg (4))))), (.op (.index 4 (.const (0)))), (.op (.branch (.lt (.ivar (4)) (.const (4))) 24)), (.op (.assign 6 (.bin .add (.lit (0) 1) (.bin .mul (.bin .div (.reg (3)) (.reg (5))) (.un .fromHalf (.load .global 2 (.ivar (4)))))))), (.op (.assign 6 (.bin .add (.reg (6)) (.bin .mul (.bin .div (.reg (4)) (.reg (5))) (.un .fromHalf (.load .global 2 (.add (.const (4)) (.ivar (4))))))))), (.op (.store .global 3 (.add (.mul (.add (.mul (.ivar (1)) (.const (2))) (.ivar (2))) (.const (4))) (.ivar (4))) (.un .toHalf (.reg (6))))), (.op (.index 4 (.add (.ivar (4)) (.const (1))))), (.op (.jump 18)), (.op .halt)])]
def spec (ops : Ops α) (input : Nat → Nat → α) : List α :=
  [(ops.toHalf (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.div (ops.exp (ops.sub (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 0)) (ops.fromHalf (input 1 0)))) (ops.mul (ops.fromHalf (input 0 1)) (ops.fromHalf (input 1 1)))) (ops.mul (ops.fromHalf (input 0 2)) (ops.fromHalf (input 1 2)))) (ops.mul (ops.fromHalf (input 0 3)) (ops.fromHalf (input 1 3)))) (ops.literal (2) 1)) (ops.max (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 0)) (ops.fromHalf (input 1 0)))) (ops.mul (ops.fromHalf (input 0 1)) (ops.fromHalf (input 1 1)))) (ops.mul (ops.fromHalf (input 0 2)) (ops.fromHalf (input 1 2)))) (ops.mul (ops.fromHalf (input 0 3)) (ops.fromHalf (input 1 3)))) (ops.literal (2) 1)) (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 0)) (ops.fromHalf (input 1 4)))) (ops.mul (ops.fromHalf (input 0 1)) (ops.fromHalf (input 1 5)))) (ops.mul (ops.fromHalf (input 0 2)) (ops.fromHalf (input 1 6)))) (ops.mul (ops.fromHalf (input 0 3)) (ops.fromHalf (input 1 7)))) (ops.literal (2) 1))))) (ops.add (ops.add (ops.literal (0) 1) (ops.exp (ops.sub (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 0)) (ops.fromHalf (input 1 0)))) (ops.mul (ops.fromHalf (input 0 1)) (ops.fromHalf (input 1 1)))) (ops.mul (ops.fromHalf (input 0 2)) (ops.fromHalf (input 1 2)))) (ops.mul (ops.fromHalf (input 0 3)) (ops.fromHalf (input 1 3)))) (ops.literal (2) 1)) (ops.max (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 0)) (ops.fromHalf (input 1 0)))) (ops.mul (ops.fromHalf (input 0 1)) (ops.fromHalf (input 1 1)))) (ops.mul (ops.fromHalf (input 0 2)) (ops.fromHalf (input 1 2)))) (ops.mul (ops.fromHalf (input 0 3)) (ops.fromHalf (input 1 3)))) (ops.literal (2) 1)) (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 0)) (ops.fromHalf (input 1 4)))) (ops.mul (ops.fromHalf (input 0 1)) (ops.fromHalf (input 1 5)))) (ops.mul (ops.fromHalf (input 0 2)) (ops.fromHalf (input 1 6)))) (ops.mul (ops.fromHalf (input 0 3)) (ops.fromHalf (input 1 7)))) (ops.literal (2) 1)))))) (ops.exp (ops.sub (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 0)) (ops.fromHalf (input 1 4)))) (ops.mul (ops.fromHalf (input 0 1)) (ops.fromHalf (input 1 5)))) (ops.mul (ops.fromHalf (input 0 2)) (ops.fromHalf (input 1 6)))) (ops.mul (ops.fromHalf (input 0 3)) (ops.fromHalf (input 1 7)))) (ops.literal (2) 1)) (ops.max (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 0)) (ops.fromHalf (input 1 0)))) (ops.mul (ops.fromHalf (input 0 1)) (ops.fromHalf (input 1 1)))) (ops.mul (ops.fromHalf (input 0 2)) (ops.fromHalf (input 1 2)))) (ops.mul (ops.fromHalf (input 0 3)) (ops.fromHalf (input 1 3)))) (ops.literal (2) 1)) (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 0)) (ops.fromHalf (input 1 4)))) (ops.mul (ops.fromHalf (input 0 1)) (ops.fromHalf (input 1 5)))) (ops.mul (ops.fromHalf (input 0 2)) (ops.fromHalf (input 1 6)))) (ops.mul (ops.fromHalf (input 0 3)) (ops.fromHalf (input 1 7)))) (ops.literal (2) 1))))))) (ops.fromHalf (input 2 0)))) (ops.mul (ops.div (ops.exp (ops.sub (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 0)) (ops.fromHalf (input 1 4)))) (ops.mul (ops.fromHalf (input 0 1)) (ops.fromHalf (input 1 5)))) (ops.mul (ops.fromHalf (input 0 2)) (ops.fromHalf (input 1 6)))) (ops.mul (ops.fromHalf (input 0 3)) (ops.fromHalf (input 1 7)))) (ops.literal (2) 1)) (ops.max (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 0)) (ops.fromHalf (input 1 0)))) (ops.mul (ops.fromHalf (input 0 1)) (ops.fromHalf (input 1 1)))) (ops.mul (ops.fromHalf (input 0 2)) (ops.fromHalf (input 1 2)))) (ops.mul (ops.fromHalf (input 0 3)) (ops.fromHalf (input 1 3)))) (ops.literal (2) 1)) (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 0)) (ops.fromHalf (input 1 4)))) (ops.mul (ops.fromHalf (input 0 1)) (ops.fromHalf (input 1 5)))) (ops.mul (ops.fromHalf (input 0 2)) (ops.fromHalf (input 1 6)))) (ops.mul (ops.fromHalf (input 0 3)) (ops.fromHalf (input 1 7)))) (ops.literal (2) 1))))) (ops.add (ops.add (ops.literal (0) 1) (ops.exp (ops.sub (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 0)) (ops.fromHalf (input 1 0)))) (ops.mul (ops.fromHalf (input 0 1)) (ops.fromHalf (input 1 1)))) (ops.mul (ops.fromHalf (input 0 2)) (ops.fromHalf (input 1 2)))) (ops.mul (ops.fromHalf (input 0 3)) (ops.fromHalf (input 1 3)))) (ops.literal (2) 1)) (ops.max (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 0)) (ops.fromHalf (input 1 0)))) (ops.mul (ops.fromHalf (input 0 1)) (ops.fromHalf (input 1 1)))) (ops.mul (ops.fromHalf (input 0 2)) (ops.fromHalf (input 1 2)))) (ops.mul (ops.fromHalf (input 0 3)) (ops.fromHalf (input 1 3)))) (ops.literal (2) 1)) (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 0)) (ops.fromHalf (input 1 4)))) (ops.mul (ops.fromHalf (input 0 1)) (ops.fromHalf (input 1 5)))) (ops.mul (ops.fromHalf (input 0 2)) (ops.fromHalf (input 1 6)))) (ops.mul (ops.fromHalf (input 0 3)) (ops.fromHalf (input 1 7)))) (ops.literal (2) 1)))))) (ops.exp (ops.sub (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 0)) (ops.fromHalf (input 1 4)))) (ops.mul (ops.fromHalf (input 0 1)) (ops.fromHalf (input 1 5)))) (ops.mul (ops.fromHalf (input 0 2)) (ops.fromHalf (input 1 6)))) (ops.mul (ops.fromHalf (input 0 3)) (ops.fromHalf (input 1 7)))) (ops.literal (2) 1)) (ops.max (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 0)) (ops.fromHalf (input 1 0)))) (ops.mul (ops.fromHalf (input 0 1)) (ops.fromHalf (input 1 1)))) (ops.mul (ops.fromHalf (input 0 2)) (ops.fromHalf (input 1 2)))) (ops.mul (ops.fromHalf (input 0 3)) (ops.fromHalf (input 1 3)))) (ops.literal (2) 1)) (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 0)) (ops.fromHalf (input 1 4)))) (ops.mul (ops.fromHalf (input 0 1)) (ops.fromHalf (input 1 5)))) (ops.mul (ops.fromHalf (input 0 2)) (ops.fromHalf (input 1 6)))) (ops.mul (ops.fromHalf (input 0 3)) (ops.fromHalf (input 1 7)))) (ops.literal (2) 1))))))) (ops.fromHalf (input 2 4))))), (ops.toHalf (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.div (ops.exp (ops.sub (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 0)) (ops.fromHalf (input 1 0)))) (ops.mul (ops.fromHalf (input 0 1)) (ops.fromHalf (input 1 1)))) (ops.mul (ops.fromHalf (input 0 2)) (ops.fromHalf (input 1 2)))) (ops.mul (ops.fromHalf (input 0 3)) (ops.fromHalf (input 1 3)))) (ops.literal (2) 1)) (ops.max (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 0)) (ops.fromHalf (input 1 0)))) (ops.mul (ops.fromHalf (input 0 1)) (ops.fromHalf (input 1 1)))) (ops.mul (ops.fromHalf (input 0 2)) (ops.fromHalf (input 1 2)))) (ops.mul (ops.fromHalf (input 0 3)) (ops.fromHalf (input 1 3)))) (ops.literal (2) 1)) (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 0)) (ops.fromHalf (input 1 4)))) (ops.mul (ops.fromHalf (input 0 1)) (ops.fromHalf (input 1 5)))) (ops.mul (ops.fromHalf (input 0 2)) (ops.fromHalf (input 1 6)))) (ops.mul (ops.fromHalf (input 0 3)) (ops.fromHalf (input 1 7)))) (ops.literal (2) 1))))) (ops.add (ops.add (ops.literal (0) 1) (ops.exp (ops.sub (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 0)) (ops.fromHalf (input 1 0)))) (ops.mul (ops.fromHalf (input 0 1)) (ops.fromHalf (input 1 1)))) (ops.mul (ops.fromHalf (input 0 2)) (ops.fromHalf (input 1 2)))) (ops.mul (ops.fromHalf (input 0 3)) (ops.fromHalf (input 1 3)))) (ops.literal (2) 1)) (ops.max (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 0)) (ops.fromHalf (input 1 0)))) (ops.mul (ops.fromHalf (input 0 1)) (ops.fromHalf (input 1 1)))) (ops.mul (ops.fromHalf (input 0 2)) (ops.fromHalf (input 1 2)))) (ops.mul (ops.fromHalf (input 0 3)) (ops.fromHalf (input 1 3)))) (ops.literal (2) 1)) (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 0)) (ops.fromHalf (input 1 4)))) (ops.mul (ops.fromHalf (input 0 1)) (ops.fromHalf (input 1 5)))) (ops.mul (ops.fromHalf (input 0 2)) (ops.fromHalf (input 1 6)))) (ops.mul (ops.fromHalf (input 0 3)) (ops.fromHalf (input 1 7)))) (ops.literal (2) 1)))))) (ops.exp (ops.sub (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 0)) (ops.fromHalf (input 1 4)))) (ops.mul (ops.fromHalf (input 0 1)) (ops.fromHalf (input 1 5)))) (ops.mul (ops.fromHalf (input 0 2)) (ops.fromHalf (input 1 6)))) (ops.mul (ops.fromHalf (input 0 3)) (ops.fromHalf (input 1 7)))) (ops.literal (2) 1)) (ops.max (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 0)) (ops.fromHalf (input 1 0)))) (ops.mul (ops.fromHalf (input 0 1)) (ops.fromHalf (input 1 1)))) (ops.mul (ops.fromHalf (input 0 2)) (ops.fromHalf (input 1 2)))) (ops.mul (ops.fromHalf (input 0 3)) (ops.fromHalf (input 1 3)))) (ops.literal (2) 1)) (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 0)) (ops.fromHalf (input 1 4)))) (ops.mul (ops.fromHalf (input 0 1)) (ops.fromHalf (input 1 5)))) (ops.mul (ops.fromHalf (input 0 2)) (ops.fromHalf (input 1 6)))) (ops.mul (ops.fromHalf (input 0 3)) (ops.fromHalf (input 1 7)))) (ops.literal (2) 1))))))) (ops.fromHalf (input 2 1)))) (ops.mul (ops.div (ops.exp (ops.sub (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 0)) (ops.fromHalf (input 1 4)))) (ops.mul (ops.fromHalf (input 0 1)) (ops.fromHalf (input 1 5)))) (ops.mul (ops.fromHalf (input 0 2)) (ops.fromHalf (input 1 6)))) (ops.mul (ops.fromHalf (input 0 3)) (ops.fromHalf (input 1 7)))) (ops.literal (2) 1)) (ops.max (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 0)) (ops.fromHalf (input 1 0)))) (ops.mul (ops.fromHalf (input 0 1)) (ops.fromHalf (input 1 1)))) (ops.mul (ops.fromHalf (input 0 2)) (ops.fromHalf (input 1 2)))) (ops.mul (ops.fromHalf (input 0 3)) (ops.fromHalf (input 1 3)))) (ops.literal (2) 1)) (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 0)) (ops.fromHalf (input 1 4)))) (ops.mul (ops.fromHalf (input 0 1)) (ops.fromHalf (input 1 5)))) (ops.mul (ops.fromHalf (input 0 2)) (ops.fromHalf (input 1 6)))) (ops.mul (ops.fromHalf (input 0 3)) (ops.fromHalf (input 1 7)))) (ops.literal (2) 1))))) (ops.add (ops.add (ops.literal (0) 1) (ops.exp (ops.sub (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 0)) (ops.fromHalf (input 1 0)))) (ops.mul (ops.fromHalf (input 0 1)) (ops.fromHalf (input 1 1)))) (ops.mul (ops.fromHalf (input 0 2)) (ops.fromHalf (input 1 2)))) (ops.mul (ops.fromHalf (input 0 3)) (ops.fromHalf (input 1 3)))) (ops.literal (2) 1)) (ops.max (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 0)) (ops.fromHalf (input 1 0)))) (ops.mul (ops.fromHalf (input 0 1)) (ops.fromHalf (input 1 1)))) (ops.mul (ops.fromHalf (input 0 2)) (ops.fromHalf (input 1 2)))) (ops.mul (ops.fromHalf (input 0 3)) (ops.fromHalf (input 1 3)))) (ops.literal (2) 1)) (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 0)) (ops.fromHalf (input 1 4)))) (ops.mul (ops.fromHalf (input 0 1)) (ops.fromHalf (input 1 5)))) (ops.mul (ops.fromHalf (input 0 2)) (ops.fromHalf (input 1 6)))) (ops.mul (ops.fromHalf (input 0 3)) (ops.fromHalf (input 1 7)))) (ops.literal (2) 1)))))) (ops.exp (ops.sub (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 0)) (ops.fromHalf (input 1 4)))) (ops.mul (ops.fromHalf (input 0 1)) (ops.fromHalf (input 1 5)))) (ops.mul (ops.fromHalf (input 0 2)) (ops.fromHalf (input 1 6)))) (ops.mul (ops.fromHalf (input 0 3)) (ops.fromHalf (input 1 7)))) (ops.literal (2) 1)) (ops.max (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 0)) (ops.fromHalf (input 1 0)))) (ops.mul (ops.fromHalf (input 0 1)) (ops.fromHalf (input 1 1)))) (ops.mul (ops.fromHalf (input 0 2)) (ops.fromHalf (input 1 2)))) (ops.mul (ops.fromHalf (input 0 3)) (ops.fromHalf (input 1 3)))) (ops.literal (2) 1)) (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 0)) (ops.fromHalf (input 1 4)))) (ops.mul (ops.fromHalf (input 0 1)) (ops.fromHalf (input 1 5)))) (ops.mul (ops.fromHalf (input 0 2)) (ops.fromHalf (input 1 6)))) (ops.mul (ops.fromHalf (input 0 3)) (ops.fromHalf (input 1 7)))) (ops.literal (2) 1))))))) (ops.fromHalf (input 2 5))))), (ops.toHalf (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.div (ops.exp (ops.sub (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 0)) (ops.fromHalf (input 1 0)))) (ops.mul (ops.fromHalf (input 0 1)) (ops.fromHalf (input 1 1)))) (ops.mul (ops.fromHalf (input 0 2)) (ops.fromHalf (input 1 2)))) (ops.mul (ops.fromHalf (input 0 3)) (ops.fromHalf (input 1 3)))) (ops.literal (2) 1)) (ops.max (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 0)) (ops.fromHalf (input 1 0)))) (ops.mul (ops.fromHalf (input 0 1)) (ops.fromHalf (input 1 1)))) (ops.mul (ops.fromHalf (input 0 2)) (ops.fromHalf (input 1 2)))) (ops.mul (ops.fromHalf (input 0 3)) (ops.fromHalf (input 1 3)))) (ops.literal (2) 1)) (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 0)) (ops.fromHalf (input 1 4)))) (ops.mul (ops.fromHalf (input 0 1)) (ops.fromHalf (input 1 5)))) (ops.mul (ops.fromHalf (input 0 2)) (ops.fromHalf (input 1 6)))) (ops.mul (ops.fromHalf (input 0 3)) (ops.fromHalf (input 1 7)))) (ops.literal (2) 1))))) (ops.add (ops.add (ops.literal (0) 1) (ops.exp (ops.sub (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 0)) (ops.fromHalf (input 1 0)))) (ops.mul (ops.fromHalf (input 0 1)) (ops.fromHalf (input 1 1)))) (ops.mul (ops.fromHalf (input 0 2)) (ops.fromHalf (input 1 2)))) (ops.mul (ops.fromHalf (input 0 3)) (ops.fromHalf (input 1 3)))) (ops.literal (2) 1)) (ops.max (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 0)) (ops.fromHalf (input 1 0)))) (ops.mul (ops.fromHalf (input 0 1)) (ops.fromHalf (input 1 1)))) (ops.mul (ops.fromHalf (input 0 2)) (ops.fromHalf (input 1 2)))) (ops.mul (ops.fromHalf (input 0 3)) (ops.fromHalf (input 1 3)))) (ops.literal (2) 1)) (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 0)) (ops.fromHalf (input 1 4)))) (ops.mul (ops.fromHalf (input 0 1)) (ops.fromHalf (input 1 5)))) (ops.mul (ops.fromHalf (input 0 2)) (ops.fromHalf (input 1 6)))) (ops.mul (ops.fromHalf (input 0 3)) (ops.fromHalf (input 1 7)))) (ops.literal (2) 1)))))) (ops.exp (ops.sub (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 0)) (ops.fromHalf (input 1 4)))) (ops.mul (ops.fromHalf (input 0 1)) (ops.fromHalf (input 1 5)))) (ops.mul (ops.fromHalf (input 0 2)) (ops.fromHalf (input 1 6)))) (ops.mul (ops.fromHalf (input 0 3)) (ops.fromHalf (input 1 7)))) (ops.literal (2) 1)) (ops.max (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 0)) (ops.fromHalf (input 1 0)))) (ops.mul (ops.fromHalf (input 0 1)) (ops.fromHalf (input 1 1)))) (ops.mul (ops.fromHalf (input 0 2)) (ops.fromHalf (input 1 2)))) (ops.mul (ops.fromHalf (input 0 3)) (ops.fromHalf (input 1 3)))) (ops.literal (2) 1)) (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 0)) (ops.fromHalf (input 1 4)))) (ops.mul (ops.fromHalf (input 0 1)) (ops.fromHalf (input 1 5)))) (ops.mul (ops.fromHalf (input 0 2)) (ops.fromHalf (input 1 6)))) (ops.mul (ops.fromHalf (input 0 3)) (ops.fromHalf (input 1 7)))) (ops.literal (2) 1))))))) (ops.fromHalf (input 2 2)))) (ops.mul (ops.div (ops.exp (ops.sub (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 0)) (ops.fromHalf (input 1 4)))) (ops.mul (ops.fromHalf (input 0 1)) (ops.fromHalf (input 1 5)))) (ops.mul (ops.fromHalf (input 0 2)) (ops.fromHalf (input 1 6)))) (ops.mul (ops.fromHalf (input 0 3)) (ops.fromHalf (input 1 7)))) (ops.literal (2) 1)) (ops.max (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 0)) (ops.fromHalf (input 1 0)))) (ops.mul (ops.fromHalf (input 0 1)) (ops.fromHalf (input 1 1)))) (ops.mul (ops.fromHalf (input 0 2)) (ops.fromHalf (input 1 2)))) (ops.mul (ops.fromHalf (input 0 3)) (ops.fromHalf (input 1 3)))) (ops.literal (2) 1)) (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 0)) (ops.fromHalf (input 1 4)))) (ops.mul (ops.fromHalf (input 0 1)) (ops.fromHalf (input 1 5)))) (ops.mul (ops.fromHalf (input 0 2)) (ops.fromHalf (input 1 6)))) (ops.mul (ops.fromHalf (input 0 3)) (ops.fromHalf (input 1 7)))) (ops.literal (2) 1))))) (ops.add (ops.add (ops.literal (0) 1) (ops.exp (ops.sub (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 0)) (ops.fromHalf (input 1 0)))) (ops.mul (ops.fromHalf (input 0 1)) (ops.fromHalf (input 1 1)))) (ops.mul (ops.fromHalf (input 0 2)) (ops.fromHalf (input 1 2)))) (ops.mul (ops.fromHalf (input 0 3)) (ops.fromHalf (input 1 3)))) (ops.literal (2) 1)) (ops.max (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 0)) (ops.fromHalf (input 1 0)))) (ops.mul (ops.fromHalf (input 0 1)) (ops.fromHalf (input 1 1)))) (ops.mul (ops.fromHalf (input 0 2)) (ops.fromHalf (input 1 2)))) (ops.mul (ops.fromHalf (input 0 3)) (ops.fromHalf (input 1 3)))) (ops.literal (2) 1)) (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 0)) (ops.fromHalf (input 1 4)))) (ops.mul (ops.fromHalf (input 0 1)) (ops.fromHalf (input 1 5)))) (ops.mul (ops.fromHalf (input 0 2)) (ops.fromHalf (input 1 6)))) (ops.mul (ops.fromHalf (input 0 3)) (ops.fromHalf (input 1 7)))) (ops.literal (2) 1)))))) (ops.exp (ops.sub (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 0)) (ops.fromHalf (input 1 4)))) (ops.mul (ops.fromHalf (input 0 1)) (ops.fromHalf (input 1 5)))) (ops.mul (ops.fromHalf (input 0 2)) (ops.fromHalf (input 1 6)))) (ops.mul (ops.fromHalf (input 0 3)) (ops.fromHalf (input 1 7)))) (ops.literal (2) 1)) (ops.max (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 0)) (ops.fromHalf (input 1 0)))) (ops.mul (ops.fromHalf (input 0 1)) (ops.fromHalf (input 1 1)))) (ops.mul (ops.fromHalf (input 0 2)) (ops.fromHalf (input 1 2)))) (ops.mul (ops.fromHalf (input 0 3)) (ops.fromHalf (input 1 3)))) (ops.literal (2) 1)) (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 0)) (ops.fromHalf (input 1 4)))) (ops.mul (ops.fromHalf (input 0 1)) (ops.fromHalf (input 1 5)))) (ops.mul (ops.fromHalf (input 0 2)) (ops.fromHalf (input 1 6)))) (ops.mul (ops.fromHalf (input 0 3)) (ops.fromHalf (input 1 7)))) (ops.literal (2) 1))))))) (ops.fromHalf (input 2 6))))), (ops.toHalf (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.div (ops.exp (ops.sub (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 0)) (ops.fromHalf (input 1 0)))) (ops.mul (ops.fromHalf (input 0 1)) (ops.fromHalf (input 1 1)))) (ops.mul (ops.fromHalf (input 0 2)) (ops.fromHalf (input 1 2)))) (ops.mul (ops.fromHalf (input 0 3)) (ops.fromHalf (input 1 3)))) (ops.literal (2) 1)) (ops.max (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 0)) (ops.fromHalf (input 1 0)))) (ops.mul (ops.fromHalf (input 0 1)) (ops.fromHalf (input 1 1)))) (ops.mul (ops.fromHalf (input 0 2)) (ops.fromHalf (input 1 2)))) (ops.mul (ops.fromHalf (input 0 3)) (ops.fromHalf (input 1 3)))) (ops.literal (2) 1)) (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 0)) (ops.fromHalf (input 1 4)))) (ops.mul (ops.fromHalf (input 0 1)) (ops.fromHalf (input 1 5)))) (ops.mul (ops.fromHalf (input 0 2)) (ops.fromHalf (input 1 6)))) (ops.mul (ops.fromHalf (input 0 3)) (ops.fromHalf (input 1 7)))) (ops.literal (2) 1))))) (ops.add (ops.add (ops.literal (0) 1) (ops.exp (ops.sub (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 0)) (ops.fromHalf (input 1 0)))) (ops.mul (ops.fromHalf (input 0 1)) (ops.fromHalf (input 1 1)))) (ops.mul (ops.fromHalf (input 0 2)) (ops.fromHalf (input 1 2)))) (ops.mul (ops.fromHalf (input 0 3)) (ops.fromHalf (input 1 3)))) (ops.literal (2) 1)) (ops.max (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 0)) (ops.fromHalf (input 1 0)))) (ops.mul (ops.fromHalf (input 0 1)) (ops.fromHalf (input 1 1)))) (ops.mul (ops.fromHalf (input 0 2)) (ops.fromHalf (input 1 2)))) (ops.mul (ops.fromHalf (input 0 3)) (ops.fromHalf (input 1 3)))) (ops.literal (2) 1)) (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 0)) (ops.fromHalf (input 1 4)))) (ops.mul (ops.fromHalf (input 0 1)) (ops.fromHalf (input 1 5)))) (ops.mul (ops.fromHalf (input 0 2)) (ops.fromHalf (input 1 6)))) (ops.mul (ops.fromHalf (input 0 3)) (ops.fromHalf (input 1 7)))) (ops.literal (2) 1)))))) (ops.exp (ops.sub (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 0)) (ops.fromHalf (input 1 4)))) (ops.mul (ops.fromHalf (input 0 1)) (ops.fromHalf (input 1 5)))) (ops.mul (ops.fromHalf (input 0 2)) (ops.fromHalf (input 1 6)))) (ops.mul (ops.fromHalf (input 0 3)) (ops.fromHalf (input 1 7)))) (ops.literal (2) 1)) (ops.max (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 0)) (ops.fromHalf (input 1 0)))) (ops.mul (ops.fromHalf (input 0 1)) (ops.fromHalf (input 1 1)))) (ops.mul (ops.fromHalf (input 0 2)) (ops.fromHalf (input 1 2)))) (ops.mul (ops.fromHalf (input 0 3)) (ops.fromHalf (input 1 3)))) (ops.literal (2) 1)) (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 0)) (ops.fromHalf (input 1 4)))) (ops.mul (ops.fromHalf (input 0 1)) (ops.fromHalf (input 1 5)))) (ops.mul (ops.fromHalf (input 0 2)) (ops.fromHalf (input 1 6)))) (ops.mul (ops.fromHalf (input 0 3)) (ops.fromHalf (input 1 7)))) (ops.literal (2) 1))))))) (ops.fromHalf (input 2 3)))) (ops.mul (ops.div (ops.exp (ops.sub (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 0)) (ops.fromHalf (input 1 4)))) (ops.mul (ops.fromHalf (input 0 1)) (ops.fromHalf (input 1 5)))) (ops.mul (ops.fromHalf (input 0 2)) (ops.fromHalf (input 1 6)))) (ops.mul (ops.fromHalf (input 0 3)) (ops.fromHalf (input 1 7)))) (ops.literal (2) 1)) (ops.max (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 0)) (ops.fromHalf (input 1 0)))) (ops.mul (ops.fromHalf (input 0 1)) (ops.fromHalf (input 1 1)))) (ops.mul (ops.fromHalf (input 0 2)) (ops.fromHalf (input 1 2)))) (ops.mul (ops.fromHalf (input 0 3)) (ops.fromHalf (input 1 3)))) (ops.literal (2) 1)) (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 0)) (ops.fromHalf (input 1 4)))) (ops.mul (ops.fromHalf (input 0 1)) (ops.fromHalf (input 1 5)))) (ops.mul (ops.fromHalf (input 0 2)) (ops.fromHalf (input 1 6)))) (ops.mul (ops.fromHalf (input 0 3)) (ops.fromHalf (input 1 7)))) (ops.literal (2) 1))))) (ops.add (ops.add (ops.literal (0) 1) (ops.exp (ops.sub (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 0)) (ops.fromHalf (input 1 0)))) (ops.mul (ops.fromHalf (input 0 1)) (ops.fromHalf (input 1 1)))) (ops.mul (ops.fromHalf (input 0 2)) (ops.fromHalf (input 1 2)))) (ops.mul (ops.fromHalf (input 0 3)) (ops.fromHalf (input 1 3)))) (ops.literal (2) 1)) (ops.max (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 0)) (ops.fromHalf (input 1 0)))) (ops.mul (ops.fromHalf (input 0 1)) (ops.fromHalf (input 1 1)))) (ops.mul (ops.fromHalf (input 0 2)) (ops.fromHalf (input 1 2)))) (ops.mul (ops.fromHalf (input 0 3)) (ops.fromHalf (input 1 3)))) (ops.literal (2) 1)) (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 0)) (ops.fromHalf (input 1 4)))) (ops.mul (ops.fromHalf (input 0 1)) (ops.fromHalf (input 1 5)))) (ops.mul (ops.fromHalf (input 0 2)) (ops.fromHalf (input 1 6)))) (ops.mul (ops.fromHalf (input 0 3)) (ops.fromHalf (input 1 7)))) (ops.literal (2) 1)))))) (ops.exp (ops.sub (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 0)) (ops.fromHalf (input 1 4)))) (ops.mul (ops.fromHalf (input 0 1)) (ops.fromHalf (input 1 5)))) (ops.mul (ops.fromHalf (input 0 2)) (ops.fromHalf (input 1 6)))) (ops.mul (ops.fromHalf (input 0 3)) (ops.fromHalf (input 1 7)))) (ops.literal (2) 1)) (ops.max (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 0)) (ops.fromHalf (input 1 0)))) (ops.mul (ops.fromHalf (input 0 1)) (ops.fromHalf (input 1 1)))) (ops.mul (ops.fromHalf (input 0 2)) (ops.fromHalf (input 1 2)))) (ops.mul (ops.fromHalf (input 0 3)) (ops.fromHalf (input 1 3)))) (ops.literal (2) 1)) (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 0)) (ops.fromHalf (input 1 4)))) (ops.mul (ops.fromHalf (input 0 1)) (ops.fromHalf (input 1 5)))) (ops.mul (ops.fromHalf (input 0 2)) (ops.fromHalf (input 1 6)))) (ops.mul (ops.fromHalf (input 0 3)) (ops.fromHalf (input 1 7)))) (ops.literal (2) 1))))))) (ops.fromHalf (input 2 7))))), (ops.toHalf (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.div (ops.exp (ops.sub (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 4)) (ops.fromHalf (input 1 0)))) (ops.mul (ops.fromHalf (input 0 5)) (ops.fromHalf (input 1 1)))) (ops.mul (ops.fromHalf (input 0 6)) (ops.fromHalf (input 1 2)))) (ops.mul (ops.fromHalf (input 0 7)) (ops.fromHalf (input 1 3)))) (ops.literal (2) 1)) (ops.max (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 4)) (ops.fromHalf (input 1 0)))) (ops.mul (ops.fromHalf (input 0 5)) (ops.fromHalf (input 1 1)))) (ops.mul (ops.fromHalf (input 0 6)) (ops.fromHalf (input 1 2)))) (ops.mul (ops.fromHalf (input 0 7)) (ops.fromHalf (input 1 3)))) (ops.literal (2) 1)) (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 4)) (ops.fromHalf (input 1 4)))) (ops.mul (ops.fromHalf (input 0 5)) (ops.fromHalf (input 1 5)))) (ops.mul (ops.fromHalf (input 0 6)) (ops.fromHalf (input 1 6)))) (ops.mul (ops.fromHalf (input 0 7)) (ops.fromHalf (input 1 7)))) (ops.literal (2) 1))))) (ops.add (ops.add (ops.literal (0) 1) (ops.exp (ops.sub (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 4)) (ops.fromHalf (input 1 0)))) (ops.mul (ops.fromHalf (input 0 5)) (ops.fromHalf (input 1 1)))) (ops.mul (ops.fromHalf (input 0 6)) (ops.fromHalf (input 1 2)))) (ops.mul (ops.fromHalf (input 0 7)) (ops.fromHalf (input 1 3)))) (ops.literal (2) 1)) (ops.max (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 4)) (ops.fromHalf (input 1 0)))) (ops.mul (ops.fromHalf (input 0 5)) (ops.fromHalf (input 1 1)))) (ops.mul (ops.fromHalf (input 0 6)) (ops.fromHalf (input 1 2)))) (ops.mul (ops.fromHalf (input 0 7)) (ops.fromHalf (input 1 3)))) (ops.literal (2) 1)) (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 4)) (ops.fromHalf (input 1 4)))) (ops.mul (ops.fromHalf (input 0 5)) (ops.fromHalf (input 1 5)))) (ops.mul (ops.fromHalf (input 0 6)) (ops.fromHalf (input 1 6)))) (ops.mul (ops.fromHalf (input 0 7)) (ops.fromHalf (input 1 7)))) (ops.literal (2) 1)))))) (ops.exp (ops.sub (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 4)) (ops.fromHalf (input 1 4)))) (ops.mul (ops.fromHalf (input 0 5)) (ops.fromHalf (input 1 5)))) (ops.mul (ops.fromHalf (input 0 6)) (ops.fromHalf (input 1 6)))) (ops.mul (ops.fromHalf (input 0 7)) (ops.fromHalf (input 1 7)))) (ops.literal (2) 1)) (ops.max (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 4)) (ops.fromHalf (input 1 0)))) (ops.mul (ops.fromHalf (input 0 5)) (ops.fromHalf (input 1 1)))) (ops.mul (ops.fromHalf (input 0 6)) (ops.fromHalf (input 1 2)))) (ops.mul (ops.fromHalf (input 0 7)) (ops.fromHalf (input 1 3)))) (ops.literal (2) 1)) (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 4)) (ops.fromHalf (input 1 4)))) (ops.mul (ops.fromHalf (input 0 5)) (ops.fromHalf (input 1 5)))) (ops.mul (ops.fromHalf (input 0 6)) (ops.fromHalf (input 1 6)))) (ops.mul (ops.fromHalf (input 0 7)) (ops.fromHalf (input 1 7)))) (ops.literal (2) 1))))))) (ops.fromHalf (input 2 0)))) (ops.mul (ops.div (ops.exp (ops.sub (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 4)) (ops.fromHalf (input 1 4)))) (ops.mul (ops.fromHalf (input 0 5)) (ops.fromHalf (input 1 5)))) (ops.mul (ops.fromHalf (input 0 6)) (ops.fromHalf (input 1 6)))) (ops.mul (ops.fromHalf (input 0 7)) (ops.fromHalf (input 1 7)))) (ops.literal (2) 1)) (ops.max (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 4)) (ops.fromHalf (input 1 0)))) (ops.mul (ops.fromHalf (input 0 5)) (ops.fromHalf (input 1 1)))) (ops.mul (ops.fromHalf (input 0 6)) (ops.fromHalf (input 1 2)))) (ops.mul (ops.fromHalf (input 0 7)) (ops.fromHalf (input 1 3)))) (ops.literal (2) 1)) (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 4)) (ops.fromHalf (input 1 4)))) (ops.mul (ops.fromHalf (input 0 5)) (ops.fromHalf (input 1 5)))) (ops.mul (ops.fromHalf (input 0 6)) (ops.fromHalf (input 1 6)))) (ops.mul (ops.fromHalf (input 0 7)) (ops.fromHalf (input 1 7)))) (ops.literal (2) 1))))) (ops.add (ops.add (ops.literal (0) 1) (ops.exp (ops.sub (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 4)) (ops.fromHalf (input 1 0)))) (ops.mul (ops.fromHalf (input 0 5)) (ops.fromHalf (input 1 1)))) (ops.mul (ops.fromHalf (input 0 6)) (ops.fromHalf (input 1 2)))) (ops.mul (ops.fromHalf (input 0 7)) (ops.fromHalf (input 1 3)))) (ops.literal (2) 1)) (ops.max (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 4)) (ops.fromHalf (input 1 0)))) (ops.mul (ops.fromHalf (input 0 5)) (ops.fromHalf (input 1 1)))) (ops.mul (ops.fromHalf (input 0 6)) (ops.fromHalf (input 1 2)))) (ops.mul (ops.fromHalf (input 0 7)) (ops.fromHalf (input 1 3)))) (ops.literal (2) 1)) (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 4)) (ops.fromHalf (input 1 4)))) (ops.mul (ops.fromHalf (input 0 5)) (ops.fromHalf (input 1 5)))) (ops.mul (ops.fromHalf (input 0 6)) (ops.fromHalf (input 1 6)))) (ops.mul (ops.fromHalf (input 0 7)) (ops.fromHalf (input 1 7)))) (ops.literal (2) 1)))))) (ops.exp (ops.sub (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 4)) (ops.fromHalf (input 1 4)))) (ops.mul (ops.fromHalf (input 0 5)) (ops.fromHalf (input 1 5)))) (ops.mul (ops.fromHalf (input 0 6)) (ops.fromHalf (input 1 6)))) (ops.mul (ops.fromHalf (input 0 7)) (ops.fromHalf (input 1 7)))) (ops.literal (2) 1)) (ops.max (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 4)) (ops.fromHalf (input 1 0)))) (ops.mul (ops.fromHalf (input 0 5)) (ops.fromHalf (input 1 1)))) (ops.mul (ops.fromHalf (input 0 6)) (ops.fromHalf (input 1 2)))) (ops.mul (ops.fromHalf (input 0 7)) (ops.fromHalf (input 1 3)))) (ops.literal (2) 1)) (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 4)) (ops.fromHalf (input 1 4)))) (ops.mul (ops.fromHalf (input 0 5)) (ops.fromHalf (input 1 5)))) (ops.mul (ops.fromHalf (input 0 6)) (ops.fromHalf (input 1 6)))) (ops.mul (ops.fromHalf (input 0 7)) (ops.fromHalf (input 1 7)))) (ops.literal (2) 1))))))) (ops.fromHalf (input 2 4))))), (ops.toHalf (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.div (ops.exp (ops.sub (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 4)) (ops.fromHalf (input 1 0)))) (ops.mul (ops.fromHalf (input 0 5)) (ops.fromHalf (input 1 1)))) (ops.mul (ops.fromHalf (input 0 6)) (ops.fromHalf (input 1 2)))) (ops.mul (ops.fromHalf (input 0 7)) (ops.fromHalf (input 1 3)))) (ops.literal (2) 1)) (ops.max (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 4)) (ops.fromHalf (input 1 0)))) (ops.mul (ops.fromHalf (input 0 5)) (ops.fromHalf (input 1 1)))) (ops.mul (ops.fromHalf (input 0 6)) (ops.fromHalf (input 1 2)))) (ops.mul (ops.fromHalf (input 0 7)) (ops.fromHalf (input 1 3)))) (ops.literal (2) 1)) (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 4)) (ops.fromHalf (input 1 4)))) (ops.mul (ops.fromHalf (input 0 5)) (ops.fromHalf (input 1 5)))) (ops.mul (ops.fromHalf (input 0 6)) (ops.fromHalf (input 1 6)))) (ops.mul (ops.fromHalf (input 0 7)) (ops.fromHalf (input 1 7)))) (ops.literal (2) 1))))) (ops.add (ops.add (ops.literal (0) 1) (ops.exp (ops.sub (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 4)) (ops.fromHalf (input 1 0)))) (ops.mul (ops.fromHalf (input 0 5)) (ops.fromHalf (input 1 1)))) (ops.mul (ops.fromHalf (input 0 6)) (ops.fromHalf (input 1 2)))) (ops.mul (ops.fromHalf (input 0 7)) (ops.fromHalf (input 1 3)))) (ops.literal (2) 1)) (ops.max (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 4)) (ops.fromHalf (input 1 0)))) (ops.mul (ops.fromHalf (input 0 5)) (ops.fromHalf (input 1 1)))) (ops.mul (ops.fromHalf (input 0 6)) (ops.fromHalf (input 1 2)))) (ops.mul (ops.fromHalf (input 0 7)) (ops.fromHalf (input 1 3)))) (ops.literal (2) 1)) (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 4)) (ops.fromHalf (input 1 4)))) (ops.mul (ops.fromHalf (input 0 5)) (ops.fromHalf (input 1 5)))) (ops.mul (ops.fromHalf (input 0 6)) (ops.fromHalf (input 1 6)))) (ops.mul (ops.fromHalf (input 0 7)) (ops.fromHalf (input 1 7)))) (ops.literal (2) 1)))))) (ops.exp (ops.sub (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 4)) (ops.fromHalf (input 1 4)))) (ops.mul (ops.fromHalf (input 0 5)) (ops.fromHalf (input 1 5)))) (ops.mul (ops.fromHalf (input 0 6)) (ops.fromHalf (input 1 6)))) (ops.mul (ops.fromHalf (input 0 7)) (ops.fromHalf (input 1 7)))) (ops.literal (2) 1)) (ops.max (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 4)) (ops.fromHalf (input 1 0)))) (ops.mul (ops.fromHalf (input 0 5)) (ops.fromHalf (input 1 1)))) (ops.mul (ops.fromHalf (input 0 6)) (ops.fromHalf (input 1 2)))) (ops.mul (ops.fromHalf (input 0 7)) (ops.fromHalf (input 1 3)))) (ops.literal (2) 1)) (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 4)) (ops.fromHalf (input 1 4)))) (ops.mul (ops.fromHalf (input 0 5)) (ops.fromHalf (input 1 5)))) (ops.mul (ops.fromHalf (input 0 6)) (ops.fromHalf (input 1 6)))) (ops.mul (ops.fromHalf (input 0 7)) (ops.fromHalf (input 1 7)))) (ops.literal (2) 1))))))) (ops.fromHalf (input 2 1)))) (ops.mul (ops.div (ops.exp (ops.sub (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 4)) (ops.fromHalf (input 1 4)))) (ops.mul (ops.fromHalf (input 0 5)) (ops.fromHalf (input 1 5)))) (ops.mul (ops.fromHalf (input 0 6)) (ops.fromHalf (input 1 6)))) (ops.mul (ops.fromHalf (input 0 7)) (ops.fromHalf (input 1 7)))) (ops.literal (2) 1)) (ops.max (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 4)) (ops.fromHalf (input 1 0)))) (ops.mul (ops.fromHalf (input 0 5)) (ops.fromHalf (input 1 1)))) (ops.mul (ops.fromHalf (input 0 6)) (ops.fromHalf (input 1 2)))) (ops.mul (ops.fromHalf (input 0 7)) (ops.fromHalf (input 1 3)))) (ops.literal (2) 1)) (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 4)) (ops.fromHalf (input 1 4)))) (ops.mul (ops.fromHalf (input 0 5)) (ops.fromHalf (input 1 5)))) (ops.mul (ops.fromHalf (input 0 6)) (ops.fromHalf (input 1 6)))) (ops.mul (ops.fromHalf (input 0 7)) (ops.fromHalf (input 1 7)))) (ops.literal (2) 1))))) (ops.add (ops.add (ops.literal (0) 1) (ops.exp (ops.sub (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 4)) (ops.fromHalf (input 1 0)))) (ops.mul (ops.fromHalf (input 0 5)) (ops.fromHalf (input 1 1)))) (ops.mul (ops.fromHalf (input 0 6)) (ops.fromHalf (input 1 2)))) (ops.mul (ops.fromHalf (input 0 7)) (ops.fromHalf (input 1 3)))) (ops.literal (2) 1)) (ops.max (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 4)) (ops.fromHalf (input 1 0)))) (ops.mul (ops.fromHalf (input 0 5)) (ops.fromHalf (input 1 1)))) (ops.mul (ops.fromHalf (input 0 6)) (ops.fromHalf (input 1 2)))) (ops.mul (ops.fromHalf (input 0 7)) (ops.fromHalf (input 1 3)))) (ops.literal (2) 1)) (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 4)) (ops.fromHalf (input 1 4)))) (ops.mul (ops.fromHalf (input 0 5)) (ops.fromHalf (input 1 5)))) (ops.mul (ops.fromHalf (input 0 6)) (ops.fromHalf (input 1 6)))) (ops.mul (ops.fromHalf (input 0 7)) (ops.fromHalf (input 1 7)))) (ops.literal (2) 1)))))) (ops.exp (ops.sub (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 4)) (ops.fromHalf (input 1 4)))) (ops.mul (ops.fromHalf (input 0 5)) (ops.fromHalf (input 1 5)))) (ops.mul (ops.fromHalf (input 0 6)) (ops.fromHalf (input 1 6)))) (ops.mul (ops.fromHalf (input 0 7)) (ops.fromHalf (input 1 7)))) (ops.literal (2) 1)) (ops.max (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 4)) (ops.fromHalf (input 1 0)))) (ops.mul (ops.fromHalf (input 0 5)) (ops.fromHalf (input 1 1)))) (ops.mul (ops.fromHalf (input 0 6)) (ops.fromHalf (input 1 2)))) (ops.mul (ops.fromHalf (input 0 7)) (ops.fromHalf (input 1 3)))) (ops.literal (2) 1)) (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 4)) (ops.fromHalf (input 1 4)))) (ops.mul (ops.fromHalf (input 0 5)) (ops.fromHalf (input 1 5)))) (ops.mul (ops.fromHalf (input 0 6)) (ops.fromHalf (input 1 6)))) (ops.mul (ops.fromHalf (input 0 7)) (ops.fromHalf (input 1 7)))) (ops.literal (2) 1))))))) (ops.fromHalf (input 2 5))))), (ops.toHalf (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.div (ops.exp (ops.sub (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 4)) (ops.fromHalf (input 1 0)))) (ops.mul (ops.fromHalf (input 0 5)) (ops.fromHalf (input 1 1)))) (ops.mul (ops.fromHalf (input 0 6)) (ops.fromHalf (input 1 2)))) (ops.mul (ops.fromHalf (input 0 7)) (ops.fromHalf (input 1 3)))) (ops.literal (2) 1)) (ops.max (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 4)) (ops.fromHalf (input 1 0)))) (ops.mul (ops.fromHalf (input 0 5)) (ops.fromHalf (input 1 1)))) (ops.mul (ops.fromHalf (input 0 6)) (ops.fromHalf (input 1 2)))) (ops.mul (ops.fromHalf (input 0 7)) (ops.fromHalf (input 1 3)))) (ops.literal (2) 1)) (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 4)) (ops.fromHalf (input 1 4)))) (ops.mul (ops.fromHalf (input 0 5)) (ops.fromHalf (input 1 5)))) (ops.mul (ops.fromHalf (input 0 6)) (ops.fromHalf (input 1 6)))) (ops.mul (ops.fromHalf (input 0 7)) (ops.fromHalf (input 1 7)))) (ops.literal (2) 1))))) (ops.add (ops.add (ops.literal (0) 1) (ops.exp (ops.sub (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 4)) (ops.fromHalf (input 1 0)))) (ops.mul (ops.fromHalf (input 0 5)) (ops.fromHalf (input 1 1)))) (ops.mul (ops.fromHalf (input 0 6)) (ops.fromHalf (input 1 2)))) (ops.mul (ops.fromHalf (input 0 7)) (ops.fromHalf (input 1 3)))) (ops.literal (2) 1)) (ops.max (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 4)) (ops.fromHalf (input 1 0)))) (ops.mul (ops.fromHalf (input 0 5)) (ops.fromHalf (input 1 1)))) (ops.mul (ops.fromHalf (input 0 6)) (ops.fromHalf (input 1 2)))) (ops.mul (ops.fromHalf (input 0 7)) (ops.fromHalf (input 1 3)))) (ops.literal (2) 1)) (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 4)) (ops.fromHalf (input 1 4)))) (ops.mul (ops.fromHalf (input 0 5)) (ops.fromHalf (input 1 5)))) (ops.mul (ops.fromHalf (input 0 6)) (ops.fromHalf (input 1 6)))) (ops.mul (ops.fromHalf (input 0 7)) (ops.fromHalf (input 1 7)))) (ops.literal (2) 1)))))) (ops.exp (ops.sub (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 4)) (ops.fromHalf (input 1 4)))) (ops.mul (ops.fromHalf (input 0 5)) (ops.fromHalf (input 1 5)))) (ops.mul (ops.fromHalf (input 0 6)) (ops.fromHalf (input 1 6)))) (ops.mul (ops.fromHalf (input 0 7)) (ops.fromHalf (input 1 7)))) (ops.literal (2) 1)) (ops.max (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 4)) (ops.fromHalf (input 1 0)))) (ops.mul (ops.fromHalf (input 0 5)) (ops.fromHalf (input 1 1)))) (ops.mul (ops.fromHalf (input 0 6)) (ops.fromHalf (input 1 2)))) (ops.mul (ops.fromHalf (input 0 7)) (ops.fromHalf (input 1 3)))) (ops.literal (2) 1)) (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 4)) (ops.fromHalf (input 1 4)))) (ops.mul (ops.fromHalf (input 0 5)) (ops.fromHalf (input 1 5)))) (ops.mul (ops.fromHalf (input 0 6)) (ops.fromHalf (input 1 6)))) (ops.mul (ops.fromHalf (input 0 7)) (ops.fromHalf (input 1 7)))) (ops.literal (2) 1))))))) (ops.fromHalf (input 2 2)))) (ops.mul (ops.div (ops.exp (ops.sub (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 4)) (ops.fromHalf (input 1 4)))) (ops.mul (ops.fromHalf (input 0 5)) (ops.fromHalf (input 1 5)))) (ops.mul (ops.fromHalf (input 0 6)) (ops.fromHalf (input 1 6)))) (ops.mul (ops.fromHalf (input 0 7)) (ops.fromHalf (input 1 7)))) (ops.literal (2) 1)) (ops.max (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 4)) (ops.fromHalf (input 1 0)))) (ops.mul (ops.fromHalf (input 0 5)) (ops.fromHalf (input 1 1)))) (ops.mul (ops.fromHalf (input 0 6)) (ops.fromHalf (input 1 2)))) (ops.mul (ops.fromHalf (input 0 7)) (ops.fromHalf (input 1 3)))) (ops.literal (2) 1)) (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 4)) (ops.fromHalf (input 1 4)))) (ops.mul (ops.fromHalf (input 0 5)) (ops.fromHalf (input 1 5)))) (ops.mul (ops.fromHalf (input 0 6)) (ops.fromHalf (input 1 6)))) (ops.mul (ops.fromHalf (input 0 7)) (ops.fromHalf (input 1 7)))) (ops.literal (2) 1))))) (ops.add (ops.add (ops.literal (0) 1) (ops.exp (ops.sub (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 4)) (ops.fromHalf (input 1 0)))) (ops.mul (ops.fromHalf (input 0 5)) (ops.fromHalf (input 1 1)))) (ops.mul (ops.fromHalf (input 0 6)) (ops.fromHalf (input 1 2)))) (ops.mul (ops.fromHalf (input 0 7)) (ops.fromHalf (input 1 3)))) (ops.literal (2) 1)) (ops.max (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 4)) (ops.fromHalf (input 1 0)))) (ops.mul (ops.fromHalf (input 0 5)) (ops.fromHalf (input 1 1)))) (ops.mul (ops.fromHalf (input 0 6)) (ops.fromHalf (input 1 2)))) (ops.mul (ops.fromHalf (input 0 7)) (ops.fromHalf (input 1 3)))) (ops.literal (2) 1)) (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 4)) (ops.fromHalf (input 1 4)))) (ops.mul (ops.fromHalf (input 0 5)) (ops.fromHalf (input 1 5)))) (ops.mul (ops.fromHalf (input 0 6)) (ops.fromHalf (input 1 6)))) (ops.mul (ops.fromHalf (input 0 7)) (ops.fromHalf (input 1 7)))) (ops.literal (2) 1)))))) (ops.exp (ops.sub (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 4)) (ops.fromHalf (input 1 4)))) (ops.mul (ops.fromHalf (input 0 5)) (ops.fromHalf (input 1 5)))) (ops.mul (ops.fromHalf (input 0 6)) (ops.fromHalf (input 1 6)))) (ops.mul (ops.fromHalf (input 0 7)) (ops.fromHalf (input 1 7)))) (ops.literal (2) 1)) (ops.max (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 4)) (ops.fromHalf (input 1 0)))) (ops.mul (ops.fromHalf (input 0 5)) (ops.fromHalf (input 1 1)))) (ops.mul (ops.fromHalf (input 0 6)) (ops.fromHalf (input 1 2)))) (ops.mul (ops.fromHalf (input 0 7)) (ops.fromHalf (input 1 3)))) (ops.literal (2) 1)) (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 4)) (ops.fromHalf (input 1 4)))) (ops.mul (ops.fromHalf (input 0 5)) (ops.fromHalf (input 1 5)))) (ops.mul (ops.fromHalf (input 0 6)) (ops.fromHalf (input 1 6)))) (ops.mul (ops.fromHalf (input 0 7)) (ops.fromHalf (input 1 7)))) (ops.literal (2) 1))))))) (ops.fromHalf (input 2 6))))), (ops.toHalf (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.div (ops.exp (ops.sub (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 4)) (ops.fromHalf (input 1 0)))) (ops.mul (ops.fromHalf (input 0 5)) (ops.fromHalf (input 1 1)))) (ops.mul (ops.fromHalf (input 0 6)) (ops.fromHalf (input 1 2)))) (ops.mul (ops.fromHalf (input 0 7)) (ops.fromHalf (input 1 3)))) (ops.literal (2) 1)) (ops.max (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 4)) (ops.fromHalf (input 1 0)))) (ops.mul (ops.fromHalf (input 0 5)) (ops.fromHalf (input 1 1)))) (ops.mul (ops.fromHalf (input 0 6)) (ops.fromHalf (input 1 2)))) (ops.mul (ops.fromHalf (input 0 7)) (ops.fromHalf (input 1 3)))) (ops.literal (2) 1)) (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 4)) (ops.fromHalf (input 1 4)))) (ops.mul (ops.fromHalf (input 0 5)) (ops.fromHalf (input 1 5)))) (ops.mul (ops.fromHalf (input 0 6)) (ops.fromHalf (input 1 6)))) (ops.mul (ops.fromHalf (input 0 7)) (ops.fromHalf (input 1 7)))) (ops.literal (2) 1))))) (ops.add (ops.add (ops.literal (0) 1) (ops.exp (ops.sub (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 4)) (ops.fromHalf (input 1 0)))) (ops.mul (ops.fromHalf (input 0 5)) (ops.fromHalf (input 1 1)))) (ops.mul (ops.fromHalf (input 0 6)) (ops.fromHalf (input 1 2)))) (ops.mul (ops.fromHalf (input 0 7)) (ops.fromHalf (input 1 3)))) (ops.literal (2) 1)) (ops.max (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 4)) (ops.fromHalf (input 1 0)))) (ops.mul (ops.fromHalf (input 0 5)) (ops.fromHalf (input 1 1)))) (ops.mul (ops.fromHalf (input 0 6)) (ops.fromHalf (input 1 2)))) (ops.mul (ops.fromHalf (input 0 7)) (ops.fromHalf (input 1 3)))) (ops.literal (2) 1)) (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 4)) (ops.fromHalf (input 1 4)))) (ops.mul (ops.fromHalf (input 0 5)) (ops.fromHalf (input 1 5)))) (ops.mul (ops.fromHalf (input 0 6)) (ops.fromHalf (input 1 6)))) (ops.mul (ops.fromHalf (input 0 7)) (ops.fromHalf (input 1 7)))) (ops.literal (2) 1)))))) (ops.exp (ops.sub (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 4)) (ops.fromHalf (input 1 4)))) (ops.mul (ops.fromHalf (input 0 5)) (ops.fromHalf (input 1 5)))) (ops.mul (ops.fromHalf (input 0 6)) (ops.fromHalf (input 1 6)))) (ops.mul (ops.fromHalf (input 0 7)) (ops.fromHalf (input 1 7)))) (ops.literal (2) 1)) (ops.max (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 4)) (ops.fromHalf (input 1 0)))) (ops.mul (ops.fromHalf (input 0 5)) (ops.fromHalf (input 1 1)))) (ops.mul (ops.fromHalf (input 0 6)) (ops.fromHalf (input 1 2)))) (ops.mul (ops.fromHalf (input 0 7)) (ops.fromHalf (input 1 3)))) (ops.literal (2) 1)) (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 4)) (ops.fromHalf (input 1 4)))) (ops.mul (ops.fromHalf (input 0 5)) (ops.fromHalf (input 1 5)))) (ops.mul (ops.fromHalf (input 0 6)) (ops.fromHalf (input 1 6)))) (ops.mul (ops.fromHalf (input 0 7)) (ops.fromHalf (input 1 7)))) (ops.literal (2) 1))))))) (ops.fromHalf (input 2 3)))) (ops.mul (ops.div (ops.exp (ops.sub (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 4)) (ops.fromHalf (input 1 4)))) (ops.mul (ops.fromHalf (input 0 5)) (ops.fromHalf (input 1 5)))) (ops.mul (ops.fromHalf (input 0 6)) (ops.fromHalf (input 1 6)))) (ops.mul (ops.fromHalf (input 0 7)) (ops.fromHalf (input 1 7)))) (ops.literal (2) 1)) (ops.max (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 4)) (ops.fromHalf (input 1 0)))) (ops.mul (ops.fromHalf (input 0 5)) (ops.fromHalf (input 1 1)))) (ops.mul (ops.fromHalf (input 0 6)) (ops.fromHalf (input 1 2)))) (ops.mul (ops.fromHalf (input 0 7)) (ops.fromHalf (input 1 3)))) (ops.literal (2) 1)) (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 4)) (ops.fromHalf (input 1 4)))) (ops.mul (ops.fromHalf (input 0 5)) (ops.fromHalf (input 1 5)))) (ops.mul (ops.fromHalf (input 0 6)) (ops.fromHalf (input 1 6)))) (ops.mul (ops.fromHalf (input 0 7)) (ops.fromHalf (input 1 7)))) (ops.literal (2) 1))))) (ops.add (ops.add (ops.literal (0) 1) (ops.exp (ops.sub (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 4)) (ops.fromHalf (input 1 0)))) (ops.mul (ops.fromHalf (input 0 5)) (ops.fromHalf (input 1 1)))) (ops.mul (ops.fromHalf (input 0 6)) (ops.fromHalf (input 1 2)))) (ops.mul (ops.fromHalf (input 0 7)) (ops.fromHalf (input 1 3)))) (ops.literal (2) 1)) (ops.max (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 4)) (ops.fromHalf (input 1 0)))) (ops.mul (ops.fromHalf (input 0 5)) (ops.fromHalf (input 1 1)))) (ops.mul (ops.fromHalf (input 0 6)) (ops.fromHalf (input 1 2)))) (ops.mul (ops.fromHalf (input 0 7)) (ops.fromHalf (input 1 3)))) (ops.literal (2) 1)) (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 4)) (ops.fromHalf (input 1 4)))) (ops.mul (ops.fromHalf (input 0 5)) (ops.fromHalf (input 1 5)))) (ops.mul (ops.fromHalf (input 0 6)) (ops.fromHalf (input 1 6)))) (ops.mul (ops.fromHalf (input 0 7)) (ops.fromHalf (input 1 7)))) (ops.literal (2) 1)))))) (ops.exp (ops.sub (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 4)) (ops.fromHalf (input 1 4)))) (ops.mul (ops.fromHalf (input 0 5)) (ops.fromHalf (input 1 5)))) (ops.mul (ops.fromHalf (input 0 6)) (ops.fromHalf (input 1 6)))) (ops.mul (ops.fromHalf (input 0 7)) (ops.fromHalf (input 1 7)))) (ops.literal (2) 1)) (ops.max (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 4)) (ops.fromHalf (input 1 0)))) (ops.mul (ops.fromHalf (input 0 5)) (ops.fromHalf (input 1 1)))) (ops.mul (ops.fromHalf (input 0 6)) (ops.fromHalf (input 1 2)))) (ops.mul (ops.fromHalf (input 0 7)) (ops.fromHalf (input 1 3)))) (ops.literal (2) 1)) (ops.div (ops.add (ops.add (ops.add (ops.add (ops.literal (0) 1) (ops.mul (ops.fromHalf (input 0 4)) (ops.fromHalf (input 1 4)))) (ops.mul (ops.fromHalf (input 0 5)) (ops.fromHalf (input 1 5)))) (ops.mul (ops.fromHalf (input 0 6)) (ops.fromHalf (input 1 6)))) (ops.mul (ops.fromHalf (input 0 7)) (ops.fromHalf (input 1 7)))) (ops.literal (2) 1))))))) (ops.fromHalf (input 2 7)))))]

def finalState (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) : State α :=
  (runLaunch ops layout geometry fuel program (initial layout input outside)).getD
    (initial layout input outside)

theorem segmentation_data : flatten segments = program :=
  by rfl

theorem segmentation (ops : Ops α) (s : State α) :
    runLaunch ops layout geometry fuel program s =
    runLaunch ops layout geometry fuel (flatten segments) s := by
  rw [segmentation_data]

def unitOps : Ops Unit := ⟨fun _ _ => (), fun _ _ => (), fun _ _ => (),
  fun _ _ => (), fun _ _ => (), fun _ _ => (), fun _ => (), fun _ => (), fun _ => (), fun _ => (), fun _ => ()⟩

theorem race_free : ∃ final,
    runLaunch unitOps layout geometry fuel program
      (initial layout (fun _ _ => ()) (fun _ => some ())) = some final ∧
    raceFree geometry final.trace = true :=
  by refine ⟨finalState unitOps (fun _ _ => ()) (fun _ => some ()), ?_, ?_⟩ <;> rfl

theorem segment_equivalence (ops : Ops α) :
    Correct ops layout geometry fuel (flatten segments) (spec ops) :=
  by intro input outside; exact ⟨finalState ops input outside, rfl, rfl, rfl⟩

theorem kernel_eq_spec (ops : Ops α) :
    Correct ops layout geometry fuel program (spec ops) := by
  exact assemble ops layout geometry fuel program segments (spec ops)
    segmentation_data (segment_equivalence ops)

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
