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

namespace NonlinearCalibration
open LarkNonlinear
set_option maxRecDepth 100000
def ops : Ops Float := ⟨fun n d => Float.ofInt n / Float.ofNat d,
 (· + ·), (· - ·), (· * ·), fun a b => if a < b then b else a,
 (· / ·), Float.exp, Float.tanh, fun a => 1.0 / Float.sqrt a,
 id, id⟩
-- Half conversions are not evaluated in this Float interpretation; the hardware
-- conversion probe uses a separate Python IEEE binary16 oracle.
def pairs : List (Float × Float) := [((Float.ofInt (0) / Float.ofNat 1),(Float.ofInt (1) / Float.ofNat 1048576)), ((Float.ofInt (1) / Float.ofNat 1),(Float.ofInt (1) / Float.ofNat 1024)), ((Float.ofInt (-1) / Float.ofNat 1),(Float.ofInt (1) / Float.ofNat 1)), ((Float.ofInt (10) / Float.ofNat 1),(Float.ofInt (1024) / Float.ofNat 1)), ((Float.ofInt (-10) / Float.ofNat 1),(Float.ofInt (1048576) / Float.ofNat 1)), ((Float.ofInt (5) / Float.ofNat 16),(Float.ofInt (909) / Float.ofNat 64)), ((Float.ofInt (-141) / Float.ofNat 16),(Float.ofInt (107) / Float.ofNat 64)), ((Float.ofInt (113) / Float.ofNat 32),(Float.ofInt (247) / Float.ofNat 32)), ((Float.ofInt (123) / Float.ofNat 16),(Float.ofInt (227) / Float.ofNat 16)), ((Float.ofInt (-35) / Float.ofNat 4),(Float.ofInt (189) / Float.ofNat 16)), ((Float.ofInt (13) / Float.ofNat 4),(Float.ofInt (391) / Float.ofNat 64)), ((Float.ofInt (-57) / Float.ofNat 16),(Float.ofInt (343) / Float.ofNat 64)), ((Float.ofInt (49) / Float.ofNat 8),(Float.ofInt (91) / Float.ofNat 64)), ((Float.ofInt (73) / Float.ofNat 16),(Float.ofInt (6) / Float.ofNat 1)), ((Float.ofInt (-47) / Float.ofNat 8),(Float.ofInt (429) / Float.ofNat 32)), ((Float.ofInt (191) / Float.ofNat 32),(Float.ofInt (19) / Float.ofNat 64)), ((Float.ofInt (-69) / Float.ofNat 8),(Float.ofInt (71) / Float.ofNat 8)), ((Float.ofInt (69) / Float.ofNat 16),(Float.ofInt (191) / Float.ofNat 16)), ((Float.ofInt (93) / Float.ofNat 16),(Float.ofInt (837) / Float.ofNat 64)), ((Float.ofInt (51) / Float.ofNat 32),(Float.ofInt (271) / Float.ofNat 64)), ((Float.ofInt (21) / Float.ofNat 4),(Float.ofInt (837) / Float.ofNat 64)), ((Float.ofInt (-3) / Float.ofNat 2),(Float.ofInt (499) / Float.ofNat 32)), ((Float.ofInt (65) / Float.ofNat 8),(Float.ofInt (583) / Float.ofNat 64)), ((Float.ofInt (-15) / Float.ofNat 32),(Float.ofInt (493) / Float.ofNat 64)), ((Float.ofInt (-17) / Float.ofNat 2),(Float.ofInt (231) / Float.ofNat 64)), ((Float.ofInt (-9) / Float.ofNat 2),(Float.ofInt (501) / Float.ofNat 32)), ((Float.ofInt (-99) / Float.ofNat 16),(Float.ofInt (387) / Float.ofNat 64)), ((Float.ofInt (-191) / Float.ofNat 32),(Float.ofInt (705) / Float.ofNat 64)), ((Float.ofInt (65) / Float.ofNat 8),(Float.ofInt (143) / Float.ofNat 16)), ((Float.ofInt (-21) / Float.ofNat 16),(Float.ofInt (817) / Float.ofNat 64)), ((Float.ofInt (-105) / Float.ofNat 32),(Float.ofInt (33) / Float.ofNat 4)), ((Float.ofInt (-111) / Float.ofNat 32),(Float.ofInt (291) / Float.ofNat 32)), ((Float.ofInt (-5) / Float.ofNat 8),(Float.ofInt (135) / Float.ofNat 16)), ((Float.ofInt (109) / Float.ofNat 16),(Float.ofInt (11) / Float.ofNat 2)), ((Float.ofInt (247) / Float.ofNat 32),(Float.ofInt (1009) / Float.ofNat 64)), ((Float.ofInt (-43) / Float.ofNat 8),(Float.ofInt (147) / Float.ofNat 64)), ((Float.ofInt (-7) / Float.ofNat 32),(Float.ofInt (489) / Float.ofNat 32)), ((Float.ofInt (7) / Float.ofNat 2),(Float.ofInt (115) / Float.ofNat 64)), ((Float.ofInt (155) / Float.ofNat 16),(Float.ofInt (65) / Float.ofNat 64)), ((Float.ofInt (-131) / Float.ofNat 32),(Float.ofInt (481) / Float.ofNat 64)), ((Float.ofInt (-263) / Float.ofNat 32),(Float.ofInt (343) / Float.ofNat 32)), ((Float.ofInt (-191) / Float.ofNat 32),(Float.ofInt (763) / Float.ofNat 64)), ((Float.ofInt (-15) / Float.ofNat 4),(Float.ofInt (249) / Float.ofNat 32)), ((Float.ofInt (147) / Float.ofNat 16),(Float.ofInt (155) / Float.ofNat 32)), ((Float.ofInt (-11) / Float.ofNat 8),(Float.ofInt (263) / Float.ofNat 64)), ((Float.ofInt (-83) / Float.ofNat 16),(Float.ofInt (427) / Float.ofNat 32)), ((Float.ofInt (-147) / Float.ofNat 16),(Float.ofInt (583) / Float.ofNat 64)), ((Float.ofInt (-319) / Float.ofNat 32),(Float.ofInt (635) / Float.ofNat 64)), ((Float.ofInt (185) / Float.ofNat 32),(Float.ofInt (11) / Float.ofNat 64)), ((Float.ofInt (-137) / Float.ofNat 16),(Float.ofInt (17) / Float.ofNat 32)), ((Float.ofInt (-287) / Float.ofNat 32),(Float.ofInt (219) / Float.ofNat 64)), ((Float.ofInt (-241) / Float.ofNat 32),(Float.ofInt (445) / Float.ofNat 64)), ((Float.ofInt (-3) / Float.ofNat 32),(Float.ofInt (23) / Float.ofNat 4)), ((Float.ofInt (-121) / Float.ofNat 16),(Float.ofInt (71) / Float.ofNat 16)), ((Float.ofInt (-89) / Float.ofNat 16),(Float.ofInt (385) / Float.ofNat 32)), ((Float.ofInt (7) / Float.ofNat 1),(Float.ofInt (105) / Float.ofNat 64)), ((Float.ofInt (77) / Float.ofNat 16),(Float.ofInt (1005) / Float.ofNat 64)), ((Float.ofInt (33) / Float.ofNat 32),(Float.ofInt (487) / Float.ofNat 32)), ((Float.ofInt (25) / Float.ofNat 8),(Float.ofInt (65) / Float.ofNat 64)), ((Float.ofInt (173) / Float.ofNat 32),(Float.ofInt (413) / Float.ofNat 32)), ((Float.ofInt (-77) / Float.ofNat 8),(Float.ofInt (295) / Float.ofNat 64)), ((Float.ofInt (-5) / Float.ofNat 8),(Float.ofInt (25) / Float.ofNat 8)), ((Float.ofInt (75) / Float.ofNat 16),(Float.ofInt (325) / Float.ofNat 64)), ((Float.ofInt (-237) / Float.ofNat 32),(Float.ofInt (195) / Float.ofNat 64)), ((Float.ofInt (-31) / Float.ofNat 8),(Float.ofInt (315) / Float.ofNat 64)), ((Float.ofInt (-4) / Float.ofNat 1),(Float.ofInt (485) / Float.ofNat 64)), ((Float.ofInt (-61) / Float.ofNat 8),(Float.ofInt (143) / Float.ofNat 64)), ((Float.ofInt (-103) / Float.ofNat 32),(Float.ofInt (101) / Float.ofNat 32)), ((Float.ofInt (-125) / Float.ofNat 32),(Float.ofInt (745) / Float.ofNat 64)), ((Float.ofInt (-141) / Float.ofNat 32),(Float.ofInt (391) / Float.ofNat 64)), ((Float.ofInt (-307) / Float.ofNat 32),(Float.ofInt (341) / Float.ofNat 64)), ((Float.ofInt (141) / Float.ofNat 32),(Float.ofInt (991) / Float.ofNat 64)), ((Float.ofInt (-7) / Float.ofNat 2),(Float.ofInt (761) / Float.ofNat 64)), ((Float.ofInt (-191) / Float.ofNat 32),(Float.ofInt (61) / Float.ofNat 32)), ((Float.ofInt (-47) / Float.ofNat 16),(Float.ofInt (307) / Float.ofNat 64)), ((Float.ofInt (-235) / Float.ofNat 32),(Float.ofInt (623) / Float.ofNat 64)), ((Float.ofInt (-91) / Float.ofNat 32),(Float.ofInt (1003) / Float.ofNat 64)), ((Float.ofInt (-5) / Float.ofNat 1),(Float.ofInt (627) / Float.ofNat 64)), ((Float.ofInt (203) / Float.ofNat 32),(Float.ofInt (329) / Float.ofNat 64)), ((Float.ofInt (289) / Float.ofNat 32),(Float.ofInt (545) / Float.ofNat 64)), ((Float.ofInt (263) / Float.ofNat 32),(Float.ofInt (5) / Float.ofNat 16)), ((Float.ofInt (-123) / Float.ofNat 32),(Float.ofInt (991) / Float.ofNat 64)), ((Float.ofInt (-275) / Float.ofNat 32),(Float.ofInt (609) / Float.ofNat 64)), ((Float.ofInt (-133) / Float.ofNat 16),(Float.ofInt (7) / Float.ofNat 16)), ((Float.ofInt (-17) / Float.ofNat 16),(Float.ofInt (365) / Float.ofNat 64)), ((Float.ofInt (3) / Float.ofNat 32),(Float.ofInt (569) / Float.ofNat 64)), ((Float.ofInt (-287) / Float.ofNat 32),(Float.ofInt (363) / Float.ofNat 64)), ((Float.ofInt (2) / Float.ofNat 1),(Float.ofInt (955) / Float.ofNat 64)), ((Float.ofInt (-11) / Float.ofNat 4),(Float.ofInt (617) / Float.ofNat 64)), ((Float.ofInt (211) / Float.ofNat 32),(Float.ofInt (771) / Float.ofNat 64)), ((Float.ofInt (99) / Float.ofNat 32),(Float.ofInt (63) / Float.ofNat 8)), ((Float.ofInt (219) / Float.ofNat 32),(Float.ofInt (161) / Float.ofNat 16)), ((Float.ofInt (-79) / Float.ofNat 16),(Float.ofInt (2) / Float.ofNat 1)), ((Float.ofInt (289) / Float.ofNat 32),(Float.ofInt (323) / Float.ofNat 64)), ((Float.ofInt (-99) / Float.ofNat 32),(Float.ofInt (233) / Float.ofNat 16)), ((Float.ofInt (-69) / Float.ofNat 16),(Float.ofInt (141) / Float.ofNat 32)), ((Float.ofInt (-63) / Float.ofNat 16),(Float.ofInt (211) / Float.ofNat 16)), ((Float.ofInt (-79) / Float.ofNat 16),(Float.ofInt (5) / Float.ofNat 16)), ((Float.ofInt (-309) / Float.ofNat 32),(Float.ofInt (289) / Float.ofNat 64)), ((Float.ofInt (109) / Float.ofNat 32),(Float.ofInt (83) / Float.ofNat 32)), ((Float.ofInt (35) / Float.ofNat 32),(Float.ofInt (475) / Float.ofNat 32)), ((Float.ofInt (81) / Float.ofNat 16),(Float.ofInt (669) / Float.ofNat 64)), ((Float.ofInt (-65) / Float.ofNat 32),(Float.ofInt (379) / Float.ofNat 64)), ((Float.ofInt (95) / Float.ofNat 32),(Float.ofInt (847) / Float.ofNat 64)), ((Float.ofInt (-47) / Float.ofNat 16),(Float.ofInt (95) / Float.ofNat 8)), ((Float.ofInt (39) / Float.ofNat 16),(Float.ofInt (853) / Float.ofNat 64)), ((Float.ofInt (7) / Float.ofNat 32),(Float.ofInt (299) / Float.ofNat 64)), ((Float.ofInt (37) / Float.ofNat 16),(Float.ofInt (39) / Float.ofNat 8)), ((Float.ofInt (-7) / Float.ofNat 8),(Float.ofInt (53) / Float.ofNat 4)), ((Float.ofInt (145) / Float.ofNat 16),(Float.ofInt (547) / Float.ofNat 64)), ((Float.ofInt (-59) / Float.ofNat 32),(Float.ofInt (949) / Float.ofNat 64)), ((Float.ofInt (163) / Float.ofNat 32),(Float.ofInt (455) / Float.ofNat 32)), ((Float.ofInt (3) / Float.ofNat 16),(Float.ofInt (687) / Float.ofNat 64)), ((Float.ofInt (3) / Float.ofNat 16),(Float.ofInt (661) / Float.ofNat 64)), ((Float.ofInt (289) / Float.ofNat 32),(Float.ofInt (117) / Float.ofNat 32)), ((Float.ofInt (47) / Float.ofNat 16),(Float.ofInt (69) / Float.ofNat 16)), ((Float.ofInt (-251) / Float.ofNat 32),(Float.ofInt (473) / Float.ofNat 64)), ((Float.ofInt (-81) / Float.ofNat 16),(Float.ofInt (421) / Float.ofNat 32)), ((Float.ofInt (-119) / Float.ofNat 32),(Float.ofInt (149) / Float.ofNat 64)), ((Float.ofInt (-129) / Float.ofNat 16),(Float.ofInt (71) / Float.ofNat 32)), ((Float.ofInt (-77) / Float.ofNat 8),(Float.ofInt (125) / Float.ofNat 64)), ((Float.ofInt (-271) / Float.ofNat 32),(Float.ofInt (237) / Float.ofNat 16)), ((Float.ofInt (-203) / Float.ofNat 32),(Float.ofInt (7) / Float.ofNat 64)), ((Float.ofInt (-6) / Float.ofNat 1),(Float.ofInt (13) / Float.ofNat 16)), ((Float.ofInt (3) / Float.ofNat 32),(Float.ofInt (31) / Float.ofNat 8)), ((Float.ofInt (-117) / Float.ofNat 32),(Float.ofInt (765) / Float.ofNat 64)), ((Float.ofInt (27) / Float.ofNat 16),(Float.ofInt (231) / Float.ofNat 16)), ((Float.ofInt (-101) / Float.ofNat 32),(Float.ofInt (407) / Float.ofNat 32)), ((Float.ofInt (35) / Float.ofNat 8),(Float.ofInt (921) / Float.ofNat 64)), ((Float.ofInt (-197) / Float.ofNat 32),(Float.ofInt (483) / Float.ofNat 64)), ((Float.ofInt (9) / Float.ofNat 1),(Float.ofInt (777) / Float.ofNat 64)), ((Float.ofInt (65) / Float.ofNat 16),(Float.ofInt (657) / Float.ofNat 64)), ((Float.ofInt (107) / Float.ofNat 32),(Float.ofInt (485) / Float.ofNat 32)), ((Float.ofInt (17) / Float.ofNat 4),(Float.ofInt (287) / Float.ofNat 32)), ((Float.ofInt (35) / Float.ofNat 4),(Float.ofInt (209) / Float.ofNat 32)), ((Float.ofInt (-123) / Float.ofNat 32),(Float.ofInt (37) / Float.ofNat 16)), ((Float.ofInt (57) / Float.ofNat 32),(Float.ofInt (401) / Float.ofNat 32)), ((Float.ofInt (33) / Float.ofNat 16),(Float.ofInt (13) / Float.ofNat 32)), ((Float.ofInt (-43) / Float.ofNat 16),(Float.ofInt (12) / Float.ofNat 1)), ((Float.ofInt (-233) / Float.ofNat 32),(Float.ofInt (493) / Float.ofNat 64)), ((Float.ofInt (-47) / Float.ofNat 8),(Float.ofInt (163) / Float.ofNat 32)), ((Float.ofInt (177) / Float.ofNat 32),(Float.ofInt (183) / Float.ofNat 32)), ((Float.ofInt (-265) / Float.ofNat 32),(Float.ofInt (55) / Float.ofNat 64)), ((Float.ofInt (173) / Float.ofNat 32),(Float.ofInt (455) / Float.ofNat 64)), ((Float.ofInt (149) / Float.ofNat 16),(Float.ofInt (687) / Float.ofNat 64)), ((Float.ofInt (-149) / Float.ofNat 16),(Float.ofInt (373) / Float.ofNat 32)), ((Float.ofInt (175) / Float.ofNat 32),(Float.ofInt (151) / Float.ofNat 32)), ((Float.ofInt (-317) / Float.ofNat 32),(Float.ofInt (841) / Float.ofNat 64)), ((Float.ofInt (123) / Float.ofNat 32),(Float.ofInt (285) / Float.ofNat 64)), ((Float.ofInt (75) / Float.ofNat 16),(Float.ofInt (373) / Float.ofNat 32)), ((Float.ofInt (-241) / Float.ofNat 32),(Float.ofInt (43) / Float.ofNat 32)), ((Float.ofInt (71) / Float.ofNat 32),(Float.ofInt (753) / Float.ofNat 64)), ((Float.ofInt (-29) / Float.ofNat 4),(Float.ofInt (61) / Float.ofNat 8)), ((Float.ofInt (133) / Float.ofNat 16),(Float.ofInt (385) / Float.ofNat 32)), ((Float.ofInt (61) / Float.ofNat 8),(Float.ofInt (115) / Float.ofNat 8)), ((Float.ofInt (217) / Float.ofNat 32),(Float.ofInt (591) / Float.ofNat 64)), ((Float.ofInt (5) / Float.ofNat 2),(Float.ofInt (201) / Float.ofNat 64)), ((Float.ofInt (85) / Float.ofNat 16),(Float.ofInt (55) / Float.ofNat 32)), ((Float.ofInt (-57) / Float.ofNat 32),(Float.ofInt (591) / Float.ofNat 64)), ((Float.ofInt (-141) / Float.ofNat 32),(Float.ofInt (213) / Float.ofNat 32)), ((Float.ofInt (-313) / Float.ofNat 32),(Float.ofInt (935) / Float.ofNat 64)), ((Float.ofInt (-75) / Float.ofNat 8),(Float.ofInt (211) / Float.ofNat 64)), ((Float.ofInt (285) / Float.ofNat 32),(Float.ofInt (849) / Float.ofNat 64)), ((Float.ofInt (-135) / Float.ofNat 32),(Float.ofInt (449) / Float.ofNat 32)), ((Float.ofInt (83) / Float.ofNat 16),(Float.ofInt (523) / Float.ofNat 64)), ((Float.ofInt (-115) / Float.ofNat 16),(Float.ofInt (353) / Float.ofNat 64)), ((Float.ofInt (89) / Float.ofNat 32),(Float.ofInt (37) / Float.ofNat 4)), ((Float.ofInt (9) / Float.ofNat 2),(Float.ofInt (329) / Float.ofNat 32)), ((Float.ofInt (-31) / Float.ofNat 32),(Float.ofInt (491) / Float.ofNat 32)), ((Float.ofInt (115) / Float.ofNat 32),(Float.ofInt (77) / Float.ofNat 16)), ((Float.ofInt (303) / Float.ofNat 32),(Float.ofInt (23) / Float.ofNat 64)), ((Float.ofInt (-75) / Float.ofNat 8),(Float.ofInt (13) / Float.ofNat 1)), ((Float.ofInt (-105) / Float.ofNat 32),(Float.ofInt (137) / Float.ofNat 16)), ((Float.ofInt (-41) / Float.ofNat 16),(Float.ofInt (5) / Float.ofNat 4)), ((Float.ofInt (9) / Float.ofNat 2),(Float.ofInt (41) / Float.ofNat 16)), ((Float.ofInt (177) / Float.ofNat 32),(Float.ofInt (457) / Float.ofNat 32)), ((Float.ofInt (-31) / Float.ofNat 4),(Float.ofInt (197) / Float.ofNat 64)), ((Float.ofInt (35) / Float.ofNat 16),(Float.ofInt (967) / Float.ofNat 64)), ((Float.ofInt (15) / Float.ofNat 2),(Float.ofInt (207) / Float.ofNat 64)), ((Float.ofInt (129) / Float.ofNat 32),(Float.ofInt (335) / Float.ofNat 64)), ((Float.ofInt (61) / Float.ofNat 32),(Float.ofInt (887) / Float.ofNat 64)), ((Float.ofInt (-119) / Float.ofNat 16),(Float.ofInt (403) / Float.ofNat 64)), ((Float.ofInt (47) / Float.ofNat 8),(Float.ofInt (91) / Float.ofNat 32)), ((Float.ofInt (155) / Float.ofNat 32),(Float.ofInt (441) / Float.ofNat 64)), ((Float.ofInt (5) / Float.ofNat 8),(Float.ofInt (465) / Float.ofNat 64)), ((Float.ofInt (-21) / Float.ofNat 32),(Float.ofInt (373) / Float.ofNat 32)), ((Float.ofInt (-9) / Float.ofNat 1),(Float.ofInt (225) / Float.ofNat 64)), ((Float.ofInt (-15) / Float.ofNat 8),(Float.ofInt (255) / Float.ofNat 64)), ((Float.ofInt (-19) / Float.ofNat 2),(Float.ofInt (13) / Float.ofNat 4)), ((Float.ofInt (141) / Float.ofNat 16),(Float.ofInt (717) / Float.ofNat 64)), ((Float.ofInt (-5) / Float.ofNat 8),(Float.ofInt (117) / Float.ofNat 16)), ((Float.ofInt (-31) / Float.ofNat 8),(Float.ofInt (145) / Float.ofNat 16)), ((Float.ofInt (-33) / Float.ofNat 16),(Float.ofInt (455) / Float.ofNat 64)), ((Float.ofInt (-197) / Float.ofNat 32),(Float.ofInt (43) / Float.ofNat 32)), ((Float.ofInt (-69) / Float.ofNat 16),(Float.ofInt (33) / Float.ofNat 16)), ((Float.ofInt (-305) / Float.ofNat 32),(Float.ofInt (5) / Float.ofNat 32)), ((Float.ofInt (269) / Float.ofNat 32),(Float.ofInt (393) / Float.ofNat 64)), ((Float.ofInt (1) / Float.ofNat 8),(Float.ofInt (91) / Float.ofNat 64)), ((Float.ofInt (-1) / Float.ofNat 4),(Float.ofInt (99) / Float.ofNat 16)), ((Float.ofInt (17) / Float.ofNat 4),(Float.ofInt (109) / Float.ofNat 16)), ((Float.ofInt (-129) / Float.ofNat 16),(Float.ofInt (353) / Float.ofNat 64)), ((Float.ofInt (27) / Float.ofNat 32),(Float.ofInt (373) / Float.ofNat 32)), ((Float.ofInt (77) / Float.ofNat 16),(Float.ofInt (533) / Float.ofNat 64)), ((Float.ofInt (129) / Float.ofNat 16),(Float.ofInt (283) / Float.ofNat 64)), ((Float.ofInt (-163) / Float.ofNat 32),(Float.ofInt (117) / Float.ofNat 64)), ((Float.ofInt (73) / Float.ofNat 8),(Float.ofInt (141) / Float.ofNat 32)), ((Float.ofInt (69) / Float.ofNat 16),(Float.ofInt (115) / Float.ofNat 16)), ((Float.ofInt (75) / Float.ofNat 32),(Float.ofInt (23) / Float.ofNat 16)), ((Float.ofInt (-11) / Float.ofNat 2),(Float.ofInt (151) / Float.ofNat 16)), ((Float.ofInt (-29) / Float.ofNat 4),(Float.ofInt (131) / Float.ofNat 16)), ((Float.ofInt (165) / Float.ofNat 32),(Float.ofInt (341) / Float.ofNat 64)), ((Float.ofInt (7) / Float.ofNat 4),(Float.ofInt (455) / Float.ofNat 32)), ((Float.ofInt (173) / Float.ofNat 32),(Float.ofInt (105) / Float.ofNat 8)), ((Float.ofInt (-265) / Float.ofNat 32),(Float.ofInt (91) / Float.ofNat 16)), ((Float.ofInt (53) / Float.ofNat 16),(Float.ofInt (275) / Float.ofNat 64)), ((Float.ofInt (53) / Float.ofNat 32),(Float.ofInt (717) / Float.ofNat 64)), ((Float.ofInt (111) / Float.ofNat 16),(Float.ofInt (425) / Float.ofNat 64)), ((Float.ofInt (-65) / Float.ofNat 32),(Float.ofInt (919) / Float.ofNat 64)), ((Float.ofInt (15) / Float.ofNat 8),(Float.ofInt (305) / Float.ofNat 64)), ((Float.ofInt (141) / Float.ofNat 16),(Float.ofInt (811) / Float.ofNat 64)), ((Float.ofInt (-21) / Float.ofNat 8),(Float.ofInt (117) / Float.ofNat 32)), ((Float.ofInt (-9) / Float.ofNat 1),(Float.ofInt (799) / Float.ofNat 64)), ((Float.ofInt (-17) / Float.ofNat 32),(Float.ofInt (201) / Float.ofNat 16)), ((Float.ofInt (37) / Float.ofNat 32),(Float.ofInt (691) / Float.ofNat 64)), ((Float.ofInt (0) / Float.ofNat 1),(Float.ofInt (77) / Float.ofNat 8)), ((Float.ofInt (-113) / Float.ofNat 16),(Float.ofInt (893) / Float.ofNat 64)), ((Float.ofInt (287) / Float.ofNat 32),(Float.ofInt (773) / Float.ofNat 64)), ((Float.ofInt (-257) / Float.ofNat 32),(Float.ofInt (675) / Float.ofNat 64)), ((Float.ofInt (221) / Float.ofNat 32),(Float.ofInt (203) / Float.ofNat 32)), ((Float.ofInt (51) / Float.ofNat 8),(Float.ofInt (465) / Float.ofNat 64)), ((Float.ofInt (67) / Float.ofNat 8),(Float.ofInt (413) / Float.ofNat 32)), ((Float.ofInt (13) / Float.ofNat 8),(Float.ofInt (483) / Float.ofNat 32)), ((Float.ofInt (-11) / Float.ofNat 32),(Float.ofInt (3) / Float.ofNat 32)), ((Float.ofInt (-207) / Float.ofNat 32),(Float.ofInt (133) / Float.ofNat 16)), ((Float.ofInt (-149) / Float.ofNat 16),(Float.ofInt (143) / Float.ofNat 32)), ((Float.ofInt (157) / Float.ofNat 16),(Float.ofInt (311) / Float.ofNat 64)), ((Float.ofInt (7) / Float.ofNat 8),(Float.ofInt (469) / Float.ofNat 32)), ((Float.ofInt (17) / Float.ofNat 32),(Float.ofInt (75) / Float.ofNat 8)), ((Float.ofInt (135) / Float.ofNat 16),(Float.ofInt (19) / Float.ofNat 64)), ((Float.ofInt (183) / Float.ofNat 32),(Float.ofInt (111) / Float.ofNat 32)), ((Float.ofInt (-105) / Float.ofNat 16),(Float.ofInt (489) / Float.ofNat 32)), ((Float.ofInt (-183) / Float.ofNat 32),(Float.ofInt (403) / Float.ofNat 64)), ((Float.ofInt (-5) / Float.ofNat 1),(Float.ofInt (429) / Float.ofNat 64)), ((Float.ofInt (-141) / Float.ofNat 32),(Float.ofInt (205) / Float.ofNat 32)), ((Float.ofInt (121) / Float.ofNat 16),(Float.ofInt (325) / Float.ofNat 64)), ((Float.ofInt (7) / Float.ofNat 2),(Float.ofInt (79) / Float.ofNat 16)), ((Float.ofInt (251) / Float.ofNat 32),(Float.ofInt (117) / Float.ofNat 16)), ((Float.ofInt (-139) / Float.ofNat 32),(Float.ofInt (479) / Float.ofNat 64)), ((Float.ofInt (143) / Float.ofNat 16),(Float.ofInt (53) / Float.ofNat 4)), ((Float.ofInt (53) / Float.ofNat 32),(Float.ofInt (713) / Float.ofNat 64)), ((Float.ofInt (157) / Float.ofNat 32),(Float.ofInt (95) / Float.ofNat 8)), ((Float.ofInt (-95) / Float.ofNat 32),(Float.ofInt (15) / Float.ofNat 1)), ((Float.ofInt (-225) / Float.ofNat 32),(Float.ofInt (473) / Float.ofNat 32)), ((Float.ofInt (-87) / Float.ofNat 16),(Float.ofInt (359) / Float.ofNat 64)), ((Float.ofInt (-243) / Float.ofNat 32),(Float.ofInt (187) / Float.ofNat 64)), ((Float.ofInt (63) / Float.ofNat 16),(Float.ofInt (437) / Float.ofNat 32))]
#eval pairs.map (fun (a,b) => (applyBinary ops .div a b).toBits.toNat)
#eval pairs.map (fun (a,_) => (applyUnary ops .exp a).toBits.toNat)
#eval pairs.map (fun (a,_) => (applyUnary ops .tanh a).toBits.toNat)
#eval pairs.map (fun (_,b) => (applyUnary ops .rsqrt b).toBits.toNat)
end NonlinearCalibration
