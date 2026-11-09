import Std

/-!
Pinned, dependency-free machine model for the bounded scalar profile.
Scalar arithmetic is universally quantified: the certificate holds for EVERY
interpretation of literal/add/sub/mul/max, including exact real arithmetic.
Addresses and control depend only on exact integer index expressions.
-/
namespace Lark

structure Ops (α : Type) where
  literal : Int → Nat → α
  add : α → α → α
  sub : α → α → α
  mul : α → α → α
  max : α → α → α

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
  | add | sub | mul | max
  deriving DecidableEq, Repr

inductive Expr where
  | lit : Int → Nat → Expr
  | reg : Nat → Expr
  | load : Space → Nat → Index → Expr
  | bin : Binary → Expr → Expr → Expr
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

end Lark

namespace Calibration
open Lark
set_option maxRecDepth 100000
def ops : Ops Float := ⟨fun n d => Float.ofInt n / Float.ofNat d,
  (· + ·), (· - ·), (· * ·), fun a b => if a < b then b else a⟩
def pairs : List (Float × Float) := [((Float.ofInt (0) / Float.ofNat 1), (Float.ofInt (1048576) / Float.ofNat 1)), ((Float.ofInt (1) / Float.ofNat 1), (Float.ofInt (-1048576) / Float.ofNat 1)), ((Float.ofInt (-1) / Float.ofNat 1), (Float.ofInt (1024) / Float.ofNat 1)), ((Float.ofInt (-1) / Float.ofNat 1048576), (Float.ofInt (-1024) / Float.ofNat 1)), ((Float.ofInt (1) / Float.ofNat 1048576), (Float.ofInt (1) / Float.ofNat 1)), ((Float.ofInt (-1) / Float.ofNat 1024), (Float.ofInt (-1) / Float.ofNat 1)), ((Float.ofInt (1) / Float.ofNat 1024), (Float.ofInt (1) / Float.ofNat 1024)), ((Float.ofInt (-1) / Float.ofNat 1), (Float.ofInt (-1) / Float.ofNat 1024)), ((Float.ofInt (1) / Float.ofNat 1), (Float.ofInt (1) / Float.ofNat 1048576)), ((Float.ofInt (-1024) / Float.ofNat 1), (Float.ofInt (-1) / Float.ofNat 1048576)), ((Float.ofInt (1024) / Float.ofNat 1), (Float.ofInt (-1) / Float.ofNat 1)), ((Float.ofInt (-1048576) / Float.ofNat 1), (Float.ofInt (1) / Float.ofNat 1)), ((Float.ofInt (1048576) / Float.ofNat 1), (Float.ofInt (0) / Float.ofNat 1)), ((Float.ofInt (19085) / Float.ofNat 256), (Float.ofInt (-57333) / Float.ofNat 256)), ((Float.ofInt (-55651) / Float.ofNat 256), (Float.ofInt (-507) / Float.ofNat 32)), ((Float.ofInt (45363) / Float.ofNat 256), (Float.ofInt (22221) / Float.ofNat 256)), ((Float.ofInt (-27559) / Float.ofNat 128), (Float.ofInt (32077) / Float.ofNat 256)), ((Float.ofInt (21611) / Float.ofNat 128), (Float.ofInt (-1879) / Float.ofNat 256)), ((Float.ofInt (-12777) / Float.ofNat 256), (Float.ofInt (-12961) / Float.ofNat 128)), ((Float.ofInt (54009) / Float.ofNat 256), (Float.ofInt (-15941) / Float.ofNat 128)), ((Float.ofInt (-15769) / Float.ofNat 128), (Float.ofInt (21827) / Float.ofNat 128)), ((Float.ofInt (32667) / Float.ofNat 128), (Float.ofInt (2255) / Float.ofNat 64)), ((Float.ofInt (-54247) / Float.ofNat 256), (Float.ofInt (3929) / Float.ofNat 64)), ((Float.ofInt (6489) / Float.ofNat 32), (Float.ofInt (-64181) / Float.ofNat 256)), ((Float.ofInt (64147) / Float.ofNat 256), (Float.ofInt (-15313) / Float.ofNat 64)), ((Float.ofInt (14741) / Float.ofNat 128), (Float.ofInt (-18795) / Float.ofNat 128)), ((Float.ofInt (59435) / Float.ofNat 256), (Float.ofInt (-8579) / Float.ofNat 256)), ((Float.ofInt (4229) / Float.ofNat 256), (Float.ofInt (-18555) / Float.ofNat 256)), ((Float.ofInt (6311) / Float.ofNat 128), (Float.ofInt (-29257) / Float.ofNat 256)), ((Float.ofInt (-13305) / Float.ofNat 64), (Float.ofInt (16501) / Float.ofNat 128)), ((Float.ofInt (-159) / Float.ofNat 2), (Float.ofInt (-52217) / Float.ofNat 256)), ((Float.ofInt (-34291) / Float.ofNat 256), (Float.ofInt (1969) / Float.ofNat 8)), ((Float.ofInt (-8077) / Float.ofNat 64), (Float.ofInt (14783) / Float.ofNat 64)), ((Float.ofInt (2909) / Float.ofNat 128), (Float.ofInt (-57293) / Float.ofNat 256)), ((Float.ofInt (-10275) / Float.ofNat 256), (Float.ofInt (20071) / Float.ofNat 128)), ((Float.ofInt (-5937) / Float.ofNat 128), (Float.ofInt (-27805) / Float.ofNat 256)), ((Float.ofInt (11309) / Float.ofNat 256), (Float.ofInt (-39957) / Float.ofNat 256)), ((Float.ofInt (-27423) / Float.ofNat 256), (Float.ofInt (-12019) / Float.ofNat 128)), ((Float.ofInt (7303) / Float.ofNat 128), (Float.ofInt (-20337) / Float.ofNat 128)), ((Float.ofInt (45231) / Float.ofNat 256), (Float.ofInt (-12617) / Float.ofNat 128)), ((Float.ofInt (-16907) / Float.ofNat 256), (Float.ofInt (-447) / Float.ofNat 32)), ((Float.ofInt (-25453) / Float.ofNat 128), (Float.ofInt (-23645) / Float.ofNat 128)), ((Float.ofInt (-2029) / Float.ofNat 16), (Float.ofInt (-39725) / Float.ofNat 256)), ((Float.ofInt (-14247) / Float.ofNat 256), (Float.ofInt (29745) / Float.ofNat 256)), ((Float.ofInt (5307) / Float.ofNat 256), (Float.ofInt (-15601) / Float.ofNat 256)), ((Float.ofInt (-13043) / Float.ofNat 128), (Float.ofInt (-21967) / Float.ofNat 256)), ((Float.ofInt (-29351) / Float.ofNat 128), (Float.ofInt (61241) / Float.ofNat 256)), ((Float.ofInt (-65065) / Float.ofNat 256), (Float.ofInt (31869) / Float.ofNat 256)), ((Float.ofInt (7979) / Float.ofNat 32), (Float.ofInt (-6249) / Float.ofNat 32)), ((Float.ofInt (-53565) / Float.ofNat 256), (Float.ofInt (-26295) / Float.ofNat 256)), ((Float.ofInt (-28429) / Float.ofNat 128), (Float.ofInt (14125) / Float.ofNat 256)), ((Float.ofInt (-11307) / Float.ofNat 64), (Float.ofInt (245) / Float.ofNat 1)), ((Float.ofInt (7913) / Float.ofNat 128), (Float.ofInt (14689) / Float.ofNat 256)), ((Float.ofInt (-45357) / Float.ofNat 256), (Float.ofInt (-23495) / Float.ofNat 256)), ((Float.ofInt (-7295) / Float.ofNat 64), (Float.ofInt (1029) / Float.ofNat 64)), ((Float.ofInt (55851) / Float.ofNat 256), (Float.ofInt (-15769) / Float.ofNat 64)), ((Float.ofInt (12465) / Float.ofNat 128), (Float.ofInt (15299) / Float.ofNat 64)), ((Float.ofInt (42121) / Float.ofNat 256), (Float.ofInt (12413) / Float.ofNat 256)), ((Float.ofInt (60725) / Float.ofNat 256), (Float.ofInt (-31013) / Float.ofNat 128)), ((Float.ofInt (-62273) / Float.ofNat 256), (Float.ofInt (-18909) / Float.ofNat 256)), ((Float.ofInt (11355) / Float.ofNat 256), (Float.ofInt (7285) / Float.ofNat 256)), ((Float.ofInt (27411) / Float.ofNat 128), (Float.ofInt (-19123) / Float.ofNat 256)), ((Float.ofInt (-44143) / Float.ofNat 256), (Float.ofInt (14161) / Float.ofNat 64)), ((Float.ofInt (-3837) / Float.ofNat 64), (Float.ofInt (3329) / Float.ofNat 64)), ((Float.ofInt (-16311) / Float.ofNat 256), (Float.ofInt (33025) / Float.ofNat 256)), ((Float.ofInt (-45869) / Float.ofNat 256), (Float.ofInt (-263) / Float.ofNat 64)), ((Float.ofInt (-2473) / Float.ofNat 64), (Float.ofInt (16785) / Float.ofNat 256)), ((Float.ofInt (-15363) / Float.ofNat 256), (Float.ofInt (-24579) / Float.ofNat 128)), ((Float.ofInt (-9783) / Float.ofNat 128), (Float.ofInt (-24259) / Float.ofNat 256)), ((Float.ofInt (-61959) / Float.ofNat 256), (Float.ofInt (6719) / Float.ofNat 32)), ((Float.ofInt (52733) / Float.ofNat 256), (Float.ofInt (-7383) / Float.ofNat 64)), ((Float.ofInt (-12129) / Float.ofNat 256), (Float.ofInt (42459) / Float.ofNat 256)), ((Float.ofInt (-32449) / Float.ofNat 256), (Float.ofInt (-63057) / Float.ofNat 256)), ((Float.ofInt (-1919) / Float.ofNat 64), (Float.ofInt (-447) / Float.ofNat 4)), ((Float.ofInt (-43521) / Float.ofNat 256), (Float.ofInt (-44413) / Float.ofNat 256)), ((Float.ofInt (-6707) / Float.ofNat 256), (Float.ofInt (55981) / Float.ofNat 256)), ((Float.ofInt (-3063) / Float.ofNat 32), (Float.ofInt (20091) / Float.ofNat 256)), ((Float.ofInt (-7531) / Float.ofNat 128), (Float.ofInt (-8565) / Float.ofNat 128)), ((Float.ofInt (-211) / Float.ofNat 1), (Float.ofInt (21387) / Float.ofNat 128)), ((Float.ofInt (-3223) / Float.ofNat 16), (Float.ofInt (31691) / Float.ofNat 256)), ((Float.ofInt (983) / Float.ofNat 32), (Float.ofInt (21775) / Float.ofNat 128)), ((Float.ofInt (4321) / Float.ofNat 64), (Float.ofInt (-27299) / Float.ofNat 256)), ((Float.ofInt (-28501) / Float.ofNat 128), (Float.ofInt (-803) / Float.ofNat 8)), ((Float.ofInt (16385) / Float.ofNat 128), (Float.ofInt (5373) / Float.ofNat 32)), ((Float.ofInt (-6109) / Float.ofNat 256), (Float.ofInt (4381) / Float.ofNat 256)), ((Float.ofInt (20887) / Float.ofNat 128), (Float.ofInt (55905) / Float.ofNat 256)), ((Float.ofInt (-23921) / Float.ofNat 256), (Float.ofInt (25423) / Float.ofNat 128)), ((Float.ofInt (-8799) / Float.ofNat 256), (Float.ofInt (11145) / Float.ofNat 128)), ((Float.ofInt (-4681) / Float.ofNat 64), (Float.ofInt (19023) / Float.ofNat 256)), ((Float.ofInt (-15827) / Float.ofNat 256), (Float.ofInt (-35667) / Float.ofNat 256)), ((Float.ofInt (-23915) / Float.ofNat 256), (Float.ofInt (-30259) / Float.ofNat 256)), ((Float.ofInt (-31273) / Float.ofNat 128), (Float.ofInt (-5109) / Float.ofNat 256)), ((Float.ofInt (44367) / Float.ofNat 256), (Float.ofInt (42165) / Float.ofNat 256)), ((Float.ofInt (25389) / Float.ofNat 256), (Float.ofInt (-11641) / Float.ofNat 64)), ((Float.ofInt (58035) / Float.ofNat 256), (Float.ofInt (-5923) / Float.ofNat 32)), ((Float.ofInt (-29) / Float.ofNat 128), (Float.ofInt (-49575) / Float.ofNat 256)), ((Float.ofInt (40807) / Float.ofNat 256), (Float.ofInt (55807) / Float.ofNat 256)), ((Float.ofInt (-7465) / Float.ofNat 256), (Float.ofInt (-64741) / Float.ofNat 256)), ((Float.ofInt (4569) / Float.ofNat 32), (Float.ofInt (-58981) / Float.ofNat 256)), ((Float.ofInt (18295) / Float.ofNat 256), (Float.ofInt (-2119) / Float.ofNat 16)), ((Float.ofInt (35557) / Float.ofNat 256), (Float.ofInt (32371) / Float.ofNat 256)), ((Float.ofInt (4661) / Float.ofNat 128), (Float.ofInt (13155) / Float.ofNat 64)), ((Float.ofInt (91) / Float.ofNat 16), (Float.ofInt (38581) / Float.ofNat 256)), ((Float.ofInt (14555) / Float.ofNat 64), (Float.ofInt (52309) / Float.ofNat 256)), ((Float.ofInt (17943) / Float.ofNat 256), (Float.ofInt (-3727) / Float.ofNat 256)), ((Float.ofInt (17977) / Float.ofNat 256), (Float.ofInt (8459) / Float.ofNat 64)), ((Float.ofInt (2539) / Float.ofNat 16), (Float.ofInt (9247) / Float.ofNat 128)), ((Float.ofInt (-373) / Float.ofNat 2), (Float.ofInt (3657) / Float.ofNat 16)), ((Float.ofInt (-12501) / Float.ofNat 128), (Float.ofInt (7811) / Float.ofNat 256)), ((Float.ofInt (-14025) / Float.ofNat 256), (Float.ofInt (-12043) / Float.ofNat 256)), ((Float.ofInt (-6197) / Float.ofNat 32), (Float.ofInt (-2917) / Float.ofNat 16)), ((Float.ofInt (-15607) / Float.ofNat 64), (Float.ofInt (4635) / Float.ofNat 32)), ((Float.ofInt (-26377) / Float.ofNat 128), (Float.ofInt (-15573) / Float.ofNat 64)), ((Float.ofInt (-17737) / Float.ofNat 128), (Float.ofInt (8177) / Float.ofNat 64)), ((Float.ofInt (-4083) / Float.ofNat 32), (Float.ofInt (-2467) / Float.ofNat 256)), ((Float.ofInt (17205) / Float.ofNat 256), (Float.ofInt (-23907) / Float.ofNat 256)), ((Float.ofInt (-13565) / Float.ofNat 256), (Float.ofInt (-4699) / Float.ofNat 64)), ((Float.ofInt (7555) / Float.ofNat 64), (Float.ofInt (-58543) / Float.ofNat 256)), ((Float.ofInt (-9319) / Float.ofNat 256), (Float.ofInt (-29) / Float.ofNat 1)), ((Float.ofInt (52301) / Float.ofNat 256), (Float.ofInt (11199) / Float.ofNat 128)), ((Float.ofInt (-16925) / Float.ofNat 128), (Float.ofInt (14935) / Float.ofNat 128)), ((Float.ofInt (24933) / Float.ofNat 128), (Float.ofInt (-27007) / Float.ofNat 256)), ((Float.ofInt (21891) / Float.ofNat 128), (Float.ofInt (42099) / Float.ofNat 256)), ((Float.ofInt (6427) / Float.ofNat 32), (Float.ofInt (-29093) / Float.ofNat 256)), ((Float.ofInt (-14907) / Float.ofNat 256), (Float.ofInt (29851) / Float.ofNat 256)), ((Float.ofInt (31073) / Float.ofNat 256), (Float.ofInt (-27309) / Float.ofNat 128)), ((Float.ofInt (523) / Float.ofNat 4), (Float.ofInt (30723) / Float.ofNat 256)), ((Float.ofInt (-2693) / Float.ofNat 128), (Float.ofInt (-3103) / Float.ofNat 256)), ((Float.ofInt (-43101) / Float.ofNat 256), (Float.ofInt (8231) / Float.ofNat 64)), ((Float.ofInt (-31499) / Float.ofNat 256), (Float.ofInt (1631) / Float.ofNat 8)), ((Float.ofInt (61915) / Float.ofNat 256), (Float.ofInt (5029) / Float.ofNat 128)), ((Float.ofInt (-12809) / Float.ofNat 64), (Float.ofInt (-2491) / Float.ofNat 16)), ((Float.ofInt (30383) / Float.ofNat 128), (Float.ofInt (-51473) / Float.ofNat 256)), ((Float.ofInt (-59773) / Float.ofNat 256), (Float.ofInt (10059) / Float.ofNat 256)), ((Float.ofInt (61401) / Float.ofNat 256), (Float.ofInt (-11089) / Float.ofNat 256)), ((Float.ofInt (-64699) / Float.ofNat 256), (Float.ofInt (54097) / Float.ofNat 256)), ((Float.ofInt (1499) / Float.ofNat 8), (Float.ofInt (-38579) / Float.ofNat 256)), ((Float.ofInt (54999) / Float.ofNat 256), (Float.ofInt (43055) / Float.ofNat 256)), ((Float.ofInt (-22633) / Float.ofNat 128), (Float.ofInt (12349) / Float.ofNat 64)), ((Float.ofInt (17307) / Float.ofNat 128), (Float.ofInt (329) / Float.ofNat 64)), ((Float.ofInt (-42865) / Float.ofNat 256), (Float.ofInt (-20425) / Float.ofNat 256)), ((Float.ofInt (18471) / Float.ofNat 128), (Float.ofInt (10131) / Float.ofNat 256)), ((Float.ofInt (60027) / Float.ofNat 256), (Float.ofInt (9327) / Float.ofNat 128)), ((Float.ofInt (457) / Float.ofNat 64), (Float.ofInt (60119) / Float.ofNat 256)), ((Float.ofInt (-9853) / Float.ofNat 128), (Float.ofInt (-6557) / Float.ofNat 64)), ((Float.ofInt (-63495) / Float.ofNat 256), (Float.ofInt (-62611) / Float.ofNat 256)), ((Float.ofInt (-15053) / Float.ofNat 64), (Float.ofInt (40923) / Float.ofNat 256)), ((Float.ofInt (-17957) / Float.ofNat 256), (Float.ofInt (4483) / Float.ofNat 256)), ((Float.ofInt (59115) / Float.ofNat 256), (Float.ofInt (-13827) / Float.ofNat 64)), ((Float.ofInt (-42359) / Float.ofNat 256), (Float.ofInt (-44617) / Float.ofNat 256)), ((Float.ofInt (39347) / Float.ofNat 256), (Float.ofInt (51345) / Float.ofNat 256)), ((Float.ofInt (53395) / Float.ofNat 256), (Float.ofInt (-10111) / Float.ofNat 64)), ((Float.ofInt (8499) / Float.ofNat 256), (Float.ofInt (58175) / Float.ofNat 256)), ((Float.ofInt (46031) / Float.ofNat 256), (Float.ofInt (-9769) / Float.ofNat 64)), ((Float.ofInt (-30127) / Float.ofNat 128), (Float.ofInt (-22705) / Float.ofNat 256)), ((Float.ofInt (-5139) / Float.ofNat 128), (Float.ofInt (47929) / Float.ofNat 256)), ((Float.ofInt (-4505) / Float.ofNat 256), (Float.ofInt (-1755) / Float.ofNat 32)), ((Float.ofInt (13339) / Float.ofNat 64), (Float.ofInt (-42349) / Float.ofNat 256)), ((Float.ofInt (30957) / Float.ofNat 128), (Float.ofInt (-9175) / Float.ofNat 256)), ((Float.ofInt (-11743) / Float.ofNat 64), (Float.ofInt (-6069) / Float.ofNat 256)), ((Float.ofInt (17159) / Float.ofNat 128), (Float.ofInt (7477) / Float.ofNat 64)), ((Float.ofInt (24711) / Float.ofNat 128), (Float.ofInt (-36783) / Float.ofNat 256)), ((Float.ofInt (8027) / Float.ofNat 64), (Float.ofInt (-32943) / Float.ofNat 256)), ((Float.ofInt (-2777) / Float.ofNat 16), (Float.ofInt (-38967) / Float.ofNat 256)), ((Float.ofInt (64733) / Float.ofNat 256), (Float.ofInt (26229) / Float.ofNat 256)), ((Float.ofInt (56241) / Float.ofNat 256), (Float.ofInt (-5657) / Float.ofNat 256)), ((Float.ofInt (21557) / Float.ofNat 256), (Float.ofInt (8669) / Float.ofNat 256)), ((Float.ofInt (5625) / Float.ofNat 128), (Float.ofInt (-7371) / Float.ofNat 256)), ((Float.ofInt (-28647) / Float.ofNat 128), (Float.ofInt (-13655) / Float.ofNat 64)), ((Float.ofInt (1215) / Float.ofNat 256), (Float.ofInt (-761) / Float.ofNat 4)), ((Float.ofInt (-61289) / Float.ofNat 256), (Float.ofInt (-16067) / Float.ofNat 64)), ((Float.ofInt (2853) / Float.ofNat 64), (Float.ofInt (-15299) / Float.ofNat 256)), ((Float.ofInt (-15357) / Float.ofNat 256), (Float.ofInt (-13483) / Float.ofNat 64)), ((Float.ofInt (-15) / Float.ofNat 8), (Float.ofInt (-14949) / Float.ofNat 256)), ((Float.ofInt (-33975) / Float.ofNat 256), (Float.ofInt (-2443) / Float.ofNat 64)), ((Float.ofInt (-18815) / Float.ofNat 256), (Float.ofInt (-20459) / Float.ofNat 256)), ((Float.ofInt (-15373) / Float.ofNat 64), (Float.ofInt (29931) / Float.ofNat 256)), ((Float.ofInt (8755) / Float.ofNat 128), (Float.ofInt (669) / Float.ofNat 64)), ((Float.ofInt (14531) / Float.ofNat 256), (Float.ofInt (-14669) / Float.ofNat 128)), ((Float.ofInt (25723) / Float.ofNat 128), (Float.ofInt (-50659) / Float.ofNat 256)), ((Float.ofInt (-1547) / Float.ofNat 8), (Float.ofInt (-14777) / Float.ofNat 128)), ((Float.ofInt (23433) / Float.ofNat 256), (Float.ofInt (-6709) / Float.ofNat 256)), ((Float.ofInt (27977) / Float.ofNat 128), (Float.ofInt (-53819) / Float.ofNat 256)), ((Float.ofInt (-12639) / Float.ofNat 128), (Float.ofInt (11679) / Float.ofNat 256)), ((Float.ofInt (25937) / Float.ofNat 128), (Float.ofInt (747) / Float.ofNat 128)), ((Float.ofInt (279) / Float.ofNat 2), (Float.ofInt (-5487) / Float.ofNat 64)), ((Float.ofInt (-28463) / Float.ofNat 256), (Float.ofInt (25469) / Float.ofNat 128)), ((Float.ofInt (-21423) / Float.ofNat 128), (Float.ofInt (20951) / Float.ofNat 128)), ((Float.ofInt (58763) / Float.ofNat 256), (Float.ofInt (-19065) / Float.ofNat 256)), ((Float.ofInt (30895) / Float.ofNat 256), (Float.ofInt (-30353) / Float.ofNat 256)), ((Float.ofInt (30381) / Float.ofNat 128), (Float.ofInt (26177) / Float.ofNat 256)), ((Float.ofInt (-12863) / Float.ofNat 64), (Float.ofInt (-11245) / Float.ofNat 256)), ((Float.ofInt (21789) / Float.ofNat 128), (Float.ofInt (3255) / Float.ofNat 16)), ((Float.ofInt (14997) / Float.ofNat 128), (Float.ofInt (-26511) / Float.ofNat 256)), ((Float.ofInt (-17) / Float.ofNat 128), (Float.ofInt (9563) / Float.ofNat 64)), ((Float.ofInt (31929) / Float.ofNat 256), (Float.ofInt (-35603) / Float.ofNat 256)), ((Float.ofInt (-319) / Float.ofNat 16), (Float.ofInt (36697) / Float.ofNat 256)), ((Float.ofInt (-14297) / Float.ofNat 64), (Float.ofInt (18661) / Float.ofNat 128)), ((Float.ofInt (3049) / Float.ofNat 64), (Float.ofInt (11415) / Float.ofNat 128)), ((Float.ofInt (12999) / Float.ofNat 128), (Float.ofInt (13187) / Float.ofNat 256)), ((Float.ofInt (8199) / Float.ofNat 128), (Float.ofInt (24329) / Float.ofNat 128)), ((Float.ofInt (-41325) / Float.ofNat 256), (Float.ofInt (33323) / Float.ofNat 256)), ((Float.ofInt (-24639) / Float.ofNat 128), (Float.ofInt (2595) / Float.ofNat 32)), ((Float.ofInt (29837) / Float.ofNat 256), (Float.ofInt (-6791) / Float.ofNat 128)), ((Float.ofInt (6853) / Float.ofNat 128), (Float.ofInt (-3011) / Float.ofNat 128)), ((Float.ofInt (-18207) / Float.ofNat 128), (Float.ofInt (20089) / Float.ofNat 128)), ((Float.ofInt (-59853) / Float.ofNat 256), (Float.ofInt (29003) / Float.ofNat 128)), ((Float.ofInt (23595) / Float.ofNat 256), (Float.ofInt (-64787) / Float.ofNat 256)), ((Float.ofInt (20779) / Float.ofNat 256), (Float.ofInt (2505) / Float.ofNat 256)), ((Float.ofInt (31659) / Float.ofNat 128), (Float.ofInt (-14475) / Float.ofNat 128)), ((Float.ofInt (-4647) / Float.ofNat 32), (Float.ofInt (-12925) / Float.ofNat 128)), ((Float.ofInt (-30317) / Float.ofNat 256), (Float.ofInt (54459) / Float.ofNat 256)), ((Float.ofInt (-3065) / Float.ofNat 32), (Float.ofInt (5579) / Float.ofNat 128)), ((Float.ofInt (-19631) / Float.ofNat 256), (Float.ofInt (-31559) / Float.ofNat 128)), ((Float.ofInt (45253) / Float.ofNat 256), (Float.ofInt (-37183) / Float.ofNat 256)), ((Float.ofInt (-18973) / Float.ofNat 256), (Float.ofInt (7455) / Float.ofNat 32)), ((Float.ofInt (15075) / Float.ofNat 128), (Float.ofInt (-14009) / Float.ofNat 256)), ((Float.ofInt (28351) / Float.ofNat 128), (Float.ofInt (-665) / Float.ofNat 16)), ((Float.ofInt (-7751) / Float.ofNat 256), (Float.ofInt (-13063) / Float.ofNat 256)), ((Float.ofInt (-41193) / Float.ofNat 256), (Float.ofInt (-23945) / Float.ofNat 256)), ((Float.ofInt (-28155) / Float.ofNat 256), (Float.ofInt (-6279) / Float.ofNat 64)), ((Float.ofInt (-22785) / Float.ofNat 128), (Float.ofInt (-5755) / Float.ofNat 256)), ((Float.ofInt (24375) / Float.ofNat 128), (Float.ofInt (-4229) / Float.ofNat 256)), ((Float.ofInt (50807) / Float.ofNat 256), (Float.ofInt (21469) / Float.ofNat 128)), ((Float.ofInt (-51883) / Float.ofNat 256), (Float.ofInt (25633) / Float.ofNat 256)), ((Float.ofInt (-1157) / Float.ofNat 128), (Float.ofInt (31723) / Float.ofNat 256)), ((Float.ofInt (50613) / Float.ofNat 256), (Float.ofInt (28637) / Float.ofNat 128)), ((Float.ofInt (31135) / Float.ofNat 256), (Float.ofInt (867) / Float.ofNat 4)), ((Float.ofInt (-1939) / Float.ofNat 32), (Float.ofInt (-19697) / Float.ofNat 256)), ((Float.ofInt (-21709) / Float.ofNat 256), (Float.ofInt (-20839) / Float.ofNat 128)), ((Float.ofInt (-26989) / Float.ofNat 128), (Float.ofInt (23113) / Float.ofNat 128)), ((Float.ofInt (-8227) / Float.ofNat 128), (Float.ofInt (-49033) / Float.ofNat 256)), ((Float.ofInt (44249) / Float.ofNat 256), (Float.ofInt (5139) / Float.ofNat 256)), ((Float.ofInt (-63133) / Float.ofNat 256), (Float.ofInt (-55599) / Float.ofNat 256)), ((Float.ofInt (3563) / Float.ofNat 128), (Float.ofInt (-7077) / Float.ofNat 32)), ((Float.ofInt (16069) / Float.ofNat 128), (Float.ofInt (-4273) / Float.ofNat 256)), ((Float.ofInt (41599) / Float.ofNat 256), (Float.ofInt (28583) / Float.ofNat 256)), ((Float.ofInt (-30891) / Float.ofNat 256), (Float.ofInt (6171) / Float.ofNat 256)), ((Float.ofInt (10377) / Float.ofNat 64), (Float.ofInt (-1777) / Float.ofNat 128)), ((Float.ofInt (62191) / Float.ofNat 256), (Float.ofInt (-37969) / Float.ofNat 256)), ((Float.ofInt (8963) / Float.ofNat 256), (Float.ofInt (-6283) / Float.ofNat 256)), ((Float.ofInt (-2439) / Float.ofNat 256), (Float.ofInt (-4349) / Float.ofNat 128)), ((Float.ofInt (-18009) / Float.ofNat 128), (Float.ofInt (46379) / Float.ofNat 256)), ((Float.ofInt (15655) / Float.ofNat 64), (Float.ofInt (-28439) / Float.ofNat 256)), ((Float.ofInt (-16121) / Float.ofNat 256), (Float.ofInt (54173) / Float.ofNat 256)), ((Float.ofInt (12337) / Float.ofNat 128), (Float.ofInt (-31993) / Float.ofNat 256)), ((Float.ofInt (7669) / Float.ofNat 256), (Float.ofInt (16971) / Float.ofNat 256)), ((Float.ofInt (4871) / Float.ofNat 32), (Float.ofInt (1603) / Float.ofNat 8)), ((Float.ofInt (2007) / Float.ofNat 256), (Float.ofInt (995) / Float.ofNat 64)), ((Float.ofInt (1109) / Float.ofNat 32), (Float.ofInt (-21497) / Float.ofNat 256)), ((Float.ofInt (3473) / Float.ofNat 256), (Float.ofInt (27923) / Float.ofNat 256)), ((Float.ofInt (-20571) / Float.ofNat 256), (Float.ofInt (8185) / Float.ofNat 64)), ((Float.ofInt (15875) / Float.ofNat 64), (Float.ofInt (323) / Float.ofNat 64)), ((Float.ofInt (-23383) / Float.ofNat 128), (Float.ofInt (9647) / Float.ofNat 256)), ((Float.ofInt (29785) / Float.ofNat 128), (Float.ofInt (6593) / Float.ofNat 256)), ((Float.ofInt (-12721) / Float.ofNat 64), (Float.ofInt (1465) / Float.ofNat 8))]
#eval pairs.map (fun (a,b) => (applyBinary ops .add a b).toBits.toNat)
#eval pairs.map (fun (a,b) => (applyBinary ops .sub a b).toBits.toNat)
#eval pairs.map (fun (a,b) => (applyBinary ops .mul a b).toBits.toNat)
#eval pairs.map (fun (a,b) => (applyBinary ops .max a b).toBits.toNat)
end Calibration
