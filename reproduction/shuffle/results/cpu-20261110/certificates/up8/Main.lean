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
Opt-in full-wave64 register shuffles. Scalar execution, memory, layout and
race freedom reuse the pinned nonlinear machine. A shuffle reads one snapshot
of every participating lane's registers and advances all PCs simultaneously.
It DOES NOT advance memory-ordering epochs or modify memory/access traces.
Only full waves and widths 1,2,4,8,16,32,64 are admitted.
-/
namespace LarkCollective
open LarkNonlinear

inductive ShuffleKind where
  | index | xor | up | down
  deriving DecidableEq, Repr, BEq

inductive Instr where
  | scalar : LarkNonlinear.Instr → Instr
  | shuffle : ShuffleKind → Nat → Nat → Index → Nat → Instr
  deriving DecidableEq, Repr

inductive Cut where
  | warp | block | grid | halt | shuffle
  deriving DecidableEq, Repr, BEq

def scalarCut : LarkNonlinear.Cut → Cut
  | .warp => .warp
  | .block => .block
  | .grid => .grid
  | .halt => .halt

def parked (p : List Instr) (s : State α) (t : Nat) : Option Cut :=
  match p[s.pc t]? with
  | some (.scalar (.barrier c)) => some (scalarCut c)
  | some (.scalar .halt) => some .halt
  | some (.shuffle ..) => some .shuffle
  | _ => none

def sourceLane (kind : ShuffleKind) (width lane argument : Nat) : Option Nat := do
  if !([1, 2, 4, 8, 16, 32, 64].contains width) ∨ 64 ≤ lane then none else do
    let position := lane % width
    let base := (lane / width) * width
    let selected ← match kind with
      | .index => if argument < width then some (base + argument) else none
      | .xor => if argument < width then some (base + Nat.xor position argument) else none
      | .up => if argument ≤ width then
          some (if argument ≤ position then lane - argument else lane) else none
      | .down => if argument ≤ width then
          some (if position + argument < width then lane + argument else lane) else none
    if selected < 64 ∧ selected / width = lane / width then some selected else none

def shuffleValues (g : Geometry) (p : List Instr) (ts : List Nat)
    (s : State α) : Option (Nat × List (Nat × α)) := do
  if g.warp ≠ 64 ∨ g.block % 64 ≠ 0 ∨ ts.length ≠ 64 then none else do
    let first ← ts.head?
    match ← p[s.pc first]? with
    | .scalar _ => none
    | .shuffle kind dest src selector width =>
      let values ← ts.mapM fun t => do
        let arg ← evalIndex g t s selector
        if arg < 0 then none else do
          let lane := (t % g.block) % 64
          let selected ← sourceLane kind width lane arg.toNat
          let owner := (t / g.block) * g.block + ((t % g.block) / 64) * 64
          let source := owner + selected
          if !(ts.contains source) then none else do
            let value ← s.regs source src
            pure (t, value)
      pure (dest, values)

def shuffleUpdates (dest : Nat) (values : List (Nat × α)) (s : State α) : State α :=
  { s with
    pc := fun t => if values.any (fun pair => pair.1 == t) then s.pc t + 1 else s.pc t
    regs := fun t r => if r = dest then
      match List.lookup t values with
      | some value => some value
      | none => s.regs t r
      else s.regs t r }

def runShuffle (g : Geometry) (p : List Instr) (ts : List Nat)
    (s : State α) : Option (State α) := do
  let (dest, values) ← shuffleValues g p ts s
  pure (shuffleUpdates dest values s)

/-- Register transport grants no memory ordering and has no memory footprint. -/
theorem shuffleUpdates_preserves (dest : Nat) (values : List (Nat × α)) (s : State α) :
    (shuffleUpdates dest values s).memory = s.memory ∧
    (shuffleUpdates dest values s).trace = s.trace ∧
    (shuffleUpdates dest values s).epochs = s.epochs := by
  exact ⟨rfl, rfl, rfl⟩

theorem runShuffle_preserves (g : Geometry) (p : List Instr) (ts : List Nat)
    (s next : State α) (h : runShuffle g p ts s = some next) :
    next.memory = s.memory ∧ next.trace = s.trace ∧ next.epochs = s.epochs := by
  cases hv : shuffleValues g p ts s with
  | none => simp [runShuffle, hv] at h
  | some pair =>
      simp [runShuffle, hv] at h
      subst next
      exact shuffleUpdates_preserves pair.1 pair.2 s

/-- A cheap sufficient condition for these lane-indexed input/output fixtures. -/
def Owned (trace : List Access) : Prop :=
  ∀ a ∈ trace, a.location.offset = a.thread

theorem owned_raceFree (g : Geometry) (trace : List Access) (h : Owned trace) :
    raceFree g trace = true := by
  apply List.all_eq_true.mpr
  intro a ha
  apply List.all_eq_true.mpr
  intro b hb
  by_cases he : a.thread = b.thread
  · simp [conflict, he]
  · have hn : a.location.offset ≠ b.location.offset := by
      simpa only [h a ha, h b hb] using he
    have hbeq : (a.location.offset == b.location.offset) = false := by simp [hn]
    simp [conflict, sameLocation, hbeq]

def runLane (ops : Ops α) (layout : Layout) (g : Geometry) (p : List Instr)
    (t : Nat) : Nat → State α → Option (State α)
  | 0, _ => none
  | n + 1, s =>
      match parked p s t with
      | some _ => some s
      | none => do
          match ← p[s.pc t]? with
          | .shuffle .. => none
          | .scalar instruction =>
            let next ← execute ops layout g t instruction s
            runLane ops layout g p t n next

def converged (p : List Instr) (ts : List Nat) (s : State α) : Option Cut := do
  let t ← ts.head?
  if ts.all (fun u => s.pc u == s.pc t) then parked p s t else none

def runWarp (ops : Ops α) (layout : Layout) (g : Geometry) (f : Fuel)
    (p : List Instr) (ts : List Nat) : Nat → State α → Option (State α)
  | 0, _ => none
  | n + 1, s => do
      let s ← ts.foldlM (fun s t => runLane ops layout g p t f.lane s) s
      let c ← converged p ts s
      if c = .shuffle then
        let next ← runShuffle g p ts s
        runWarp ops layout g f p ts n next
      else if c = .warp then
        runWarp ops layout g f p ts n (resume ts .warp s)
      else some s

def runBlock (ops : Ops α) (layout : Layout) (g : Geometry) (f : Fuel)
    (p : List Instr) (b : Nat) : Nat → State α → Option (State α)
  | 0, _ => none
  | n + 1, s => do
      let ws := List.range ((g.block + g.warp - 1) / g.warp)
      let s ← ws.foldlM (fun s w =>
        runWarp ops layout g f p (warpThreads g b w) f.warp s) s
      let ts := blockThreads g b
      let c ← converged p ts s
      if c = .block then runBlock ops layout g f p b n (resume ts .block s) else
        if c = .grid ∨ c = .halt then some s else none

def runGrid (ops : Ops α) (layout : Layout) (g : Geometry) (f : Fuel)
    (p : List Instr) : Nat → State α → Option (State α)
  | 0, _ => none
  | n + 1, s => do
      let s ← (List.range g.grid).foldlM (fun s b =>
        runBlock ops layout g f p b f.block s) s
      let ts := List.range (g.grid * g.block)
      let c ← converged p ts s
      if c = .grid then runGrid ops layout g f p n (resume ts .grid s) else
        if c = .halt then some s else none

def runLaunch (ops : Ops α) (layout : Layout) (g : Geometry) (f : Fuel)
    (p : List Instr) (s : State α) : Option (State α) :=
  if g.grid = 0 ∨ g.block = 0 ∨ g.warp ≠ 64 ∨ g.block % 64 ≠ 0 then none
  else runGrid ops layout g f p f.grid s

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

#print axioms shuffleUpdates_preserves
#print axioms runShuffle_preserves
#print axioms owned_raceFree
end LarkCollective


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


namespace LarkCertificate
open LarkNonlinear
abbrev Instr := LarkCollective.Instr
abbrev Segment := LarkCollective.Segment
abbrev flatten := LarkCollective.flatten
abbrev flattenSegment := LarkCollective.flattenSegment
abbrev runLaunch (ops : Ops α) := LarkCollective.runLaunch ops
abbrev Correct (ops : Ops α) := LarkCollective.Correct ops
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000

def layout : Layout := ⟨[⟨.input, 64⟩, ⟨.output, 64⟩], [], []⟩
def geometry : Geometry := ⟨1, 64, 64⟩
def fuel : Fuel := ⟨32, 8, 8, 8⟩
def program : List Instr := [(.scalar (.index 0 .tid)), (.scalar (.assign 0 (.load .global 0 (.ivar (0))))), (.shuffle .up 0 0 (.const (1)) 8), (.scalar (.store .global 1 (.ivar (0)) (.reg (0)))), (.scalar .halt)]
def traceData : List Access := [⟨63, ⟨.global, 0, 1, 63⟩, true, ⟨0, 0, 0⟩⟩, ⟨62, ⟨.global, 0, 1, 62⟩, true, ⟨0, 0, 0⟩⟩, ⟨61, ⟨.global, 0, 1, 61⟩, true, ⟨0, 0, 0⟩⟩, ⟨60, ⟨.global, 0, 1, 60⟩, true, ⟨0, 0, 0⟩⟩, ⟨59, ⟨.global, 0, 1, 59⟩, true, ⟨0, 0, 0⟩⟩, ⟨58, ⟨.global, 0, 1, 58⟩, true, ⟨0, 0, 0⟩⟩, ⟨57, ⟨.global, 0, 1, 57⟩, true, ⟨0, 0, 0⟩⟩, ⟨56, ⟨.global, 0, 1, 56⟩, true, ⟨0, 0, 0⟩⟩, ⟨55, ⟨.global, 0, 1, 55⟩, true, ⟨0, 0, 0⟩⟩, ⟨54, ⟨.global, 0, 1, 54⟩, true, ⟨0, 0, 0⟩⟩, ⟨53, ⟨.global, 0, 1, 53⟩, true, ⟨0, 0, 0⟩⟩, ⟨52, ⟨.global, 0, 1, 52⟩, true, ⟨0, 0, 0⟩⟩, ⟨51, ⟨.global, 0, 1, 51⟩, true, ⟨0, 0, 0⟩⟩, ⟨50, ⟨.global, 0, 1, 50⟩, true, ⟨0, 0, 0⟩⟩, ⟨49, ⟨.global, 0, 1, 49⟩, true, ⟨0, 0, 0⟩⟩, ⟨48, ⟨.global, 0, 1, 48⟩, true, ⟨0, 0, 0⟩⟩, ⟨47, ⟨.global, 0, 1, 47⟩, true, ⟨0, 0, 0⟩⟩, ⟨46, ⟨.global, 0, 1, 46⟩, true, ⟨0, 0, 0⟩⟩, ⟨45, ⟨.global, 0, 1, 45⟩, true, ⟨0, 0, 0⟩⟩, ⟨44, ⟨.global, 0, 1, 44⟩, true, ⟨0, 0, 0⟩⟩, ⟨43, ⟨.global, 0, 1, 43⟩, true, ⟨0, 0, 0⟩⟩, ⟨42, ⟨.global, 0, 1, 42⟩, true, ⟨0, 0, 0⟩⟩, ⟨41, ⟨.global, 0, 1, 41⟩, true, ⟨0, 0, 0⟩⟩, ⟨40, ⟨.global, 0, 1, 40⟩, true, ⟨0, 0, 0⟩⟩, ⟨39, ⟨.global, 0, 1, 39⟩, true, ⟨0, 0, 0⟩⟩, ⟨38, ⟨.global, 0, 1, 38⟩, true, ⟨0, 0, 0⟩⟩, ⟨37, ⟨.global, 0, 1, 37⟩, true, ⟨0, 0, 0⟩⟩, ⟨36, ⟨.global, 0, 1, 36⟩, true, ⟨0, 0, 0⟩⟩, ⟨35, ⟨.global, 0, 1, 35⟩, true, ⟨0, 0, 0⟩⟩, ⟨34, ⟨.global, 0, 1, 34⟩, true, ⟨0, 0, 0⟩⟩, ⟨33, ⟨.global, 0, 1, 33⟩, true, ⟨0, 0, 0⟩⟩, ⟨32, ⟨.global, 0, 1, 32⟩, true, ⟨0, 0, 0⟩⟩, ⟨31, ⟨.global, 0, 1, 31⟩, true, ⟨0, 0, 0⟩⟩, ⟨30, ⟨.global, 0, 1, 30⟩, true, ⟨0, 0, 0⟩⟩, ⟨29, ⟨.global, 0, 1, 29⟩, true, ⟨0, 0, 0⟩⟩, ⟨28, ⟨.global, 0, 1, 28⟩, true, ⟨0, 0, 0⟩⟩, ⟨27, ⟨.global, 0, 1, 27⟩, true, ⟨0, 0, 0⟩⟩, ⟨26, ⟨.global, 0, 1, 26⟩, true, ⟨0, 0, 0⟩⟩, ⟨25, ⟨.global, 0, 1, 25⟩, true, ⟨0, 0, 0⟩⟩, ⟨24, ⟨.global, 0, 1, 24⟩, true, ⟨0, 0, 0⟩⟩, ⟨23, ⟨.global, 0, 1, 23⟩, true, ⟨0, 0, 0⟩⟩, ⟨22, ⟨.global, 0, 1, 22⟩, true, ⟨0, 0, 0⟩⟩, ⟨21, ⟨.global, 0, 1, 21⟩, true, ⟨0, 0, 0⟩⟩, ⟨20, ⟨.global, 0, 1, 20⟩, true, ⟨0, 0, 0⟩⟩, ⟨19, ⟨.global, 0, 1, 19⟩, true, ⟨0, 0, 0⟩⟩, ⟨18, ⟨.global, 0, 1, 18⟩, true, ⟨0, 0, 0⟩⟩, ⟨17, ⟨.global, 0, 1, 17⟩, true, ⟨0, 0, 0⟩⟩, ⟨16, ⟨.global, 0, 1, 16⟩, true, ⟨0, 0, 0⟩⟩, ⟨15, ⟨.global, 0, 1, 15⟩, true, ⟨0, 0, 0⟩⟩, ⟨14, ⟨.global, 0, 1, 14⟩, true, ⟨0, 0, 0⟩⟩, ⟨13, ⟨.global, 0, 1, 13⟩, true, ⟨0, 0, 0⟩⟩, ⟨12, ⟨.global, 0, 1, 12⟩, true, ⟨0, 0, 0⟩⟩, ⟨11, ⟨.global, 0, 1, 11⟩, true, ⟨0, 0, 0⟩⟩, ⟨10, ⟨.global, 0, 1, 10⟩, true, ⟨0, 0, 0⟩⟩, ⟨9, ⟨.global, 0, 1, 9⟩, true, ⟨0, 0, 0⟩⟩, ⟨8, ⟨.global, 0, 1, 8⟩, true, ⟨0, 0, 0⟩⟩, ⟨7, ⟨.global, 0, 1, 7⟩, true, ⟨0, 0, 0⟩⟩, ⟨6, ⟨.global, 0, 1, 6⟩, true, ⟨0, 0, 0⟩⟩, ⟨5, ⟨.global, 0, 1, 5⟩, true, ⟨0, 0, 0⟩⟩, ⟨4, ⟨.global, 0, 1, 4⟩, true, ⟨0, 0, 0⟩⟩, ⟨3, ⟨.global, 0, 1, 3⟩, true, ⟨0, 0, 0⟩⟩, ⟨2, ⟨.global, 0, 1, 2⟩, true, ⟨0, 0, 0⟩⟩, ⟨1, ⟨.global, 0, 1, 1⟩, true, ⟨0, 0, 0⟩⟩, ⟨0, ⟨.global, 0, 1, 0⟩, true, ⟨0, 0, 0⟩⟩, ⟨63, ⟨.global, 0, 0, 63⟩, false, ⟨0, 0, 0⟩⟩, ⟨62, ⟨.global, 0, 0, 62⟩, false, ⟨0, 0, 0⟩⟩, ⟨61, ⟨.global, 0, 0, 61⟩, false, ⟨0, 0, 0⟩⟩, ⟨60, ⟨.global, 0, 0, 60⟩, false, ⟨0, 0, 0⟩⟩, ⟨59, ⟨.global, 0, 0, 59⟩, false, ⟨0, 0, 0⟩⟩, ⟨58, ⟨.global, 0, 0, 58⟩, false, ⟨0, 0, 0⟩⟩, ⟨57, ⟨.global, 0, 0, 57⟩, false, ⟨0, 0, 0⟩⟩, ⟨56, ⟨.global, 0, 0, 56⟩, false, ⟨0, 0, 0⟩⟩, ⟨55, ⟨.global, 0, 0, 55⟩, false, ⟨0, 0, 0⟩⟩, ⟨54, ⟨.global, 0, 0, 54⟩, false, ⟨0, 0, 0⟩⟩, ⟨53, ⟨.global, 0, 0, 53⟩, false, ⟨0, 0, 0⟩⟩, ⟨52, ⟨.global, 0, 0, 52⟩, false, ⟨0, 0, 0⟩⟩, ⟨51, ⟨.global, 0, 0, 51⟩, false, ⟨0, 0, 0⟩⟩, ⟨50, ⟨.global, 0, 0, 50⟩, false, ⟨0, 0, 0⟩⟩, ⟨49, ⟨.global, 0, 0, 49⟩, false, ⟨0, 0, 0⟩⟩, ⟨48, ⟨.global, 0, 0, 48⟩, false, ⟨0, 0, 0⟩⟩, ⟨47, ⟨.global, 0, 0, 47⟩, false, ⟨0, 0, 0⟩⟩, ⟨46, ⟨.global, 0, 0, 46⟩, false, ⟨0, 0, 0⟩⟩, ⟨45, ⟨.global, 0, 0, 45⟩, false, ⟨0, 0, 0⟩⟩, ⟨44, ⟨.global, 0, 0, 44⟩, false, ⟨0, 0, 0⟩⟩, ⟨43, ⟨.global, 0, 0, 43⟩, false, ⟨0, 0, 0⟩⟩, ⟨42, ⟨.global, 0, 0, 42⟩, false, ⟨0, 0, 0⟩⟩, ⟨41, ⟨.global, 0, 0, 41⟩, false, ⟨0, 0, 0⟩⟩, ⟨40, ⟨.global, 0, 0, 40⟩, false, ⟨0, 0, 0⟩⟩, ⟨39, ⟨.global, 0, 0, 39⟩, false, ⟨0, 0, 0⟩⟩, ⟨38, ⟨.global, 0, 0, 38⟩, false, ⟨0, 0, 0⟩⟩, ⟨37, ⟨.global, 0, 0, 37⟩, false, ⟨0, 0, 0⟩⟩, ⟨36, ⟨.global, 0, 0, 36⟩, false, ⟨0, 0, 0⟩⟩, ⟨35, ⟨.global, 0, 0, 35⟩, false, ⟨0, 0, 0⟩⟩, ⟨34, ⟨.global, 0, 0, 34⟩, false, ⟨0, 0, 0⟩⟩, ⟨33, ⟨.global, 0, 0, 33⟩, false, ⟨0, 0, 0⟩⟩, ⟨32, ⟨.global, 0, 0, 32⟩, false, ⟨0, 0, 0⟩⟩, ⟨31, ⟨.global, 0, 0, 31⟩, false, ⟨0, 0, 0⟩⟩, ⟨30, ⟨.global, 0, 0, 30⟩, false, ⟨0, 0, 0⟩⟩, ⟨29, ⟨.global, 0, 0, 29⟩, false, ⟨0, 0, 0⟩⟩, ⟨28, ⟨.global, 0, 0, 28⟩, false, ⟨0, 0, 0⟩⟩, ⟨27, ⟨.global, 0, 0, 27⟩, false, ⟨0, 0, 0⟩⟩, ⟨26, ⟨.global, 0, 0, 26⟩, false, ⟨0, 0, 0⟩⟩, ⟨25, ⟨.global, 0, 0, 25⟩, false, ⟨0, 0, 0⟩⟩, ⟨24, ⟨.global, 0, 0, 24⟩, false, ⟨0, 0, 0⟩⟩, ⟨23, ⟨.global, 0, 0, 23⟩, false, ⟨0, 0, 0⟩⟩, ⟨22, ⟨.global, 0, 0, 22⟩, false, ⟨0, 0, 0⟩⟩, ⟨21, ⟨.global, 0, 0, 21⟩, false, ⟨0, 0, 0⟩⟩, ⟨20, ⟨.global, 0, 0, 20⟩, false, ⟨0, 0, 0⟩⟩, ⟨19, ⟨.global, 0, 0, 19⟩, false, ⟨0, 0, 0⟩⟩, ⟨18, ⟨.global, 0, 0, 18⟩, false, ⟨0, 0, 0⟩⟩, ⟨17, ⟨.global, 0, 0, 17⟩, false, ⟨0, 0, 0⟩⟩, ⟨16, ⟨.global, 0, 0, 16⟩, false, ⟨0, 0, 0⟩⟩, ⟨15, ⟨.global, 0, 0, 15⟩, false, ⟨0, 0, 0⟩⟩, ⟨14, ⟨.global, 0, 0, 14⟩, false, ⟨0, 0, 0⟩⟩, ⟨13, ⟨.global, 0, 0, 13⟩, false, ⟨0, 0, 0⟩⟩, ⟨12, ⟨.global, 0, 0, 12⟩, false, ⟨0, 0, 0⟩⟩, ⟨11, ⟨.global, 0, 0, 11⟩, false, ⟨0, 0, 0⟩⟩, ⟨10, ⟨.global, 0, 0, 10⟩, false, ⟨0, 0, 0⟩⟩, ⟨9, ⟨.global, 0, 0, 9⟩, false, ⟨0, 0, 0⟩⟩, ⟨8, ⟨.global, 0, 0, 8⟩, false, ⟨0, 0, 0⟩⟩, ⟨7, ⟨.global, 0, 0, 7⟩, false, ⟨0, 0, 0⟩⟩, ⟨6, ⟨.global, 0, 0, 6⟩, false, ⟨0, 0, 0⟩⟩, ⟨5, ⟨.global, 0, 0, 5⟩, false, ⟨0, 0, 0⟩⟩, ⟨4, ⟨.global, 0, 0, 4⟩, false, ⟨0, 0, 0⟩⟩, ⟨3, ⟨.global, 0, 0, 3⟩, false, ⟨0, 0, 0⟩⟩, ⟨2, ⟨.global, 0, 0, 2⟩, false, ⟨0, 0, 0⟩⟩, ⟨1, ⟨.global, 0, 0, 1⟩, false, ⟨0, 0, 0⟩⟩, ⟨0, ⟨.global, 0, 0, 0⟩, false, ⟨0, 0, 0⟩⟩]
def segments : List Segment := [(.seq [(.op (.scalar (.index 0 .tid))), (.op (.scalar (.assign 0 (.load .global 0 (.ivar (0)))))), (.op (.shuffle .up 0 0 (.const (1)) 8)), (.op (.scalar (.store .global 1 (.ivar (0)) (.reg (0))))), (.op (.scalar .halt))])]
def spec (ops : Ops α) (input : Nat → Nat → α) : List α :=
  [(input 0 0), (input 0 0), (input 0 1), (input 0 2), (input 0 3), (input 0 4), (input 0 5), (input 0 6), (input 0 8), (input 0 8), (input 0 9), (input 0 10), (input 0 11), (input 0 12), (input 0 13), (input 0 14), (input 0 16), (input 0 16), (input 0 17), (input 0 18), (input 0 19), (input 0 20), (input 0 21), (input 0 22), (input 0 24), (input 0 24), (input 0 25), (input 0 26), (input 0 27), (input 0 28), (input 0 29), (input 0 30), (input 0 32), (input 0 32), (input 0 33), (input 0 34), (input 0 35), (input 0 36), (input 0 37), (input 0 38), (input 0 40), (input 0 40), (input 0 41), (input 0 42), (input 0 43), (input 0 44), (input 0 45), (input 0 46), (input 0 48), (input 0 48), (input 0 49), (input 0 50), (input 0 51), (input 0 52), (input 0 53), (input 0 54), (input 0 56), (input 0 56), (input 0 57), (input 0 58), (input 0 59), (input 0 60), (input 0 61), (input 0 62)]
def finalState (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) : State α :=
  (runLaunch ops layout geometry fuel program (initial layout input outside)).getD
    (initial layout input outside)
theorem segmentation_data : flatten segments = program :=
  by simp [LarkCollective.flatten, LarkCollective.flattenSegment, segments, program]
theorem segmentation (ops : Ops α) (s : State α) :
    runLaunch ops layout geometry fuel program s =
    runLaunch ops layout geometry fuel (flatten segments) s := by
  rw [segmentation_data]
def unitOps : Ops Unit := ⟨fun _ _ => (), fun _ _ => (), fun _ _ => (), fun _ _ => (), fun _ _ => (), fun _ _ => (), fun _ => (), fun _ => (), fun _ => (), fun _ => (), fun _ => ()⟩
theorem race_free : ∃ final,
    runLaunch unitOps layout geometry fuel program
      (initial layout (fun _ _ => ()) (fun _ => some ())) = some final ∧
    raceFree geometry final.trace = true :=
  by
  obtain ⟨final, hr, hrf, hout⟩ :=
    (LarkCollective.Transfer.correct unitOps .up 0 (.const (1)) 8 (fun t => (([0, 0, 1, 2, 3, 4, 5, 6, 8, 8, 9, 10, 11, 12, 13, 14, 16, 16, 17, 18, 19, 20, 21, 22, 24, 24, 25, 26, 27, 28, 29, 30, 32, 32, 33, 34, 35, 36, 37, 38, 40, 40, 41, 42, 43, 44, 45, 46, 48, 48, 49, 50, 51, 52, 53, 54, 56, 56, 57, 58, 59, 60, 61, 62] : List Nat)[t]?).getD 0) (by unfold LarkCollective.Transfer.Valid; decide)) (fun _ _ => ()) (fun _ => some ())
  exact ⟨final, hr, hrf⟩
theorem segment_equivalence (ops : Ops α) :
    Correct ops layout geometry fuel (flatten segments) (spec ops) :=
  by
  rw [segmentation_data]
  exact LarkCollective.Transfer.correct ops .up 0 (.const (1)) 8 (fun t => (([0, 0, 1, 2, 3, 4, 5, 6, 8, 8, 9, 10, 11, 12, 13, 14, 16, 16, 17, 18, 19, 20, 21, 22, 24, 24, 25, 26, 27, 28, 29, 30, 32, 32, 33, 34, 35, 36, 37, 38, 40, 40, 41, 42, 43, 44, 45, 46, 48, 48, 49, 50, 51, 52, 53, 54, 56, 56, 57, 58, 59, 60, 61, 62] : List Nat)[t]?).getD 0) (by unfold LarkCollective.Transfer.Valid; decide)
theorem kernel_eq_spec (ops : Ops α) :
    Correct ops layout geometry fuel program (spec ops) := by
  exact LarkCollective.assemble ops layout geometry fuel program segments (spec ops)
    segmentation_data (segment_equivalence ops)
theorem kernel_eq_spec_pre (ops : Ops α) (input : Nat → Nat → α) (s : State α)
    (pre : StdPre layout input s) :
    ∃ final, runLaunch ops layout geometry fuel program s = some final ∧
      raceFree geometry final.trace = true ∧ extract layout final = some (spec ops input) := by
  exact LarkCollective.correct_from_pre ops layout geometry fuel program (spec ops)
    (kernel_eq_spec ops) input s pre
#print axioms segmentation_data
#print axioms segmentation
#print axioms race_free
#print axioms segment_equivalence
#print axioms kernel_eq_spec
#print axioms kernel_eq_spec_pre
end LarkCertificate
