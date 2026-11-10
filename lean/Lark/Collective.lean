import Lark.Nonlinear

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
