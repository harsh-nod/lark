import Lark.Nonlinear

/-!
Opt-in full-wave64 MFMA f32_16x16x16f16 with modifiers (0,0,0).
Packed half operands occupy four scalar slots per lane; C/D use four float slots.
The exact-arithmetic operation is a left-fold dot product plus C. This is not
an IEEE model of the hardware's internal accumulation/rounding order.
All operands are read from the old register snapshot before any result is written.
No memory access, trace entry or memory-order epoch is added by the instruction.
-/
namespace LarkMFMA
open LarkNonlinear

inductive Instr where
  | scalar : LarkNonlinear.Instr → Instr
  | mfma : Nat → Nat → Nat → Nat → Instr
  deriving DecidableEq, Repr

inductive Cut where
  | warp | block | grid | halt | matrix
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
  | some (.mfma ..) => some .matrix
  | _ => none

def outputRow (lane element : Nat) : Nat := 4 * (lane / 16) + element

def outputCol (lane : Nat) : Nat := lane % 16

def aLane (row k : Nat) : Nat := row + 16 * (k / 4)
def bLane (k col : Nat) : Nat := col + 16 * (k / 4)

def dot (ops : Ops α) (left right : Nat → α) : α :=
  ((List.range 16).map fun k => ops.mul (ops.fromHalf (left k)) (ops.fromHalf (right k))).foldl
    ops.add (ops.literal 0 1)

def mfmaElement (ops : Ops α) (g : Geometry) (ts : List Nat)
    (dest a b c : Nat) (s : State α) (coordinate : Nat × Nat) :
    Option ((Nat × Nat) × α) := do
  let (t, e) := coordinate
  let lane := (t % g.block) % 64
  let owner := (t / g.block) * g.block + ((t % g.block) / 64) * 64
  let row := outputRow lane e
  let col := outputCol lane
  let terms ← (List.range 16).mapM fun k => do
    let al := owner + aLane row k
    let bl := owner + bLane k col
    if !(ts.contains al) ∨ !(ts.contains bl) then none else do
      let av ← s.regs al (a + k % 4)
      let bv ← s.regs bl (b + k % 4)
      pure (ops.mul (ops.fromHalf av) (ops.fromHalf bv))
  let cv ← s.regs t (c + e)
  pure ((t, dest + e), ops.add (terms.foldl ops.add (ops.literal 0 1)) cv)

def mfmaValues (ops : Ops α) (g : Geometry) (p : List Instr) (ts : List Nat)
    (s : State α) : Option (List ((Nat × Nat) × α)) := do
  if g.warp ≠ 64 ∨ g.block % 64 ≠ 0 ∨ ts.length ≠ 64 then none else do
    let first ← ts.head?
    match ← p[s.pc first]? with
    | .scalar _ => none
    | .mfma dest a b c =>
      let coordinates := ts.flatMap fun t => (List.range 4).map (fun e => (t, e))
      coordinates.mapM (mfmaElement ops g ts dest a b c s)

theorem mfmaValues_of (ops : Ops α) (g : Geometry) (p : List Instr) (ts : List Nat)
    (s : State α) (first dest a b c : Nat) (hw : g.warp = 64)
    (hb : g.block % 64 = 0) (hn : ts.length = 64)
    (hh : ts.head? = some first) (hf : p[s.pc first]? = some (.mfma dest a b c)) :
    mfmaValues ops g p ts s =
      (ts.flatMap fun t => (List.range 4).map (fun e => (t,e))).mapM
        (mfmaElement ops g ts dest a b c s) := by
  simp [mfmaValues, hw, hb, hn, hh, hf]

def mfmaUpdates (values : List ((Nat × Nat) × α)) (s : State α) : State α :=
  { s with
    pc := fun t => if values.any (fun pair => pair.1.1 == t) then s.pc t + 1 else s.pc t
    regs := fun t r => match List.lookup (t, r) values with
      | some value => some value
      | none => s.regs t r }

def runMFMA (ops : Ops α) (g : Geometry) (p : List Instr) (ts : List Nat)
    (s : State α) : Option (State α) := do
  let values ← mfmaValues ops g p ts s
  pure (mfmaUpdates values s)

theorem runMFMA_of (ops : Ops α) (g : Geometry) (p : List Instr) (ts : List Nat)
    (s : State α) (values : List ((Nat × Nat) × α))
    (h : mfmaValues ops g p ts s = some values) :
    runMFMA ops g p ts s = some (mfmaUpdates values s) := by
  simp [runMFMA, h]

theorem mfmaUpdates_preserves (values : List ((Nat × Nat) × α)) (s : State α) :
    (mfmaUpdates values s).memory = s.memory ∧
    (mfmaUpdates values s).trace = s.trace ∧
    (mfmaUpdates values s).epochs = s.epochs := by
  exact ⟨rfl, rfl, rfl⟩

theorem runMFMA_preserves (ops : Ops α) (g : Geometry) (p : List Instr) (ts : List Nat)
    (s next : State α) (h : runMFMA ops g p ts s = some next) :
    next.memory = s.memory ∧ next.trace = s.trace ∧ next.epochs = s.epochs := by
  cases hv : mfmaValues ops g p ts s with
  | none => simp [runMFMA, hv] at h
  | some values =>
      simp [runMFMA, hv] at h
      subst next
      exact mfmaUpdates_preserves values s

def runLane (ops : Ops α) (layout : Layout) (g : Geometry) (p : List Instr)
    (t : Nat) : Nat → State α → Option (State α)
  | 0, _ => none
  | n + 1, s =>
      match parked p s t with
      | some _ => some s
      | none => do
          match ← p[s.pc t]? with
          | .mfma .. => none
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
      if c = .matrix then
        let next ← runMFMA ops g p ts s
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

theorem runWarp_matrix_step (ops : Ops α) (layout : Layout) (g : Geometry) (f : Fuel)
    (p : List Instr) (ts : List Nat) (n : Nat) (s loaded matrix : State α)
    (hl : ts.foldlM (fun s t => runLane ops layout g p t f.lane s) s = some loaded)
    (hc : converged p ts loaded = some .matrix)
    (hm : runMFMA ops g p ts loaded = some matrix) :
    runWarp ops layout g f p ts (n+1) s = runWarp ops layout g f p ts n matrix := by
  simp [runWarp, hl, hc, hm]

theorem runWarp_halt (ops : Ops α) (layout : Layout) (g : Geometry) (f : Fuel)
    (p : List Instr) (ts : List Nat) (n : Nat) (s final : State α)
    (hl : ts.foldlM (fun s t => runLane ops layout g p t f.lane s) s = some final)
    (hc : converged p ts final = some .halt) :
    runWarp ops layout g f p ts (n+1) s = some final := by
  simp [runWarp, hl, hc]

theorem runBlock_halt (ops : Ops α) (layout : Layout) (g : Geometry) (f : Fuel)
    (p : List Instr) (b n : Nat) (s final : State α)
    (hl : (List.range ((g.block+g.warp-1)/g.warp)).foldlM
      (fun s w => runWarp ops layout g f p (warpThreads g b w) f.warp s) s = some final)
    (hc : converged p (blockThreads g b) final = some .halt) :
    runBlock ops layout g f p b (n+1) s = some final := by
  simp [runBlock, hl, hc]

theorem runGrid_halt (ops : Ops α) (layout : Layout) (g : Geometry) (f : Fuel)
    (p : List Instr) (n : Nat) (s final : State α)
    (hl : (List.range g.grid).foldlM
      (fun s b => runBlock ops layout g f p b f.block s) s = some final)
    (hc : converged p (List.range (g.grid*g.block)) final = some .halt) :
    runGrid ops layout g f p (n+1) s = some final := by
  simp [runGrid, hl, hc]

theorem runLaunch_of (ops : Ops α) (layout : Layout) (g : Geometry) (f : Fuel)
    (p : List Instr) (s : State α) (hg : g.grid ≠ 0) (hb : g.block ≠ 0)
    (hw : g.warp = 64) (hm : g.block % 64 = 0) :
    runLaunch ops layout g f p s = runGrid ops layout g f p f.grid s := by
  simp [runLaunch, hg, hb, hw, hm]

theorem foldlM_singleton (f : State α → Nat → Option (State α)) (s : State α) (t : Nat) :
    [t].foldlM f s = f s t := by
  cases hf : f s t <;> simp [List.foldlM_cons, List.foldlM_nil, hf]

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

#print axioms mfmaUpdates_preserves
#print axioms runMFMA_preserves
end LarkMFMA
