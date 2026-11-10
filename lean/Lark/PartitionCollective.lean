import Lark.CollectiveGather

/-!
Opt-in scheduler for complete logical shuffle partitions inside a physical
wave64. Scalar semantics, native synchronization epochs and race freedom are
unchanged. The earlier full-wave machine remains pinned and unchanged.

The scheduler admits a parked shuffle cohort only when it is a union of whole
aligned logical partitions, all in one native wave and at one instruction.
This covers the final logical-16 reduction of a 1,024-thread HIP block without
padding extra lanes or granting a memory fence to a shuffle.
-/
namespace LarkPartitionCollective
open LarkNonlinear LarkCollective
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def nativeBase (g : Geometry) (t : Nat) : Nat :=
  (t / g.block) * g.block + ((t % g.block) / 64) * 64

def nativeLane (g : Geometry) (t : Nat) : Nat := (t % g.block) % 64

def completePartitions (g : Geometry) (ts : List Nat) (width : Nat) : Bool :=
  ts.all fun t => (List.range width).all fun lane =>
    ts.contains (nativeBase g t + (nativeLane g t / width) * width + lane)

def shuffleValues (g : Geometry) (p : List LarkCollective.Instr) (ts : List Nat)
    (s : State α) : Option (Nat × List (Nat × α)) := do
  if g.warp ≠ 64 ∨ g.block % 64 ≠ 0 ∨ ts = [] ∨ ¬ ts.Nodup ∨ 64 < ts.length then
    none
  else do
    let first ← ts.head?
    if !(ts.all fun t => s.pc t == s.pc first && nativeBase g t == nativeBase g first) then
      none
    else do
      match ← p[s.pc first]? with
      | .scalar _ => none
      | .shuffle kind dest src selector width =>
        if !([1, 2, 4, 8, 16, 32, 64].contains width) ∨ !completePartitions g ts width then
          none
        else do
          let values ← ts.mapM (Gather.readValue g ts s kind src selector width)
          pure (dest, values)

def runShuffle (g : Geometry) (p : List LarkCollective.Instr) (ts : List Nat)
    (s : State α) : Option (State α) := do
  let (dest, values) ← shuffleValues g p ts s
  pure (shuffleUpdates dest values s)

theorem runShuffle_preserves (g : Geometry) (p : List LarkCollective.Instr) (ts : List Nat)
    (s next : State α) (h : runShuffle g p ts s = some next) :
    next.memory = s.memory ∧ next.indices = s.indices ∧
      next.epochs = s.epochs ∧ next.trace = s.trace := by
  cases hv : shuffleValues g p ts s with
  | none => simp [runShuffle, hv] at h
  | some pair =>
      simp [runShuffle, hv] at h
      subst next
      exact ⟨rfl, rfl, rfl, rfl⟩

def isShuffle (p : List LarkCollective.Instr) (s : State α) (t : Nat) : Bool :=
  match p[s.pc t]? with
  | some (.shuffle ..) => true
  | _ => false

def nextCohort (p : List LarkCollective.Instr) (ts : List Nat) (s : State α) : Option (List Nat) := do
  let first ← (ts.filter (isShuffle p s)).head?
  pure (ts.filter fun t => s.pc t == s.pc first)

theorem nextCohort_subset (p : List LarkCollective.Instr) (ts cohort : List Nat) (s : State α)
    (h : nextCohort p ts s = some cohort) : ∀ t ∈ cohort, t ∈ ts := by
  unfold nextCohort at h
  cases hh : (ts.filter (isShuffle p s)).head? with
  | none => simp [hh] at h
  | some first =>
      simp only [hh, bind, pure, Option.some_bind, Option.some.injEq] at h
      subst cohort
      intro t ht
      exact (List.mem_filter.mp ht).1

theorem nextCohort_nonempty (p : List LarkCollective.Instr) (ts cohort : List Nat) (s : State α)
    (h : nextCohort p ts s = some cohort) : cohort ≠ [] := by
  unfold nextCohort at h
  cases hf : ts.filter (isShuffle p s) with
  | nil => simp [hf] at h
  | cons first rest =>
      simp only [hf, List.head?_cons, bind, pure, Option.some_bind, Option.some.injEq] at h
      subst cohort
      have hm : first ∈ ts := (List.mem_filter.mp (show first ∈ ts.filter (isShuffle p s) by
        rewrite [hf]
        simp)).1
      have hc : first ∈ ts.filter (fun t => s.pc t == s.pc first) :=
        List.mem_filter.mpr ⟨hm, by simp⟩
      intro he
      simp [he] at hc

def runWarp (ops : Ops α) (layout : Layout) (g : Geometry) (f : Fuel)
    (p : List LarkCollective.Instr) (ts : List Nat) : Nat → State α → Option (State α)
  | 0, _ => none
  | n + 1, s => do
      let s ← ts.foldlM (fun s t => LarkCollective.runLane ops layout g p t f.lane s) s
      match nextCohort p ts s with
      | some cohort =>
        let next ← runShuffle g p cohort s
        runWarp ops layout g f p ts n next
      | none =>
        let cut ← LarkCollective.converged p ts s
        if cut = .warp then runWarp ops layout g f p ts n (resume ts .warp s)
        else some s

def runBlock (ops : Ops α) (layout : Layout) (g : Geometry) (f : Fuel)
    (p : List LarkCollective.Instr) (b : Nat) : Nat → State α → Option (State α)
  | 0, _ => none
  | n + 1, s => do
      let ws := List.range ((g.block + g.warp - 1) / g.warp)
      let s ← ws.foldlM (fun s w =>
        runWarp ops layout g f p (warpThreads g b w) f.warp s) s
      let ts := blockThreads g b
      let cut ← LarkCollective.converged p ts s
      if cut = .block then runBlock ops layout g f p b n (resume ts .block s) else
        if cut = .grid ∨ cut = .halt then some s else none

def runGrid (ops : Ops α) (layout : Layout) (g : Geometry) (f : Fuel)
    (p : List LarkCollective.Instr) : Nat → State α → Option (State α)
  | 0, _ => none
  | n + 1, s => do
      let s ← (List.range g.grid).foldlM (fun s b =>
        runBlock ops layout g f p b f.block s) s
      let ts := List.range (g.grid * g.block)
      let cut ← LarkCollective.converged p ts s
      if cut = .grid then runGrid ops layout g f p n (resume ts .grid s) else
        if cut = .halt then some s else none

def runLaunch (ops : Ops α) (layout : Layout) (g : Geometry) (f : Fuel)
    (p : List LarkCollective.Instr) (s : State α) : Option (State α) :=
  if g.grid = 0 ∨ g.block = 0 ∨ g.warp ≠ 64 ∨ g.block % 64 ≠ 0 then none
  else runGrid ops layout g f p f.grid s

def Correct (ops : Ops α) (layout : Layout) (g : Geometry) (f : Fuel)
    (p : List LarkCollective.Instr) (spec : (Nat → Nat → α) → List α) : Prop :=
  ∀ input outside, ∃ final,
    runLaunch ops layout g f p (initial layout input outside) = some final ∧
    raceFree g final.trace = true ∧ extract layout final = some (spec input)

#print axioms runShuffle_preserves
#print axioms nextCohort_subset
#print axioms nextCohort_nonempty
end LarkPartitionCollective
