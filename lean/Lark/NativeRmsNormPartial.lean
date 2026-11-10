import Lark.NativeRmsNormFirstStage

/-! Execute the source lane-zero partial store and stop at the first block barrier.
This does not yet compose the complete six-stage wave or the block scheduler.
-/
namespace LarkNativeRmsNorm
open LarkNonlinear
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def partialCell (t warp : Nat) : Location := ⟨.shared, t / 1024, 0, warp⟩

def partialWritten (t warp : Nat) (value : α) (s : State α) : State α :=
  advance { record s t (partialCell t warp) true with
    memory := fun l => if l = partialCell t warp then some value else s.memory l } t 38

def partialAfter (t lane warp : Nat) (value : α) (s : State α) : State α :=
  if lane = 0 then partialWritten t warp value (advance s t 37) else advance s t 38

theorem partial_branch_code :
    program[36]? = some (.scalar (.branch (.eq (.ivar 2) (.const 0)) 38)) := by decide
theorem partial_store_code :
    program[37]? = some (.scalar (.store .shared 0 (.ivar 3) (.reg 0))) := by decide

theorem partial_location (p : Shape) (t warp : Nat) (hw : warp < 16) :
    location (layout p) (geometry p) t .shared 0 (warp : Int) true = some (partialCell t warp) := by
  simp [location, layout, geometry, partialCell, show ¬ (warp : Int) < 0 by omega, hw]

theorem partial_store_eq (p : Shape) (ops : Ops α) (t warp : Nat) (value : α) (s : State α)
    (hw : warp < 16) (hi : s.indices t 3 = some (warp : Int))
    (ha : s.regs t 0 = some value) (hp : s.pc t = 37) :
    execute ops (layout p) (geometry p) t (.store .shared 0 (.ivar 3) (.reg 0)) s =
      some (partialWritten t warp value s) := by
  simp [execute, evalIndex, hi, partial_location p t warp hw, evalExpr, ha, hp, partialWritten, record]

/-- Source PC 36 through its guarded store to the actual barrier at PC 38. -/
theorem partial_lane (p : Shape) (ops : Ops α) (t lane warp extra : Nat) (value : α) (s : State α)
    (hw : warp < 16) (hi2 : s.indices t 2 = some (lane : Int))
    (hi3 : s.indices t 3 = some (warp : Int)) (ha : s.regs t 0 = some value) (hp : s.pc t = 36) :
    LarkCollective.runLane ops (layout p) (geometry p) program t (extra + 3) s =
      some (partialAfter t lane warp value s) := by
  have heq : evalPredicate (geometry p) t s (.eq (.ivar 2) (.const 0)) = some (decide (lane = 0)) := by
    simp [evalPredicate, evalIndex, hi2, int32] <;> omega
  by_cases hl : lane = 0
  · have hg : evalPredicate (geometry p) t s (.eq (.ivar 2) (.const 0)) = some true := by simpa [hl] using heq
    let s1 := advance s t 37
    have h1 : execute ops (layout p) (geometry p) t (.branch (.eq (.ivar 2) (.const 0)) 38) s = some s1 := by
      simp only [execute, hg, hp, bind, pure, Option.bind]
      rfl
    have h2 := partial_store_eq p ops t warp value s1 hw hi3 ha (by simp [s1, advance])
    rewrite [scalar_step ops _ _ _ _ _ _ _ _
      (by simp [LarkCollective.parked, hp, partial_branch_code])
      (by simpa only [hp] using partial_branch_code) h1]
    rewrite [scalar_step ops _ _ _ _ _ _ _ _
      (by simp [LarkCollective.parked, s1, advance, partial_store_code])
      (by simpa only [s1, advance, ↓reduceIte] using partial_store_code) h2]
    have hcut : LarkCollective.parked program (partialWritten t warp value s1) t = some .block := by
      unfold LarkCollective.parked
      simp only [partialWritten, advance, ↓reduceIte]
      rewrite [first_barrier]
      rfl
    rewrite [LarkCollective.runLane, hcut]
    simp only [partialAfter, hl, ↓reduceIte]
    rfl
  · have hg : evalPredicate (geometry p) t s (.eq (.ivar 2) (.const 0)) = some false := by simpa [hl] using heq
    have h1 : execute ops (layout p) (geometry p) t (.branch (.eq (.ivar 2) (.const 0)) 38) s =
        some (advance s t 38) := by
      simp only [execute, hg, bind, pure, Option.bind]
      rfl
    rewrite [scalar_step ops _ _ _ _ _ _ _ _
      (by simp [LarkCollective.parked, hp, partial_branch_code])
      (by simpa only [hp] using partial_branch_code) h1]
    have hcut : LarkCollective.parked program (advance s t 38) t = some .block := by
      unfold LarkCollective.parked
      simp only [advance, ↓reduceIte]
      rewrite [first_barrier]
      rfl
    rewrite [LarkCollective.runLane, hcut]
    simp only [partialAfter, hl, ↓reduceIte]

theorem partial_fields (t lane warp : Nat) (value : α) (s : State α) :
    (partialAfter t lane warp value s).pc t = 38 ∧
    (partialAfter t lane warp value s).indices = s.indices ∧
    (partialAfter t lane warp value s).regs = s.regs ∧
    (partialAfter t lane warp value s).epochs = s.epochs := by
  unfold partialAfter
  split <;> simp [partialWritten, advance, record]

theorem partial_other (t u lane warp : Nat) (value : α) (s : State α) (hu : u ≠ t) :
    (partialAfter t lane warp value s).pc u = s.pc u := by
  unfold partialAfter
  split <;> simp [partialWritten, advance, record, hu]

theorem partial_value (t warp : Nat) (value : α) (s : State α) :
    (partialAfter t 0 warp value s).memory (partialCell t warp) = some value := by
  simp [partialAfter, partialWritten, advance, record]

theorem partial_global_memory (t lane warp : Nat) (value : α) (s : State α) (l : Location)
    (hl : l.space = .global) : (partialAfter t lane warp value s).memory l = s.memory l := by
  have hn : l ≠ partialCell t warp := by intro he; have := congrArg Location.space he; simp [partialCell, hl] at this
  unfold partialAfter
  split <;> simp [partialWritten, advance, record, hn]

theorem partial_reads (p : Shape) (input : Nat → Nat → α) (t lane warp : Nat) (value : α)
    (s : State α) (reads : Reads p input s) : Reads p input (partialAfter t lane warp value s) := by
  constructor
  · intro i hi
    exact (partial_global_memory t lane warp value s (globalCell 1 i) rfl).trans (reads.1 i hi)
  · intro i hi
    exact (partial_global_memory t lane warp value s (globalCell 2 i) rfl).trans (reads.2 i hi)

theorem partial_good (p : Shape) (t lane warp : Nat) (value : α) (s : State α)
    (hl : lane = (t % 1024) % 64) (hw : warp = (t % 1024) / 64) (he : (s.epochs t).block = 0)
    (good : ∀ a ∈ s.trace, LarkReductionFootprint.Good (traversal p) 0 a) :
    ∀ a ∈ (partialAfter t lane warp value s).trace, LarkReductionFootprint.Good (traversal p) 0 a := by
  by_cases hz : lane = 0
  · intro a ha
    simp only [partialAfter, hz, ↓reduceIte, partialWritten, advance, record, List.mem_cons] at ha
    rcases ha with rfl | ha
    · apply LarkReductionFootprint.Good.partialStore
      · rfl
      · rfl
      · rfl
      · exact hw
      · change (t % 1024) % 64 = 0
        omega
      · exact he
      · rfl
    · exact good a ha
  · simpa only [partialAfter, hz, ↓reduceIte, advance] using good

def firstLastAfter (ops : Ops α) (t lane warp valid : Nat) (a b : α) (s : State α) : State α :=
  partialAfter t lane warp (if lane + 32 < valid then ops.add a b else a)
    (guardedAfter ops t 33 lane 32 valid a b s)

/-- Actual source execution after the sixth shuffle through the first block barrier. -/
theorem first_last_lane (p : Shape) (ops : Ops α) (t lane warp valid : Nat) (a b : α) (s : State α)
    (hl : lane < 64) (hw : warp < 16)
    (hi2 : s.indices t 2 = some (lane : Int)) (hi3 : s.indices t 3 = some (warp : Int))
    (hv : s.indices t 4 = some (valid : Int))
    (ha : s.regs t 0 = some a) (hb : s.regs t 1 = some b) (hp : s.pc t = 34) :
    LarkCollective.runLane ops (layout p) (geometry p) program t fuel.lane s =
      some (firstLastAfter ops t lane warp valid a b s) := by
  let next := guardedAfter ops t 33 lane 32 valid a b s
  let value := if lane + 32 < valid then ops.add a b else a
  have hpres := guarded_preserves ops t 33 lane 32 valid a b s
  have hi2' : next.indices t 2 = some (lane : Int) :=
    (congrFun (congrFun hpres.1 t) 2).trans hi2
  have hi3' : next.indices t 3 = some (warp : Int) :=
    (congrFun (congrFun hpres.1 t) 3).trans hi3
  have ha' : next.regs t 0 = some value := guarded_acc ops t 33 lane 32 valid a b s ha
  have hp' : next.pc t = 36 := guarded_pc ops t 33 lane 32 valid a b s
  by_cases h : lane + 32 < valid
  · rewrite [show fuel.lane = 254 + 2 by decide,
      guarded_true_eq p ops t 33 lane 32 valid 254 (.ivar 4) a b s hl (by decide) hi2 hv ha hb hp
        (first_guard_code 5 (by decide)).1 (first_guard_code 5 (by decide)).2 h]
    exact partial_lane p ops t lane warp 251 value next hw hi2' hi3' ha' hp'
  · rewrite [show fuel.lane = 255 + 1 by decide,
      guarded_false_eq p ops t 33 lane 32 valid 255 (.ivar 4) a b s hl (by decide) hi2 hv hp
        (first_guard_code 5 (by decide)).1 h]
    exact partial_lane p ops t lane warp 252 value next hw hi2' hi3' ha' hp'

theorem first_last_fields (ops : Ops α) (t lane warp valid : Nat) (a b : α) (s : State α) :
    (firstLastAfter ops t lane warp valid a b s).pc t = 38 ∧
    (firstLastAfter ops t lane warp valid a b s).indices = s.indices ∧
    (firstLastAfter ops t lane warp valid a b s).epochs = s.epochs := by
  have h := partial_fields t lane warp (if lane + 32 < valid then ops.add a b else a)
    (guardedAfter ops t 33 lane 32 valid a b s)
  have hg := guarded_preserves ops t 33 lane 32 valid a b s
  exact ⟨h.1, h.2.1.trans hg.1, h.2.2.2.trans hg.2.2.1⟩

theorem first_last_other (ops : Ops α) (t u lane warp valid : Nat) (a b : α) (s : State α)
    (hu : u ≠ t) :
    (firstLastAfter ops t lane warp valid a b s).pc u = s.pc u ∧
    (firstLastAfter ops t lane warp valid a b s).regs u = s.regs u := by
  have hpc := partial_other t u lane warp (if lane + 32 < valid then ops.add a b else a)
    (guardedAfter ops t 33 lane 32 valid a b s) hu
  have hg := guarded_other ops t u 33 lane 32 valid a b s hu
  have hr := (partial_fields t lane warp (if lane + 32 < valid then ops.add a b else a)
    (guardedAfter ops t 33 lane 32 valid a b s)).2.2.1
  exact ⟨hpc.trans hg.1, (congrFun hr u).trans hg.2⟩

theorem first_last_acc (ops : Ops α) (t lane warp valid : Nat) (a b : α) (s : State α)
    (ha : s.regs t 0 = some a) :
    (firstLastAfter ops t lane warp valid a b s).regs t 0 =
      some (if lane + 32 < valid then ops.add a b else a) := by
  have h := (partial_fields t lane warp (if lane + 32 < valid then ops.add a b else a)
    (guardedAfter ops t 33 lane 32 valid a b s)).2.2.1
  exact (congrFun (congrFun h t) 0).trans (guarded_acc ops t 33 lane 32 valid a b s ha)

theorem first_last_memory_nonzero (ops : Ops α) (t lane warp valid : Nat) (a b : α) (s : State α)
    (hl : lane ≠ 0) : (firstLastAfter ops t lane warp valid a b s).memory = s.memory := by
  change (partialAfter t lane warp _ _).memory = _
  simp only [partialAfter, hl, ↓reduceIte, advance]
  exact (guarded_preserves ops t 33 lane 32 valid a b s).2.1

theorem first_last_value (ops : Ops α) (t warp valid : Nat) (a b : α) (s : State α) :
    (firstLastAfter ops t 0 warp valid a b s).memory (partialCell t warp) =
      some (if 32 < valid then ops.add a b else a) :=
  partial_value t warp _ _

theorem first_last_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t lane warp valid : Nat) (a b : α) (s : State α) (reads : Reads p input s) :
    Reads p input (firstLastAfter ops t lane warp valid a b s) :=
  partial_reads p input t lane warp _ _
    (reads_of_memory p input s _ reads (guarded_preserves ops t 33 lane 32 valid a b s).2.1)

theorem first_last_good (p : Shape) (ops : Ops α) (t lane warp valid : Nat) (a b : α) (s : State α)
    (hl : lane = (t % 1024) % 64) (hw : warp = (t % 1024) / 64) (he : (s.epochs t).block = 0)
    (good : ∀ access ∈ s.trace, LarkReductionFootprint.Good (traversal p) 0 access) :
    ∀ access ∈ (firstLastAfter ops t lane warp valid a b s).trace,
      LarkReductionFootprint.Good (traversal p) 0 access := by
  have hpres := guarded_preserves ops t 33 lane 32 valid a b s
  apply partial_good p t lane warp _ _ hl hw
  · exact (congrArg (fun epochs => (epochs t).block) hpres.2.2.1).trans he
  · exact fun access ha => good access (hpres.2.2.2 ▸ ha)

#print axioms partial_store_eq
#print axioms partial_lane
#print axioms partial_reads
#print axioms partial_good
#print axioms first_last_lane
#print axioms first_last_fields
#print axioms first_last_good
end LarkNativeRmsNorm
