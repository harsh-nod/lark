import Lark.PtxFeedForwardUpLaunch
import Lark.PtxFeedForwardDownLaunch

/- Sequential host composition of the two exact compiled FFN stages.
   Each launch keeps its original three-parameter layout. Explicit bijections
   bind them to five shared logical allocations: x, w1, down, hidden and out.
   Local grid epochs are embedded injectively into a host launch namespace;
   this represents the ordering of the two launches in one stream.
   Scalar-operation and logical-pointer correspondence remain trusted. -/
namespace LarkPtxFeedForward.Pipeline
open LarkNonlinear LarkPtxMatrix
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- Symbolic proof parameters; canonical specialization fixes both full launches. -/
structure LaunchCounts where
  upCount : Nat
  downCount : Nat
  up_exact : upCount = 65536
  down_exact : downCount = 16384

def originalCounts : LaunchCounts := ⟨65536, 16384, rfl, rfl⟩

structure Renaming where
  forward : Nat → Nat
  backward : Nat → Nat
  forward_backward : ∀ b, forward (backward b) = b
  backward_forward : ∀ b, backward (forward b) = b

def upIndex : Nat → Nat
  | 2 => 3
  | 3 => 2
  | n => n

theorem up_inverse : ∀ b, upIndex (upIndex b) = b
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | n+4 => rfl

def upRenaming : Renaming := ⟨upIndex, upIndex, up_inverse, up_inverse⟩

def downIndex : Nat → Nat
  | 0 => 3
  | 1 => 2
  | 2 => 4
  | 3 => 0
  | 4 => 1
  | n => n

def downInverse : Nat → Nat
  | 0 => 3
  | 1 => 4
  | 2 => 1
  | 3 => 0
  | 4 => 2
  | n => n

theorem down_forward_backward : ∀ b, downIndex (downInverse b) = b
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | n+5 => rfl

theorem down_backward_forward : ∀ b, downInverse (downIndex b) = b
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | n+5 => rfl

def downRenaming : Renaming :=
  ⟨downIndex, downInverse, down_forward_backward, down_backward_forward⟩

def renameLocation (f : Nat → Nat) (l : Location) : Location :=
  { l with buffer := f l.buffer }

theorem rename_roundtrip (r : Renaming) (l : Location) :
    renameLocation r.forward (renameLocation r.backward l) = l := by
  cases l
  simp [renameLocation, r.forward_backward]

def cell (buffer index : Nat) : Location := ⟨.global, 0, buffer, index⟩

def layout : Layout :=
  ⟨[⟨.input, 64*256⟩, ⟨.input, 256*1024⟩, ⟨.input, 1024*256⟩,
     ⟨.scratch, 64*1024⟩, ⟨.output, 64*256⟩], [], []⟩

def view (r : Renaming) (root : State α) : State α :=
  { root with memory := fun l => root.memory (renameLocation r.forward l), trace := [] }

def liftAccess (launch : Nat) (f : Nat → Nat) (a : Access) : Access :=
  { a with location := renameLocation f a.location,
           epoch := { a.epoch with grid := 2*a.epoch.grid+launch } }

theorem epoch_namespace_injective (launch a b : Nat) :
    2*a+launch = 2*b+launch ↔ a = b := by omega

theorem launch_namespaces_disjoint (a b : Nat) : 2*a ≠ 2*b+1 := by omega

def commit (r : Renaming) (launch : Nat) (before stage : State α) : State α :=
  { stage with memory := fun l => stage.memory (renameLocation r.backward l),
               trace := before.trace ++ stage.trace.map (liftAccess launch r.forward),
               epochs := fun t => { stage.epochs t with grid := 2*(stage.epochs t).grid+launch } }

def upStart (input : Nat → Nat → α) (outside : Location → Option α) : State α :=
  view upRenaming (initial layout input outside)

def upEnd (counts : LaunchCounts) (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) : State α :=
  FfnUp.runLanes ops input 0 counts.upCount (upStart input outside)

def afterUp (counts : LaunchCounts) (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) : State α :=
  commit upRenaming 0 (initial layout input outside) (upEnd counts ops input outside)

/-- Ghost scalar names for proving reads; the actual down-start memory is a view
    of the up-stage result, not a fresh reference-generated intermediate. -/
def downInput (ops : Ops α) (input : Nat → Nat → α) (slot i : Nat) : α :=
  if slot = 0 then Reference.hiddenValue ops input i else input 2 i

def downStart (counts : LaunchCounts) (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) : State α :=
  view downRenaming (afterUp counts ops input outside)

def downEnd (counts : LaunchCounts) (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) : State α :=
  FfnDown.runLanes ops (downInput ops input) 0 counts.downCount (downStart counts ops input outside)

def finalState (counts : LaunchCounts) (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) : State α :=
  commit downRenaming 1 (afterUp counts ops input outside) (downEnd counts ops input outside)

theorem up_reads (input : Nat → Nat → α) (outside : Location → Option α) :
    FfnUp.Reads input (FfnUp.start (upStart input outside)) := by
  constructor
  · intro i hi
    change (initial layout input outside).memory (cell 0 i) = _
    simp [initial, layout, cell, hi]
  · intro i hi
    change (initial layout input outside).memory (cell 1 i) = _
    simp [initial, layout, cell, hi]

theorem up_execution (counts : LaunchCounts) (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) :
    FfnUp.LaneSequence ops FfnUp.program 0 counts.upCount (upStart input outside) (upEnd counts ops input outside) := by
  simpa only [upEnd] using
    FfnUp.runLanes_execute ops input 0 counts.upCount _ (by have hc := counts.up_exact; omega) (up_reads input outside)

theorem hidden_outputs (counts : LaunchCounts) (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α)
    (i : Nat) (hi : i < 65536) :
    (afterUp counts ops input outside).memory (cell 3 i) = some (Reference.hiddenValue ops input i) := by
  change (upEnd counts ops input outside).memory (FfnUp.outputCell i) = _
  rw [upEnd, FfnUp.runLanes_output_memory]
  have hcount : i < counts.upCount := by have hc := counts.up_exact; omega
  simp [hcount, FfnUp.reference]

theorem afterUp_other (counts : LaunchCounts) (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α)
    (l : Location) (h : ∀ i, i < 65536 → l ≠ cell 3 i) :
    (afterUp counts ops input outside).memory l = (initial layout input outside).memory l := by
  have hn : ∀ i, 0 ≤ i → i < 0+counts.upCount →
      renameLocation upRenaming.backward l ≠ FfnUp.outputCell i := by
    intro i _ hi he
    apply h i (by have hc := counts.up_exact; omega)
    have hr := congrArg (renameLocation upRenaming.forward) he
    rw [rename_roundtrip] at hr
    simpa only [upRenaming, renameLocation, upIndex, FfnUp.outputCell, cell] using hr
  change (upEnd counts ops input outside).memory
    (renameLocation upRenaming.backward l) = _
  rw [upEnd, FfnUp.runLanes_other_memory ops input 0 counts.upCount (upStart input outside) _ hn]
  exact congrArg (initial layout input outside).memory (rename_roundtrip upRenaming l)

theorem down_reads (counts : LaunchCounts) (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) :
    FfnDown.Reads (downInput ops input) (FfnDown.start (downStart counts ops input outside)) := by
  constructor
  · intro i hi
    change (afterUp counts ops input outside).memory (cell 3 i) = some (Reference.hiddenValue ops input i)
    exact hidden_outputs counts ops input outside i hi
  · intro i hi
    change (afterUp counts ops input outside).memory (cell 2 i) = some (input 2 i)
    rw [afterUp_other counts ops input outside (cell 2 i) (by
      intro j _ he
      have hb := congrArg Location.buffer he
      have hbad : (2 : Nat) = 3 := hb
      omega)]
    simp [initial, layout, cell, hi]

theorem down_execution (counts : LaunchCounts) (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) :
    FfnDown.LaneSequence ops FfnDown.program 0 counts.downCount
      (downStart counts ops input outside) (downEnd counts ops input outside) := by
  simpa only [downEnd] using
    FfnDown.runLanes_execute ops (downInput ops input) 0 counts.downCount _ (by have hc := counts.down_exact; omega) (down_reads counts ops input outside)

theorem actual_intermediate_shared (counts : LaunchCounts) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (i : Nat) :
    (downStart counts ops input outside).memory (cell 0 i) =
      (upEnd counts ops input outside).memory (cell 2 i) := rfl

theorem down_reference (ops : Ops α) (input : Nat → Nat → α) (t : Nat) :
    FfnDown.reference ops (downInput ops input) t = Reference.outputValue ops input t := by
  have he : FfnDown.referenceTerm ops (downInput ops input) t =
      Reference.downTermWith ops input 256 1024 256 t := by
    funext j acc
    rfl
  exact congrArg (fun term => ops.toHalf (Reference.scalarFold term 0 1024 (ops.literal 0 1))) he

theorem output_values (counts : LaunchCounts) (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α)
    (i : Nat) (hi : i < 16384) :
    (finalState counts ops input outside).memory (cell 4 i) = some (Reference.outputValue ops input i) := by
  change (downEnd counts ops input outside).memory
    (FfnDown.outputCell i) = _
  rw [downEnd, FfnDown.runLanes_output_memory]
  have hcount : i < counts.downCount := by have hc := counts.down_exact; omega
  simp [hcount, down_reference]

theorem final_other (counts : LaunchCounts) (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α)
    (l : Location) (h : ∀ i, i < 16384 → l ≠ cell 4 i) :
    (finalState counts ops input outside).memory l = (afterUp counts ops input outside).memory l := by
  have hn : ∀ i, 0 ≤ i → i < 0+counts.downCount →
      renameLocation downRenaming.backward l ≠ FfnDown.outputCell i := by
    intro i _ hi he
    apply h i (by have hc := counts.down_exact; omega)
    have hr := congrArg (renameLocation downRenaming.forward) he
    rw [rename_roundtrip] at hr
    simpa only [downRenaming, renameLocation, downIndex, FfnDown.outputCell, cell] using hr
  change (downEnd counts ops input outside).memory
    (renameLocation downRenaming.backward l) = _
  rw [downEnd, FfnDown.runLanes_other_memory ops (downInput ops input) 0 counts.downCount (downStart counts ops input outside) _ hn]
  exact congrArg (afterUp counts ops input outside).memory (rename_roundtrip downRenaming l)

theorem frame (counts : LaunchCounts) (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α)
    (l : Location) (hh : ∀ i, i < 65536 → l ≠ cell 3 i)
    (ho : ∀ i, i < 16384 → l ≠ cell 4 i) :
    (finalState counts ops input outside).memory l = (initial layout input outside).memory l :=
  (final_other counts ops input outside l ho).trans (afterUp_other counts ops input outside l hh)

def PhaseSafe (output : Nat) (reads : Nat → Prop) (a : Access) : Prop :=
  if a.write then a.location = cell output a.thread
  else a.location.space = .global ∧ a.location.owner = 0 ∧ reads a.location.buffer

theorem phase_conflict_false (g : Geometry) (output : Nat) (reads : Nat → Prop)
    (distinct : ∀ b, reads b → b ≠ output) (a b : Access)
    (hasafe : PhaseSafe output reads a) (hbsafe : PhaseSafe output reads b) :
    conflict g a b = false := by
  by_cases he : a.thread = b.thread
  · simp [conflict, he]
  · cases haw : a.write <;> cases hbw : b.write <;>
      simp [PhaseSafe, haw, hbw] at hasafe hbsafe
    · simp [conflict, haw, hbw]
    · have hn := distinct a.location.buffer hasafe.2.2
      simp [conflict, sameLocation, hbsafe, haw, hbw, cell, hn]
    · have hn : output ≠ b.location.buffer := Ne.symm (distinct b.location.buffer hbsafe.2.2)
      simp [conflict, sameLocation, hasafe, haw, hbw, cell, hn]
    · simp [conflict, sameLocation, hasafe, hbsafe, cell, haw, hbw, he]

theorem up_access_safe (a : Access) (h : FfnUp.AccessSafe a) :
    PhaseSafe 3 (fun b => b = 0 ∨ b = 1) (liftAccess 0 upRenaming.forward a) := by
  cases hw : a.write
  · simp [FfnUp.AccessSafe, hw] at h
    have hb : a.location.buffer = 0 ∨ a.location.buffer = 1 := by omega
    rcases hb with hb | hb <;>
      simp [PhaseSafe, liftAccess, hw, renameLocation, h.1, h.2.1, hb, upRenaming, upIndex]
  · simp [FfnUp.AccessSafe, hw] at h
    simp [PhaseSafe, liftAccess, hw, h, FfnUp.outputCell, cell, renameLocation, upRenaming, upIndex]

theorem down_access_safe (a : Access) (h : FfnDown.AccessSafe a) :
    PhaseSafe 4 (fun b => b = 3 ∨ b = 2) (liftAccess 1 downRenaming.forward a) := by
  cases hw : a.write
  · simp [FfnDown.AccessSafe, hw] at h
    have hb : a.location.buffer = 0 ∨ a.location.buffer = 1 := by omega
    rcases hb with hb | hb <;>
      simp [PhaseSafe, liftAccess, hw, renameLocation, h.1, h.2.1, hb, downRenaming, downIndex]
  · simp [FfnDown.AccessSafe, hw] at h
    simp [PhaseSafe, liftAccess, hw, h, FfnDown.outputCell, cell, renameLocation, downRenaming, downIndex]

theorem cross_conflict_false (g : Geometry) (a b : Access) :
    conflict g (liftAccess 0 upRenaming.forward a) (liftAccess 1 downRenaming.forward b) = false := by
  have h := launch_namespaces_disjoint a.epoch.grid b.epoch.grid
  simp [conflict, ordered, liftAccess, h]

theorem reverse_cross_conflict_false (g : Geometry) (a b : Access) :
    conflict g (liftAccess 1 downRenaming.forward a) (liftAccess 0 upRenaming.forward b) = false := by
  have h := Ne.symm (launch_namespaces_disjoint b.epoch.grid a.epoch.grid)
  simp [conflict, ordered, liftAccess, h]

theorem race_free (counts : LaunchCounts) (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) :
    raceFree FfnUp.geometry (finalState counts ops input outside).trace = true := by
  have hu : FfnUp.TraceSafe (upEnd counts ops input outside).trace := by
    simpa only [upEnd] using FfnUp.runLanes_trace_safe ops input 0 counts.upCount (upStart input outside)
      (by simp [FfnUp.TraceSafe, upStart, view])
  have hd : FfnDown.TraceSafe (downEnd counts ops input outside).trace := by
    simpa only [downEnd] using FfnDown.runLanes_trace_safe ops (downInput ops input) 0 counts.downCount (downStart counts ops input outside)
      (by simp [FfnDown.TraceSafe, downStart, view])
  change raceFree FfnUp.geometry
    ((upEnd counts ops input outside).trace.map (liftAccess 0 upRenaming.forward) ++
     (downEnd counts ops input outside).trace.map (liftAccess 1 downRenaming.forward)) = true
  apply List.all_eq_true.mpr
  intro a ha
  apply List.all_eq_true.mpr
  intro b hb
  suffices hconflict : conflict FfnUp.geometry a b = false by simp [hconflict]
  rcases List.mem_append.mp ha with ha | ha <;> rcases List.mem_append.mp hb with hb | hb
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hb
    exact phase_conflict_false _ 3 (fun b => b = 0 ∨ b = 1)
      (by intro b h; rcases h with rfl | rfl <;> decide) _ _ (up_access_safe a (hu a ha)) (up_access_safe b (hu b hb))
  · obtain ⟨a, _, rfl⟩ := List.mem_map.mp ha
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp hb
    exact cross_conflict_false _ a b
  · obtain ⟨a, _, rfl⟩ := List.mem_map.mp ha
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp hb
    exact reverse_cross_conflict_false _ a b
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hb
    exact phase_conflict_false _ 4 (fun b => b = 3 ∨ b = 2)
      (by intro b h; rcases h with rfl | rfl <;> decide) _ _ (down_access_safe a (hd a ha)) (down_access_safe b (hd b hb))

theorem extract_outputs (s : State α) (values : Nat → α)
    (h : ∀ i, i < 16384 → s.memory (cell 4 i) = some (values i)) :
    extract layout s = some ((List.range 16384).map values) := by
  simp only [extract, layout, List.zipIdx_cons, List.zipIdx_nil, List.flatMap_cons,
    List.flatMap_nil, List.nil_append]
  simp only [List.map_cons, List.map_nil, show Role.input ≠ Role.output by decide,
    show Role.scratch ≠ Role.output by decide, ↓reduceIte, List.nil_append, List.append_nil]
  change (((List.range 16384).map (fun i => (4, i))).mapM
    (fun bi => s.memory ⟨.global, 0, bi.1, bi.2⟩) : Option (List α)) = _
  rw [LarkPointwise.mapM_map]
  exact LarkPointwise.mapM_some (List.range 16384) _ _ (by
    intro i hi
    exact h i (List.mem_range.mp hi))

def ExecutionForCounts (counts : LaunchCounts) (ops : Ops α) (up down : List Instruction) (initial final : State α) : Prop :=
  ∃ first second,
    FfnUp.LaneSequence ops up 0 counts.upCount (view upRenaming initial) first ∧
    FfnDown.LaneSequence ops down 0 counts.downCount (view downRenaming (commit upRenaming 0 initial first)) second ∧
    final = commit downRenaming 1 (commit upRenaming 0 initial first) second

def CorrectForCounts (counts : LaunchCounts) (ops : Ops α) (up down : List Instruction) : Prop :=
  ∀ input outside, ∃ final,
    ExecutionForCounts counts ops up down (initial layout input outside) final ∧
    raceFree FfnUp.geometry final.trace = true ∧
    extract layout final = some (Reference.referenceSpec ops input) ∧
    (∀ l, (∀ i, i < 65536 → l ≠ cell 3 i) → (∀ i, i < 16384 → l ≠ cell 4 i) →
      final.memory l = (initial layout input outside).memory l)

theorem kernel_correct_for_counts (counts : LaunchCounts) (ops : Ops α) : CorrectForCounts counts ops FfnUp.program FfnDown.program := by
  intro input outside
  refine ⟨finalState counts ops input outside, ?_, race_free counts ops input outside, ?_, frame counts ops input outside⟩
  · exact ⟨upEnd counts ops input outside, downEnd counts ops input outside,
      up_execution counts ops input outside, down_execution counts ops input outside, rfl⟩
  · exact extract_outputs _ _ (output_values counts ops input outside)

def Execution (ops : Ops α) (up down : List Instruction) (initial final : State α) : Prop :=
  ExecutionForCounts originalCounts ops up down initial final

def Correct (ops : Ops α) (up down : List Instruction) : Prop :=
  CorrectForCounts originalCounts ops up down

theorem kernel_correct (ops : Ops α) : Correct ops FfnUp.program FfnDown.program :=
  kernel_correct_for_counts originalCounts ops

#print axioms rename_roundtrip
#print axioms epoch_namespace_injective
#print axioms launch_namespaces_disjoint
#print axioms up_execution
#print axioms hidden_outputs
#print axioms afterUp_other
#print axioms down_reads
#print axioms down_execution
#print axioms actual_intermediate_shared
#print axioms down_reference
#print axioms output_values
#print axioms frame
#print axioms race_free
#print axioms extract_outputs
#print axioms kernel_correct_for_counts
#print axioms kernel_correct
end LarkPtxFeedForward.Pipeline
