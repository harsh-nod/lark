import Lark.PtxFeedForwardDownExit
import Lark.PtxFeedForwardReference

/- Complete down-stage launch and independent tensor reference. The pipeline
   proof must still connect the actual shared FP16 intermediate of both stages. -/
namespace LarkPtxMatrix
open LarkNonlinear LarkPtxPointwise LarkPtxDot
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace FfnDown

def referenceTerm (ops : Ops α) (input : Nat → Nat → α) (t k : Nat) (acc : α) : α :=
  ops.add acc (ops.mul (ops.fromHalf (input 0 (t/256*1024+k))) (ops.fromHalf (input 1 (k*256+t%256))))

def referenceFold (ops : Ops α) (input : Nat → Nat → α) (t : Nat) : Nat → Nat → α → α
  | _, 0, acc => acc
  | k, r+1, acc => referenceFold ops input t (k+1) r (referenceTerm ops input t k acc)

theorem foldTerms_reference (ops : Ops α) (input : Nat → Nat → α) (t c j r : Nat) (acc : α) :
    foldTerms ops input t c j r acc = referenceFold ops input t (16*c+j) r acc := by
  induction r generalizing j acc with
  | zero => rfl
  | succ r ih =>
      simp only [foldTerms, ih, referenceFold, nextValue, referenceTerm, Nat.add_assoc]

theorem referenceFold_append (ops : Ops α) (input : Nat → Nat → α) (t k m n : Nat) (acc : α) :
    referenceFold ops input t k (m+n) acc =
      referenceFold ops input t (k+m) n (referenceFold ops input t k m acc) := by
  induction m generalizing k acc with
  | zero => simp [referenceFold]
  | succ m ih =>
      have he : m+1+n = (m+n)+1 := by omega
      simp only [he, referenceFold, ih]
      have hk : k+1+m = k+(m+1) := by omega
      rw [hk]

theorem foldChunks_reference (ops : Ops α) (input : Nat → Nat → α) (t c r : Nat) (acc : α) :
    foldChunks ops input t c r acc = referenceFold ops input t (16*c) (16*r) acc := by
  induction r generalizing c acc with
  | zero => rfl
  | succ r ih =>
      rw [foldChunks, chunkValue, ih, foldTerms_reference]
      have he : 16*(r+1) = 16+16*r := by omega
      rw [he, referenceFold_append]
      have hc : 16*(c+1) = 16*c+16 := by omega
      simp only [hc, Nat.add_zero]

theorem referenceFold_scalarFold (ops : Ops α) (input : Nat → Nat → α)
    (t k r : Nat) (acc : α) :
    referenceFold ops input t k r acc =
      LarkPtxFeedForward.Reference.scalarFold (referenceTerm ops input t) k r acc := by
  induction r generalizing k acc with
  | zero => rfl
  | succ r ih => exact ih (k+1) (referenceTerm ops input t k acc)

def reference (ops : Ops α) (input : Nat → Nat → α) (t : Nat) : α :=
  ops.toHalf (LarkPtxFeedForward.Reference.scalarFold (referenceTerm ops input t) 0 1024 (ops.literal 0 1))

theorem dotValue_reference (ops : Ops α) (input : Nat → Nat → α) (t : Nat) :
    ops.toHalf (dotValue ops input t) = reference ops input t := by
  unfold dotValue reference
  rw [foldChunks_reference, referenceFold_scalarFold]

theorem laneResult_reference (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) :
    (laneResult ops input t s).registers.base.memory =
      fun l => if l = outputCell t then some (reference ops input t) else s.memory l := by
  rw [laneResult_memory, dotValue_reference]

def afterLane (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) : State α :=
  (laneResult ops input t s).registers.base

theorem afterLane_memory (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) :
    (afterLane ops input t s).memory =
      fun l => if l = outputCell t then some (reference ops input t) else s.memory l :=
  laneResult_reference ops input t s

theorem afterLane_reads (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α)
    (h : Reads input (start s)) : Reads input (start (afterLane ops input t s)) := by
  constructor
  · intro i hi
    change (afterLane ops input t s).memory ⟨.global, 0, 0, i⟩ = _
    rw [afterLane_memory]
    simpa [outputCell] using h.1 i hi
  · intro i hi
    change (afterLane ops input t s).memory ⟨.global, 0, 1, i⟩ = _
    rw [afterLane_memory]
    simpa [outputCell] using h.2 i hi

inductive LaneSequence (ops : Ops α) (p : List Instruction) : Nat → Nat → State α → State α → Prop where
  | nil (k : Nat) (s : State α) : LaneSequence ops p k 0 s s
  | next {k r : Nat} {s final : State α} {m : Machine α} :
      Steps ops layout geometry k p (start s) m →
      m.registers.stopped = true →
      LaneSequence ops p (k+1) r m.registers.base final →
      LaneSequence ops p k (r+1) s final

def runLanes (ops : Ops α) (input : Nat → Nat → α) : Nat → Nat → State α → State α
  | _, 0, s => s
  | k, r+1, s => runLanes ops input (k+1) r (afterLane ops input k s)

theorem runLanes_execute (ops : Ops α) (input : Nat → Nat → α) (k r : Nat) (s : State α)
    (hcount : k+r ≤ 16384) (hreads : Reads input (start s)) :
    LaneSequence ops program k r s (runLanes ops input k r s) := by
  induction r generalizing k s with
  | zero => exact .nil k s
  | succ r ih =>
      have lane := source_lane ops input k s (by omega) hreads
      have rest := ih (k+1) (afterLane ops input k s) (by omega) (afterLane_reads ops input k s hreads)
      exact .next lane.1 lane.2.1 rest

theorem runLanes_reads (ops : Ops α) (input : Nat → Nat → α) (k r : Nat) (s : State α)
    (hreads : Reads input (start s)) : Reads input (start (runLanes ops input k r s)) := by
  induction r generalizing k s with
  | zero => exact hreads
  | succ r ih => exact ih (k+1) (afterLane ops input k s) (afterLane_reads ops input k s hreads)

theorem runLanes_output_memory (ops : Ops α) (input : Nat → Nat → α) (k r i : Nat) (s : State α) :
    (runLanes ops input k r s).memory (outputCell i) =
      if k ≤ i ∧ i < k+r then some (reference ops input i) else s.memory (outputCell i) := by
  induction r generalizing k s with
  | zero =>
      have hn : ¬ (k ≤ i ∧ i < k) := by omega
      simp [runLanes, hn]
  | succ r ih =>
      rw [runLanes, ih]
      by_cases hi : i = k
      · subst i
        have hrest : ¬ (k+1 ≤ k ∧ k < k+1+r) := by omega
        have hwhole : k ≤ k ∧ k < k+(r+1) := by omega
        simp [afterLane_memory, hrest, hwhole]
      · have hloc : outputCell i ≠ outputCell k := by
          intro he
          exact hi (congrArg Location.offset he)
        have hrange : (k+1 ≤ i ∧ i < k+1+r) ↔ (k ≤ i ∧ i < k+(r+1)) := by omega
        rw [afterLane_memory]
        simp only [hloc, if_false, hrange]

theorem runLanes_other_memory (ops : Ops α) (input : Nat → Nat → α) (k r : Nat) (s : State α)
    (l : Location) (h : ∀ i, k ≤ i → i < k+r → l ≠ outputCell i) :
    (runLanes ops input k r s).memory l = s.memory l := by
  induction r generalizing k s with
  | zero => rfl
  | succ r ih =>
      have htail : ∀ i, k+1 ≤ i → i < k+1+r → l ≠ outputCell i := by
        intro i hi hj
        exact h i (by omega) (by omega)
      rw [runLanes, ih (k+1) (afterLane ops input k s) htail, afterLane_memory]
      simp only [if_neg (h k (by omega) (by omega))]

theorem initial_reads (input : Nat → Nat → α) (outside : Location → Option α) :
    Reads input (start (initial layout input outside)) := by
  constructor
  · intro i hi
    change (initial layout input outside).memory ⟨.global, 0, 0, i⟩ = _
    simp [initial, layout, hi]
  · intro i hi
    change (initial layout input outside).memory ⟨.global, 0, 1, i⟩ = _
    simp [initial, layout, hi]

def finalState (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) : State α :=
  runLanes ops input 0 16384 (initial layout input outside)

theorem launch_execution (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) :
    LaneSequence ops program 0 16384 (initial layout input outside) (finalState ops input outside) :=
  runLanes_execute ops input 0 16384 _ (by decide) (initial_reads input outside)

theorem launch_outputs (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α)
    (i : Nat) (hi : i < 16384) : (finalState ops input outside).memory (outputCell i) =
      some (reference ops input i) := by
  unfold finalState
  rw [runLanes_output_memory]
  simp [hi]

theorem launch_other_memory (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (l : Location)
    (h : ∀ i, i < 16384 → l ≠ outputCell i) :
    (finalState ops input outside).memory l = (initial layout input outside).memory l := by
  unfold finalState
  have hp : ∀ i, 0 ≤ i → i < 0+16384 → l ≠ outputCell i := fun i _ hi => h i hi
  rw [runLanes_other_memory ops input 0 16384 (initial layout input outside) l hp]


theorem control_trace (c : Nat) (s : Machine α) :
    (controlResult c s).registers.base.trace = s.registers.base.trace := rfl

def AccessSafe (a : Access) : Prop :=
  if a.write then a.location = outputCell a.thread
  else a.location.space = .global ∧ a.location.owner = 0 ∧ a.location.buffer < 2

def TraceSafe (trace : List Access) : Prop := ∀ a ∈ trace, AccessSafe a

theorem termResult_trace_safe (ops : Ops α) (t c j : Nat) (a b acc : α) (s : Machine α)
    (h : TraceSafe s.registers.base.trace) :
    TraceSafe (termResult ops t c j a b acc s).registers.base.trace := by
  intro access ha
  change access ∈ (⟨t, bCell t c j, false, s.registers.base.epochs t⟩ ::
    ⟨t, aCell t c j, false, s.registers.base.epochs t⟩ :: s.registers.base.trace) at ha
  simp only [List.mem_cons] at ha
  rcases ha with rfl | rfl | ha
  · simp [AccessSafe, bCell]
  · simp [AccessSafe, aCell]
  · exact h access ha

theorem runTerms_trace_safe (ops : Ops α) (input : Nat → Nat → α) (t c j r : Nat)
    (acc : α) (s : Machine α) (h : TraceSafe s.registers.base.trace) :
    TraceSafe (runTerms ops input t c j r acc s).registers.base.trace := by
  induction r generalizing j acc s with
  | zero => exact h
  | succ r ih =>
      exact ih (j+1) (nextValue ops input t c j acc) (chunkStep ops input t c j acc s)
        (termResult_trace_safe ops t c j _ _ acc s h)

theorem iteration_trace_safe (ops : Ops α) (input : Nat → Nat → α) (t c : Nat)
    (acc : α) (s : Machine α) (h : TraceSafe s.registers.base.trace) :
    TraceSafe (iteration ops input t c acc s).registers.base.trace := by
  rw [iteration, control_trace]
  unfold bodyEnd
  exact runTerms_trace_safe ops input t c 0 16 acc (bodyStart t c s) h

theorem runChunks_trace_safe (ops : Ops α) (input : Nat → Nat → α) (t c r : Nat)
    (acc : α) (s : Machine α) (h : TraceSafe s.registers.base.trace) :
    TraceSafe (runChunks ops input t c r acc s).registers.base.trace := by
  induction r generalizing c acc s with
  | zero => exact h
  | succ r ih =>
      exact ih (c+1) (foldTerms ops input t c 0 16 acc) (iteration ops input t c acc s)
        (iteration_trace_safe ops input t c acc s h)

theorem exitReturned_trace_safe (ops : Ops α) (t : Nat) (acc : α) (s : Machine α)
    (h : TraceSafe s.registers.base.trace) :
    TraceSafe (exitReturned ops t acc s).registers.base.trace := by
  intro access ha
  change access ∈ (⟨t, outputCell t, true, s.registers.base.epochs t⟩ :: s.registers.base.trace) at ha
  rcases List.mem_cons.mp ha with rfl | ha
  · rfl
  · exact h access ha

theorem afterLane_trace_safe (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α)
    (h : TraceSafe s.trace) : TraceSafe (afterLane ops input t s).trace := by
  have hi : TraceSafe (initialized ops t s).registers.base.trace := by
    rw [initialized_base]
    exact h
  exact exitReturned_trace_safe ops t _ _
    (runChunks_trace_safe ops input t 0 64 (ops.literal 0 1) (initialized ops t s) hi)

theorem runLanes_trace_safe (ops : Ops α) (input : Nat → Nat → α) (k r : Nat) (s : State α)
    (h : TraceSafe s.trace) : TraceSafe (runLanes ops input k r s).trace := by
  induction r generalizing k s with
  | zero => exact h
  | succ r ih => exact ih (k+1) (afterLane ops input k s) (afterLane_trace_safe ops input k s h)

theorem trace_safe_raceFree (g : Geometry) (trace : List Access) (h : TraceSafe trace) :
    raceFree g trace = true := by
  apply List.all_eq_true.mpr
  intro a ha
  apply List.all_eq_true.mpr
  intro b hb
  have hasafe := h a ha
  have hbsafe := h b hb
  by_cases he : a.thread = b.thread
  · simp [conflict, he]
  · cases haw : a.write <;> cases hbw : b.write <;>
      simp [AccessSafe, haw, hbw] at hasafe hbsafe
    · simp [conflict, haw, hbw]
    · have hn : a.location.buffer ≠ 2 := by have hi := hasafe.2.2; omega
      simp [conflict, sameLocation, hbsafe, haw, hbw, outputCell, hn]
    · have hn : (2 : Nat) ≠ b.location.buffer := by have hi := hbsafe.2.2; omega
      simp [conflict, sameLocation, hasafe, haw, hbw, outputCell, hn]
    · simp [conflict, sameLocation, hasafe, hbsafe, outputCell, haw, hbw, he]

theorem launch_raceFree (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) :
    raceFree geometry (finalState ops input outside).trace = true := by
  apply trace_safe_raceFree
  unfold finalState
  exact runLanes_trace_safe ops input 0 16384 (initial layout input outside)
    (by simp [TraceSafe, initial])

def referenceSpec (ops : Ops α) (input : Nat → Nat → α) : List α :=
  (List.range 16384).map (reference ops input)

def referenceTensor (ops : Ops α) (input : Nat → Nat → α) : LarkPtxFeedForward.Reference.Tensor α :=
  LarkPtxFeedForward.Reference.mapTensor ops.toHalf
    ((LarkPtxFeedForward.Reference.multiply ops
      (LarkPtxFeedForward.Reference.mapTensor ops.fromHalf
        (LarkPtxFeedForward.Reference.inputMatrix input 0 64 1024))
      (LarkPtxFeedForward.Reference.mapTensor ops.fromHalf
        (LarkPtxFeedForward.Reference.inputMatrix input 1 1024 256))).getD
      LarkPtxFeedForward.Reference.emptyTensor)

theorem independent_reference_cell (ops : Ops α) (input : Nat → Nat → α)
    (t : Nat) (ht : t < 16384) :
    (referenceTensor ops input).cell t = some (reference ops input t) := by
  have hr : t/256 < 64 := by omega
  have hc : t%256 < 256 := Nat.mod_lt _ (by decide)
  apply LarkPtxFeedForward.Reference.mapped_multiply_fold ops ops.toHalf
    (LarkPtxFeedForward.Reference.mapTensor ops.fromHalf
      (LarkPtxFeedForward.Reference.inputMatrix input 0 64 1024))
    (LarkPtxFeedForward.Reference.mapTensor ops.fromHalf
      (LarkPtxFeedForward.Reference.inputMatrix input 1 1024 256))
    t 1024 (by rfl) (by rfl) ht
    (fun j => ops.fromHalf (input 0 (t/256*1024+j)))
    (fun j => ops.fromHalf (input 1 (j*256+t%256)))
    (referenceTerm ops input t) (by rfl)
  · intro j hj
    have hb : t/256*1024+j < 64*1024 := by change j < 1024 at hj; omega
    simp [LarkPtxFeedForward.Reference.mapTensor, LarkPtxFeedForward.Reference.inputMatrix, hb]
  · intro j hj
    have hb : j*256+t%256 < 1024*256 := by change j < 1024 at hj; omega
    simp [LarkPtxFeedForward.Reference.mapTensor, LarkPtxFeedForward.Reference.inputMatrix, hb]

theorem extract_outputs (s : State α) (values : Nat → α)
    (h : ∀ i, i < 16384 → s.memory (outputCell i) = some (values i)) :
    extract layout s = some ((List.range 16384).map values) := by
  simp only [extract, layout, List.zipIdx_cons, List.zipIdx_nil, List.flatMap_cons,
    List.flatMap_nil, List.nil_append]
  simp only [List.map_cons, List.map_nil, show Role.input ≠ Role.output by decide,
    ↓reduceIte, List.nil_append, List.append_nil]
  change (((List.range 16384).map (fun i => (2, i))).mapM
    (fun bi => s.memory ⟨.global, 0, bi.1, bi.2⟩) : Option (List α)) = _
  rw [LarkPointwise.mapM_map]
  exact LarkPointwise.mapM_some (List.range 16384) _ _ (by
    intro i hi
    exact h i (List.mem_range.mp hi))

theorem final_extract (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) :
    extract layout (finalState ops input outside) = some (referenceSpec ops input) := by
  exact extract_outputs (finalState ops input outside) (reference ops input) (launch_outputs ops input outside)

def Correct (ops : Ops α) (p : List Instruction) (spec : (Nat → Nat → α) → List α) : Prop :=
  ∀ input outside, ∃ final,
    LaneSequence ops p 0 16384 (initial layout input outside) final ∧
    raceFree geometry final.trace = true ∧
    extract layout final = some (spec input) ∧
    (∀ l, (∀ i, i < 16384 → l ≠ outputCell i) → final.memory l = (initial layout input outside).memory l)

theorem kernel_correct (ops : Ops α) : Correct ops program (referenceSpec ops) := by
  intro input outside
  exact ⟨finalState ops input outside, launch_execution ops input outside,
    launch_raceFree ops input outside, final_extract ops input outside, launch_other_memory ops input outside⟩

end FfnDown

#print axioms FfnDown.referenceFold_scalarFold
#print axioms FfnDown.dotValue_reference
#print axioms FfnDown.independent_reference_cell
#print axioms FfnDown.launch_execution
#print axioms FfnDown.launch_outputs
#print axioms FfnDown.launch_other_memory
#print axioms FfnDown.launch_raceFree
#print axioms FfnDown.final_extract
#print axioms FfnDown.kernel_correct
end LarkPtxMatrix
