import Lark.PtxLinearExit

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/- Full original Linear launch, closed reference extraction, memory preservation
   and actual access-trace safety. Abstract scalar correspondence, parsing and
   aligned disjoint non-wrapping logical allocations retain their trust boundary.
   These theorems establish no IEEE, compiler or NVIDIA backend conformance. -/
namespace LarkPtxLinear.Linear.Launch
open LarkNonlinear LarkPtxPointwise
open LarkPtxDot
open LarkPtxMatrix
open LarkPtxLinear.Linear.Body LarkPtxLinear.Linear.Exit

def referenceTerm (ops : Ops α) (input : Nat → Nat → α) (t k : Nat) (acc : α) : α :=
  ops.add acc (ops.mul (ops.fromHalf (input 0 (t/512*256+k))) (ops.fromHalf (input 1 (k*512+t%512))))

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

def reference (ops : Ops α) (input : Nat → Nat → α) (t : Nat) : α :=
  ops.toHalf (ops.add (referenceFold ops input t 0 256 (ops.literal 0 1))
    (ops.fromHalf (input 2 (t%512))))

theorem laneValue_reference (ops : Ops α) (input : Nat → Nat → α) (t : Nat) :
    laneValue ops input t = reference ops input t := by
  unfold laneValue dotValue reference
  rw [foldChunks_reference]

inductive LaneSequence (ops : Ops α) (p : List LarkPtxLinear.Instruction) :
    Nat → Nat → State α → State α → Prop where
  | nil (k : Nat) (s : State α) : LaneSequence ops p k 0 s s
  | next {k r : Nat} {s final : State α} {m : Machine α} :
      LarkPtxLinear.Steps ops LarkPtxLinear.Linear.layout LarkPtxLinear.Linear.geometry k p (LarkPtxLinear.Linear.start s) m →
      m.registers.stopped = true →
      LaneSequence ops p (k+1) r m.registers.base final →
      LaneSequence ops p k (r+1) s final

theorem control_trace (c : Nat) (s : Machine α) :
    (controlResult c s).registers.base.trace = s.registers.base.trace := rfl

def AccessSafe (a : Access) : Prop :=
  if a.write then a.location = outputCell a.thread
  else a.location.space = .global ∧ a.location.owner = 0 ∧ a.location.buffer < 3

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

theorem exitReturned_trace_safe (ops : Ops α) (t : Nat) (acc bias : α) (s : Machine α)
    (h : TraceSafe s.registers.base.trace) :
    TraceSafe (exitReturned ops t acc bias s).registers.base.trace := by
  intro access ha
  change access ∈ (⟨t, outputCell t, true, s.registers.base.epochs t⟩ ::
    ⟨t, biasCell t, false, s.registers.base.epochs t⟩ :: s.registers.base.trace) at ha
  simp only [List.mem_cons] at ha
  rcases ha with rfl | rfl | ha
  · rfl
  · simp [AccessSafe, biasCell]
  · exact h access ha

theorem source_lane_safe (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (base : State α)
    (ht : t < 32768) (hinputs : Inputs input base) (hsafe : TraceSafe base.trace) :
    ∃ final, LarkPtxLinear.Steps ops LarkPtxLinear.Linear.layout LarkPtxLinear.Linear.geometry t LarkPtxLinear.Linear.program (LarkPtxLinear.Linear.start base) final ∧
      final.registers.stopped = true ∧ final.pc = 179 ∧
      final.registers.base.memory =
        (fun l => if l = outputCell t then some (reference ops input t) else base.memory l) ∧
      TraceSafe final.registers.base.trace := by
  obtain ⟨entry, first, ready⟩ := LarkPtxLinear.Linear.Init.prologue_ready ops t base ht
  have invariant := ready_loop ops input t base entry ready hinputs.1
  have loop := runChunks_execute ops input t 0 16 (ops.literal 0 1) entry ht (by decide) invariant
  let exited := runChunks ops input t 0 16 (ops.literal 0 1) entry
  have inv : LoopInvariant input t 16 (dotValue ops input t) exited := loop.2
  have memory : exited.registers.base.memory = base.memory := by
    rw [runChunks_memory, ready.frame.memory]
  have hbias : exited.registers.base.memory (biasCell t) = some (input 2 (t%512)) := by
    rw [memory]
    exact hinputs.2 (t%512) (Nat.mod_lt _ (by decide))
  have finish := epilogue_execute ops input t (dotValue ops input t) (input 2 (t%512)) exited ht inv hbias
  have entrySafe : TraceSafe entry.registers.base.trace := by
    rw [ready.frame.memory]
    exact hsafe
  have exitedSafe : TraceSafe exited.registers.base.trace :=
    runChunks_trace_safe ops input t 0 16 (ops.literal 0 1) entry entrySafe
  refine ⟨exitReturned ops t (dotValue ops input t) (input 2 (t%512)) exited,
    LarkPtxLinear.steps_trans _ _ _ _ _ _ _ _ first
      (LarkPtxLinear.steps_trans _ _ _ _ _ _ _ _ loop.1 finish),
    exitReturned_stopped _ _ _ _ _, ?_, ?_,
    exitReturned_trace_safe _ _ _ _ _ exitedSafe⟩
  · rw [exitReturned_pc, inv.pc]
    rfl
  · rw [exitReturned_memory, memory]
    change (fun l => if l = outputCell t then some (laneValue ops input t) else base.memory l) = _
    rw [laneValue_reference]

theorem lane_inputs (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (base : State α)
    (s : Machine α) (hinputs : Inputs input base)
    (memory : s.registers.base.memory =
      fun l => if l = outputCell t then some (reference ops input t) else base.memory l) :
    Inputs input s.registers.base := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro i hi
    change s.registers.base.memory ⟨.global, 0, 0, i⟩ = _
    rw [memory]
    simpa [outputCell] using hinputs.1.1 i hi
  · intro i hi
    change s.registers.base.memory ⟨.global, 0, 1, i⟩ = _
    rw [memory]
    simpa [outputCell] using hinputs.1.2 i hi
  · intro i hi
    change s.registers.base.memory ⟨.global, 0, 2, i⟩ = _
    rw [memory]
    simpa [outputCell] using hinputs.2 i hi

theorem launch_exists_safe (ops : Ops α) (input : Nat → Nat → α) (k r : Nat) (base : State α)
    (hcount : k+r ≤ 32768) (hreads : Inputs input base) (hsafe : TraceSafe base.trace) :
    ∃ final, LaneSequence ops LarkPtxLinear.Linear.program k r base final ∧ Inputs input final ∧ TraceSafe final.trace ∧
      (∀ i, final.memory (outputCell i) =
        if k ≤ i ∧ i < k+r then some (reference ops input i) else base.memory (outputCell i)) ∧
      (∀ l, (∀ i, k ≤ i → i < k+r → l ≠ outputCell i) → final.memory l = base.memory l) := by
  induction r generalizing k base with
  | zero =>
      refine ⟨base, .nil k base, hreads, hsafe, ?_, ?_⟩
      · intro i
        have hn : ¬ (k ≤ i ∧ i < k+0) := by omega
        simp only [if_neg hn]
      · intro l _
        rfl
  | succ r ih =>
      obtain ⟨lane, execution, stopped, pc, memory, laneSafe⟩ := source_lane_safe ops input k base (by omega) hreads hsafe
      have nextReads := lane_inputs ops input k base lane hreads memory
      obtain ⟨final, tail, finalReads, finalSafe, outputs, outside⟩ := ih (k+1) lane.registers.base (by omega) nextReads laneSafe
      refine ⟨final, .next execution stopped tail, finalReads, finalSafe, ?_, ?_⟩
      · intro i
        rw [outputs]
        by_cases hi : i = k
        · subst i
          have hrest : ¬ (k+1 ≤ k ∧ k < k+1+r) := by omega
          have hwhole : k ≤ k ∧ k < k+(r+1) := by omega
          rw [if_neg hrest, memory]
          simp [hwhole]
        · have hloc : outputCell i ≠ outputCell k := by
            intro he
            exact hi (congrArg Location.offset he)
          have hrange : (k+1 ≤ i ∧ i < k+1+r) ↔ (k ≤ i ∧ i < k+(r+1)) := by omega
          rw [memory]
          simp only [hloc, if_false, hrange]
      · intro l h
        have htail : ∀ i, k+1 ≤ i → i < k+1+r → l ≠ outputCell i := by
          intro i hi hj
          exact h i (by omega) (by omega)
        rw [outside l htail, memory]
        simp only [if_neg (h k (by omega) (by omega))]

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
    · have hn : a.location.buffer ≠ 3 := by have hi := hasafe.2.2; omega
      simp [conflict, sameLocation, hbsafe, haw, hbw, outputCell, hn]
    · have hn : (3 : Nat) ≠ b.location.buffer := by have hi := hbsafe.2.2; omega
      simp [conflict, sameLocation, hasafe, haw, hbw, outputCell, hn]
    · simp [conflict, sameLocation, hasafe, hbsafe, outputCell, haw, hbw, he]

def referenceSpec (ops : Ops α) (input : Nat → Nat → α) : List α :=
  (List.range 32768).map (reference ops input)

inductive TensorReference where
  | input : Nat → TensorReference
  | fromHalf : TensorReference → TensorReference
  | matmul : TensorReference → TensorReference → TensorReference
  | add : TensorReference → TensorReference → TensorReference
  | toHalf : TensorReference → TensorReference
  deriving DecidableEq, Repr

def referenceBody : TensorReference :=
  .toHalf (.add (.matmul (.fromHalf (.input 0)) (.fromHalf (.input 1))) (.fromHalf (.input 2)))

/-- Closed original matrix-plus-bias reference. Other ASTs refuse. The scalar
and reference formalization remain trusted; no IEEE/backend result is claimed. -/
def evaluateReference (ops : Ops α) (input : Nat → Nat → α) : TensorReference → Option (List α)
  | .toHalf (.add (.matmul (.fromHalf (.input 0)) (.fromHalf (.input 1))) (.fromHalf (.input 2))) =>
      some (referenceSpec ops input)
  | _ => none

theorem evaluate_reference_body (ops : Ops α) (input : Nat → Nat → α) :
    evaluateReference ops input referenceBody = some (referenceSpec ops input) := rfl

theorem extract_outputs_sized (aSize bSize biasSize n : Nat) (s : State α) (values : Nat → α)
    (h : ∀ i, i < n → s.memory (outputCell i) = some (values i)) :
    extract ⟨[⟨.input, aSize⟩, ⟨.input, bSize⟩, ⟨.input, biasSize⟩, ⟨.output, n⟩], [], []⟩ s =
      some ((List.range n).map values) := by
  simp only [extract, List.zipIdx_cons, List.zipIdx_nil, List.flatMap_cons,
    List.flatMap_nil, List.nil_append]
  simp only [List.map_cons, List.map_nil, show Role.input ≠ Role.output by decide,
    ↓reduceIte, List.nil_append, List.append_nil]
  change (((List.range n).map (fun i => (3, i))).mapM
    (fun bi => s.memory ⟨.global, 0, bi.1, bi.2⟩) : Option (List α)) = _
  rw [LarkPointwise.mapM_map]
  exact LarkPointwise.mapM_some (List.range n) _ _ (by
    intro i hi
    exact h i (List.mem_range.mp hi))

theorem extract_outputs (s : State α) (values : Nat → α)
    (h : ∀ i, i < 32768 → s.memory (outputCell i) = some (values i)) :
    extract LarkPtxLinear.Linear.layout s = some ((List.range 32768).map values) :=
  extract_outputs_sized (64*256) (256*512) 512 32768 s values h

def Correct (ops : Ops α) (p : List LarkPtxLinear.Instruction)
    (spec : (Nat → Nat → α) → List α) : Prop :=
  ∀ input outside, ∃ final,
    LaneSequence ops p 0 32768 (initial LarkPtxLinear.Linear.layout input outside) final ∧
    raceFree LarkPtxLinear.Linear.geometry final.trace = true ∧ extract LarkPtxLinear.Linear.layout final = some (spec input) ∧
    (∀ l, (∀ i, i < 32768 → l ≠ outputCell i) →
      final.memory l = (initial LarkPtxLinear.Linear.layout input outside).memory l)

theorem kernel_correct (ops : Ops α) : Correct ops LarkPtxLinear.Linear.program (referenceSpec ops) := by
  intro input outside
  have initialSafe : TraceSafe (initial LarkPtxLinear.Linear.layout input outside).trace := by
    simp [TraceSafe, initial]
  obtain ⟨final, execution, inputs, safe, outputs, preserved⟩ :=
    launch_exists_safe ops input 0 32768 (initial LarkPtxLinear.Linear.layout input outside)
      (by decide) (initial_inputs input outside) initialSafe
  have everyOutput : ∀ i, i < 32768 → final.memory (outputCell i) = some (reference ops input i) := by
    intro i hi
    simpa only [Nat.zero_le, true_and, Nat.zero_add, if_pos hi] using outputs i
  refine ⟨final, execution, trace_safe_raceFree LarkPtxLinear.Linear.geometry final.trace safe,
    extract_outputs final (reference ops input) everyOutput, ?_⟩
  intro l h
  apply preserved l
  intro i _ hi
  exact h i (by simpa using hi)

end LarkPtxLinear.Linear.Launch

#print axioms LarkPtxLinear.Linear.Launch.foldTerms_reference
#print axioms LarkPtxLinear.Linear.Launch.referenceFold_append
#print axioms LarkPtxLinear.Linear.Launch.foldChunks_reference
#print axioms LarkPtxLinear.Linear.Launch.laneValue_reference
#print axioms LarkPtxLinear.Linear.Launch.control_trace
#print axioms LarkPtxLinear.Linear.Launch.termResult_trace_safe
#print axioms LarkPtxLinear.Linear.Launch.runTerms_trace_safe
#print axioms LarkPtxLinear.Linear.Launch.iteration_trace_safe
#print axioms LarkPtxLinear.Linear.Launch.runChunks_trace_safe
#print axioms LarkPtxLinear.Linear.Launch.exitReturned_trace_safe
#print axioms LarkPtxLinear.Linear.Launch.source_lane_safe
#print axioms LarkPtxLinear.Linear.Launch.lane_inputs
#print axioms LarkPtxLinear.Linear.Launch.launch_exists_safe
#print axioms LarkPtxLinear.Linear.Launch.trace_safe_raceFree
#print axioms LarkPtxLinear.Linear.Launch.evaluate_reference_body
#print axioms LarkPtxLinear.Linear.Launch.extract_outputs_sized
#print axioms LarkPtxLinear.Linear.Launch.extract_outputs
#print axioms LarkPtxLinear.Linear.Launch.kernel_correct
