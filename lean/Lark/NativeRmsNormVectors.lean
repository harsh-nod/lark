import Lark.NativeRmsNormAccumulate

/-! Actual two-vector traversal before the first native shuffle.
This module preserves the native vector ownership, source loop and scalar order.
-/
namespace LarkNativeRmsNorm
open LarkNonlinear
open LarkReduction (setIndex int32_cast execute_index_of)
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def vectorBegin (t : Nat) (s : State α) : State α := setIndex (advance s t 9) t 6 0 10
def vectorTail (t vector : Nat) (s : State α) : State α :=
  advance (setIndex s t 5 ((vector + 1024 : Nat) : Int) 17) t 8

theorem vector_begin_eq (p : Shape) (ops : Ops α) (t vector extra : Nat) (s : State α)
    (hi : s.indices t 5 = some (vector : Int)) (hv : vector < 2048) (hp : s.pc t = 8) :
    LarkCollective.runLane ops (layout p) (geometry p) program t (extra + 2) s =
      LarkCollective.runLane ops (layout p) (geometry p) program t extra (vectorBegin t s) := by
  let s1 := advance s t 9
  have hg := LarkReduction.predicate_lt_of (geometry p) t s (.ivar 5) (.const 2048)
    (vector : Int) 2048 hi (int32_cast 2048 (by decide)) (by omega)
  have h1 : execute ops (layout p) (geometry p) t
      (.branch (.lt (.ivar 5) (.const 2048)) 18) s = some s1 := by
    simp only [execute, hg, hp, bind, pure, Option.bind]
    rfl
  have h2 := execute_index_of ops (layout p) (geometry p) t 6 10 (.const 0) s1 0
    (by rfl) (by simp [s1, advance])
  change execute _ _ _ _ _ s1 = some (vectorBegin t s) at h2
  rewrite [scalar_step ops _ _ _ _ _ _ _ _
    (by simp [LarkCollective.parked, program, hp]) (by simp [program, hp]) h1]
  rewrite [scalar_step ops _ _ _ _ _ _ _ _
    (by simp [LarkCollective.parked, program, s1, advance]) (by simp [program, s1, advance]) h2]
  rfl

theorem vector_tail_eq (p : Shape) (ops : Ops α) (t vector extra : Nat) (s : State α)
    (hi : s.indices t 5 = some (vector : Int)) (hv : vector < 2048) (hp : s.pc t = 16) :
    LarkCollective.runLane ops (layout p) (geometry p) program t (extra + 2) s =
      LarkCollective.runLane ops (layout p) (geometry p) program t extra (vectorTail t vector s) := by
  let s1 := setIndex s t 5 ((vector + 1024 : Nat) : Int) 17
  have he := LarkReduction.eval_add_of (geometry p) t s (.ivar 5) (.const 1024)
    (vector : Int) 1024 ((vector + 1024 : Nat) : Int) hi (int32_cast 1024 (by decide))
    ((congrArg int32 (Int.natCast_add vector 1024).symm).trans (int32_cast _ (by omega)))
  have h1 := execute_index_of ops (layout p) (geometry p) t 5 17
    (.add (.ivar 5) (.const 1024)) s ((vector + 1024 : Nat) : Int) he (by omega)
  change execute _ _ _ _ _ s = some s1 at h1
  have h2 : execute ops (layout p) (geometry p) t (.jump 8) s1 = some (vectorTail t vector s) := rfl
  rewrite [scalar_step ops _ _ _ _ _ _ _ _
    (by simp [LarkCollective.parked, program, hp]) (by simp [program, hp]) h1]
  rewrite [scalar_step ops _ _ _ _ _ _ _ _
    (by simp [LarkCollective.parked, program, s1, setIndex, advance])
    (by simp [program, s1, setIndex, advance]) h2]
  rfl

def vectorAfter (ops : Ops α) (input : Nat → Nat → α) (row vector t : Nat)
    (acc : α) (s : State α) : State α :=
  vectorTail t vector (componentsRun ops input row vector t 0 8 acc (vectorBegin t s))

theorem vector_cycle (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row vector t extra : Nat) (acc : α) (s : State α)
    (reads : Reads p input s) (hr : row < p.rows) (hv : vector < 2048)
    (hi0 : s.indices t 0 = some (row : Int)) (hi5 : s.indices t 5 = some (vector : Int))
    (ha : s.regs t 0 = some acc) (hp : s.pc t = 8) :
    LarkCollective.runLane ops (layout p) (geometry p) program t (extra + 53) s =
      LarkCollective.runLane ops (layout p) (geometry p) program t extra
        (vectorAfter ops input row vector t acc s) := by
  rewrite [show extra + 53 = (extra + 51) + 2 by omega,
    vector_begin_eq p ops t vector (extra + 51) s hi5 hv hp]
  have hinner := components_run_eq p ops input row vector 0 8 t (extra + 2) acc (vectorBegin t s)
    (by decide) reads hr hv
    (by simpa [vectorBegin, setIndex, advance] using hi0)
    (by simpa [vectorBegin, setIndex, advance] using hi5)
    (by simp [vectorBegin, setIndex, advance]) ha (by simp [vectorBegin, setIndex, advance])
  have hf : extra + 51 = (extra + 2) + 6 * 8 + 1 := by omega
  rewrite [hf, hinner]
  have hv' : (componentsRun ops input row vector t 0 8 acc (vectorBegin t s)).indices t 5 =
      some (vector : Int) := by
    rewrite [components_index_other ops input row vector t 0 8 5 acc _ (by decide)]
    simpa [vectorBegin, setIndex, advance] using hi5
  exact vector_tail_eq p ops t vector extra _ hv' hv (components_pc ops input row vector t 0 8 acc _)

theorem vector_preserves (ops : Ops α) (input : Nat → Nat → α)
    (row vector t : Nat) (acc : α) (s : State α) :
    (vectorAfter ops input row vector t acc s).memory = s.memory ∧
    (vectorAfter ops input row vector t acc s).epochs = s.epochs :=
  components_preserves ops input row vector t 0 8 acc (vectorBegin t s)

theorem vector_fields (ops : Ops α) (input : Nat → Nat → α)
    (row vector t : Nat) (acc : α) (s : State α) (ha : s.regs t 0 = some acc) :
    (vectorAfter ops input row vector t acc s).pc t = 8 ∧
    (vectorAfter ops input row vector t acc s).indices t 5 = some ((vector + 1024 : Nat) : Int) ∧
    (vectorAfter ops input row vector t acc s).regs t 0 = some (componentFold ops input row vector 0 8 acc) := by
  refine ⟨by simp [vectorAfter, vectorTail, advance], by simp [vectorAfter, vectorTail, setIndex, advance], ?_⟩
  exact components_acc ops input row vector t 0 8 acc (vectorBegin t s) ha

theorem vector_index_other (ops : Ops α) (input : Nat → Nat → α)
    (row vector t reg : Nat) (acc : α) (s : State α) (h5 : reg ≠ 5) (h6 : reg ≠ 6) :
    (vectorAfter ops input row vector t acc s).indices t reg = s.indices t reg := by
  have h := components_index_other ops input row vector t 0 8 reg acc (vectorBegin t s) h6
  simpa [vectorAfter, vectorTail, vectorBegin, setIndex, advance, h5, h6] using h

theorem vector_other (ops : Ops α) (input : Nat → Nat → α)
    (row vector t u : Nat) (acc : α) (s : State α) (hu : u ≠ t) :
    (vectorAfter ops input row vector t acc s).pc u = s.pc u ∧
    (vectorAfter ops input row vector t acc s).indices u = s.indices u ∧
    (vectorAfter ops input row vector t acc s).regs u = s.regs u := by
  have h := components_other ops input row vector t 0 8 u acc (vectorBegin t s) hu
  simpa [vectorAfter, vectorTail, vectorBegin, setIndex, advance, hu] using h

theorem vector_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row vector t : Nat) (acc : α) (s : State α)
    (good : ∀ a ∈ s.trace, LarkReductionFootprint.Good (traversal p) 0 a) :
    ∀ a ∈ (vectorAfter ops input row vector t acc s).trace,
      LarkReductionFootprint.Good (traversal p) 0 a :=
  components_good p ops input row vector t 0 8 acc (vectorBegin t s) good

theorem vector_exit (p : Shape) (ops : Ops α) (t vector extra : Nat) (s : State α)
    (hi : s.indices t 5 = some (vector : Int)) (hv : 2048 ≤ vector) (hp : s.pc t = 8) :
    LarkCollective.runLane ops (layout p) (geometry p) program t (extra + 1) s =
      LarkCollective.runLane ops (layout p) (geometry p) program t extra (advance s t 18) := by
  have hg := LarkReduction.predicate_nlt_of (geometry p) t s (.ivar 5) (.const 2048)
    (vector : Int) 2048 hi (int32_cast 2048 (by decide)) (by omega)
  have he : execute ops (layout p) (geometry p) t
      (.branch (.lt (.ivar 5) (.const 2048)) 18) s = some (advance s t 18) := by
    simp only [execute, hg, bind, pure, Option.bind]
    rfl
  exact scalar_step ops _ _ _ _ _ _ _ _
    (by simp [LarkCollective.parked, program, hp]) (by simp [program, hp]) he

def twoVectorsValue (ops : Ops α) (input : Nat → Nat → α) (row tid : Nat) (acc : α) : α :=
  componentFold ops input row (tid + 1024) 0 8 (componentFold ops input row tid 0 8 acc)

def twoVectorsRun (ops : Ops α) (input : Nat → Nat → α) (row tid t : Nat)
    (acc : α) (s : State α) : State α :=
  let first := vectorAfter ops input row tid t acc s
  let second := vectorAfter ops input row (tid + 1024) t (componentFold ops input row tid 0 8 acc) first
  advance second t 18

theorem two_vectors_eq (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid t extra : Nat) (acc : α) (s : State α)
    (reads : Reads p input s) (hr : row < p.rows) (htid : tid < 1024)
    (hi0 : s.indices t 0 = some (row : Int)) (hi5 : s.indices t 5 = some (tid : Int))
    (ha : s.regs t 0 = some acc) (hp : s.pc t = 8) :
    LarkCollective.runLane ops (layout p) (geometry p) program t (extra + 107) s =
      LarkCollective.runLane ops (layout p) (geometry p) program t extra
        (twoVectorsRun ops input row tid t acc s) := by
  let first := vectorAfter ops input row tid t acc s
  let a1 := componentFold ops input row tid 0 8 acc
  let second := vectorAfter ops input row (tid + 1024) t a1 first
  have hfirst := vector_fields ops input row tid t acc s ha
  have hread1 := reads_of_memory p input s first reads (vector_preserves ops input row tid t acc s).1
  have hr1 : first.indices t 0 = some (row : Int) :=
    (vector_index_other ops input row tid t 0 acc s (by decide) (by decide)).trans hi0
  rewrite [show extra + 107 = (extra + 54) + 53 by omega,
    vector_cycle p ops input row tid t (extra + 54) acc s reads hr (by omega) hi0 hi5 ha hp]
  rewrite [show extra + 54 = (extra + 1) + 53 by omega,
    vector_cycle p ops input row (tid + 1024) t (extra + 1) a1 first
      hread1 hr (by omega) hr1 hfirst.2.1 hfirst.2.2 hfirst.1]
  have hsecond := vector_fields ops input row (tid + 1024) t a1 first hfirst.2.2
  exact vector_exit p ops t ((tid + 1024) + 1024) extra second hsecond.2.1 (by omega) hsecond.1

theorem two_vectors_preserves (ops : Ops α) (input : Nat → Nat → α)
    (row tid t : Nat) (acc : α) (s : State α) :
    (twoVectorsRun ops input row tid t acc s).memory = s.memory ∧
    (twoVectorsRun ops input row tid t acc s).epochs = s.epochs := by
  have h1 := vector_preserves ops input row tid t acc s
  have h2 := vector_preserves ops input row (tid + 1024) t (componentFold ops input row tid 0 8 acc)
    (vectorAfter ops input row tid t acc s)
  exact ⟨h2.1.trans h1.1, h2.2.trans h1.2⟩

theorem vector_acc_direct (ops : Ops α) (input : Nat → Nat → α)
    (row vector t : Nat) (acc : α) (s : State α) (ha : s.regs t 0 = some acc) :
    (vectorAfter ops input row vector t acc s).regs t 0 = some (componentFold ops input row vector 0 8 acc) :=
  components_acc ops input row vector t 0 8 acc (vectorBegin t s) ha

/-- Compose register-value facts through arbitrary state transformers, keeping
the intermediate state abstract during kernel checking. -/
theorem composed_acc (f g : State α → State α) (s : State α) (t next : Nat) (a1 a2 : α)
    (hf : (f s).regs t 0 = some a1)
    (hg : ∀ u, u.regs t 0 = some a1 → (g u).regs t 0 = some a2) :
    (advance (g (f s)) t next).regs t 0 = some a2 := hg (f s) hf

theorem two_vectors_acc (ops : Ops α) (input : Nat → Nat → α)
    (row tid t : Nat) (acc : α) (s : State α) (ha : s.regs t 0 = some acc) :
    (twoVectorsRun ops input row tid t acc s).regs t 0 = some (twoVectorsValue ops input row tid acc) := by
  let a1 := componentFold ops input row tid 0 8 acc
  exact composed_acc (fun u => vectorAfter ops input row tid t acc u)
    (fun u => vectorAfter ops input row (tid + 1024) t a1 u) s t 18 a1
    (componentFold ops input row (tid + 1024) 0 8 a1)
    (vector_acc_direct ops input row tid t acc s ha)
    (fun u hu => vector_acc_direct ops input row (tid + 1024) t a1 u hu)

theorem two_vectors_index_other (ops : Ops α) (input : Nat → Nat → α)
    (row tid t reg : Nat) (acc : α) (s : State α) (h5 : reg ≠ 5) (h6 : reg ≠ 6) :
    (twoVectorsRun ops input row tid t acc s).indices t reg = s.indices t reg := by
  have h1 := vector_index_other ops input row tid t reg acc s h5 h6
  have h2 := vector_index_other ops input row (tid + 1024) t reg (componentFold ops input row tid 0 8 acc)
    (vectorAfter ops input row tid t acc s) h5 h6
  exact h2.trans h1

theorem composed_other (f g : State α → State α) (s : State α) (t next u : Nat) (hu : u ≠ t)
    (hf : ∀ v, (f v).pc u = v.pc u ∧ (f v).indices u = v.indices u ∧ (f v).regs u = v.regs u)
    (hg : ∀ v, (g v).pc u = v.pc u ∧ (g v).indices u = v.indices u ∧ (g v).regs u = v.regs u) :
    (advance (g (f s)) t next).pc u = s.pc u ∧
    (advance (g (f s)) t next).indices u = s.indices u ∧
    (advance (g (f s)) t next).regs u = s.regs u := by
  have h1 := hf s
  have h2 := hg (f s)
  refine ⟨?_, h2.2.1.trans h1.2.1, h2.2.2.trans h1.2.2⟩
  change (if u = t then next else (g (f s)).pc u) = s.pc u
  rewrite [if_neg hu]
  exact h2.1.trans h1.1

theorem composed_trace (f g : State α → State α) (s : State α) (t next : Nat) (P : List Access → Prop)
    (hs : P s.trace) (hf : ∀ v, P v.trace → P (f v).trace)
    (hg : ∀ v, P v.trace → P (g v).trace) : P (advance (g (f s)) t next).trace := hg (f s) (hf s hs)

theorem two_vectors_other (ops : Ops α) (input : Nat → Nat → α)
    (row tid t u : Nat) (acc : α) (s : State α) (hu : u ≠ t) :
    (twoVectorsRun ops input row tid t acc s).pc u = s.pc u ∧
    (twoVectorsRun ops input row tid t acc s).indices u = s.indices u ∧
    (twoVectorsRun ops input row tid t acc s).regs u = s.regs u := by
  let a1 := componentFold ops input row tid 0 8 acc
  exact composed_other (fun v => vectorAfter ops input row tid t acc v)
    (fun v => vectorAfter ops input row (tid + 1024) t a1 v) s t 18 u hu
    (fun v => vector_other ops input row tid t u acc v hu)
    (fun v => vector_other ops input row (tid + 1024) t u a1 v hu)

theorem two_vectors_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid t : Nat) (acc : α) (s : State α)
    (good : ∀ a ∈ s.trace, LarkReductionFootprint.Good (traversal p) 0 a) :
    ∀ a ∈ (twoVectorsRun ops input row tid t acc s).trace,
      LarkReductionFootprint.Good (traversal p) 0 a := by
  let a1 := componentFold ops input row tid 0 8 acc
  exact composed_trace (fun v => vectorAfter ops input row tid t acc v)
    (fun v => vectorAfter ops input row (tid + 1024) t a1 v) s t 18
    (fun trace => ∀ a ∈ trace, LarkReductionFootprint.Good (traversal p) 0 a) good
    (fun v hv => vector_good p ops input row tid t acc v hv)
    (fun v hv => vector_good p ops input row (tid + 1024) t a1 v hv)

/-- Equality of the ordered folds; it uses no reassociation law for scalar addition. -/
theorem two_vectors_sum (ops : Ops α) (input : Nat → Nat → α) (row tid : Nat) :
    twoVectorsValue ops input row tid (ops.literal 0 1) = threadSum ops input row tid := by
  unfold twoVectorsValue threadSum threadCells
  have htwo : List.range 2 = [0, 1] := by decide
  simp only [htwo, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    Nat.zero_mul, Nat.add_zero, Nat.one_mul, List.foldl_append, List.foldl_map]
  rewrite [componentFold_foldl, componentFold_foldl]
  simp only [← List.range_eq_range', termAt_square]

#print axioms vector_cycle
#print axioms two_vectors_eq
#print axioms two_vectors_sum
#print axioms two_vectors_good
end LarkNativeRmsNorm
