import Lark.NativeSoftmaxMaxFrame

/-! Compose the actual maximum prefix through the scheduler's sequential lane
fold, preserving earlier lanes and the original shared input memory. -/
namespace LarkNativeSoftmax
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def MaxNativeIndices (t : Nat) (s : State α) : Prop :=
  s.indices t 0 = some ((t/1024 : Nat) : Int) ∧
  s.indices t 1 = some ((t%1024 : Nat) : Int) ∧
  s.indices t 2 = some (((t%1024)/32 : Nat) : Int) ∧
  s.indices t 3 = some (((t%1024)%32 : Nat) : Int)

structure MaxLaneReady (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) : Prop where
  pc : s.pc t = 20
  accumulator : s.regs t 0 = some (threadMaximum ops input (t/1024) (t%1024))
  indices : MaxNativeIndices t s

theorem max_lane_ready (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t : Nat) (s : State α) (reads : Reads p input s) (good : ∀ a ∈ s.trace, Good a) :
    MaxLaneReady ops input t (maxPrefixState ops input t s) :=
  ⟨max_prefix_pc ops input t s,max_prefix_value p ops input t s reads good,max_prefix_native_indices ops input t s⟩

theorem max_lane_ready_other (ops : Ops α) (input : Nat → Nat → α)
    (t u : Nat) (s : State α) (hu : u ≠ t) (ready : MaxLaneReady ops input u s) :
    MaxLaneReady ops input u (maxPrefixState ops input t s) := by
  have h := max_prefix_other ops input t u s hu
  exact {
    pc := h.1.trans ready.pc
    accumulator := (congrFun h.2.2 0).trans ready.accumulator
    indices := by simpa only [MaxNativeIndices,h.2.1] using ready.indices }

def maxPrefixFold (ops : Ops α) (input : Nat → Nat → α) (ts : List Nat) (s : State α) : State α :=
  ts.foldl (fun s t => maxPrefixState ops input t s) s

theorem max_fold_frames (ops : Ops α) (input : Nat → Nat → α) (ts : List Nat) (s : State α) :
    (maxPrefixFold ops input ts s).memory = s.memory ∧
    (maxPrefixFold ops input ts s).epochs = s.epochs ∧
    (maxPrefixFold ops input ts s).trace.length = s.trace.length + 56*ts.length := by
  induction ts generalizing s with
  | nil => exact ⟨rfl,rfl,by simp [maxPrefixFold]⟩
  | cons t ts ih =>
    have head := max_prefix_frames ops input t s
    have tail := ih (maxPrefixState ops input t s)
    refine ⟨tail.1.trans head.1,tail.2.1.trans head.2.1,?_⟩
    change (maxPrefixFold ops input ts (maxPrefixState ops input t s)).trace.length = _
    rewrite [tail.2.2,head.2.2,List.length_cons]
    omega

theorem max_fold_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (ts : List Nat) (s : State α) (reads : Reads p input s) : Reads p input (maxPrefixFold ops input ts s) := by
  intro offset hb
  rewrite [(max_fold_frames ops input ts s).1]
  exact reads offset hb

theorem max_fold_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (ts : List Nat) (s : State α) (reads : Reads p input s) (good : ∀ a ∈ s.trace, Good a) :
    ∀ a ∈ (maxPrefixFold ops input ts s).trace, Good a := by
  induction ts generalizing s with
  | nil => exact good
  | cons t ts ih =>
    have headReads : Reads p input (maxPrefixState ops input t s) := by
      intro offset hb
      rewrite [(max_prefix_frames ops input t s).1]
      exact reads offset hb
    exact ih _ headReads (max_prefix_good p ops input t s reads good)

theorem max_fold_inputs (ops : Ops α) (input : Nat → Nat → α)
    (ts : List Nat) (s : State α) (old : ∀ a ∈ s.trace, MaxInputAccess a) :
    ∀ a ∈ (maxPrefixFold ops input ts s).trace, MaxInputAccess a := by
  induction ts generalizing s with
  | nil => exact old
  | cons t ts ih => exact ih _ (max_prefix_inputs ops input t s old)

theorem max_fold_ready_other (ops : Ops α) (input : Nat → Nat → α)
    (ts : List Nat) (t : Nat) (s : State α) (ht : t ∉ ts) (ready : MaxLaneReady ops input t s) :
    MaxLaneReady ops input t (maxPrefixFold ops input ts s) := by
  induction ts generalizing s with
  | nil => exact ready
  | cons a ts ih =>
    have hne : t ≠ a := by intro he; subst t; simp at ht
    have hn : t ∉ ts := by intro hm; exact ht (by simp [hm])
    exact ih _ hn (max_lane_ready_other ops input a t s hne ready)

theorem max_fold_run (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (ts : List Nat) (s : State α) (hn : ts.Nodup)
    (ht : ∀ t ∈ ts, t < p.rows*1024) (hp : ∀ t ∈ ts, s.pc t = 0)
    (reads : Reads p input s) (good : ∀ a ∈ s.trace, Good a) :
    ts.foldlM (fun s t => LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t fuel.lane s) s =
      some (maxPrefixFold ops input ts s) := by
  induction ts generalizing s with
  | nil => rfl
  | cons a ts ih =>
    obtain ⟨hnot,hnodup⟩ := List.nodup_cons.mp hn
    have hbound : ∀ t ∈ ts, t < p.rows*1024 := by intro t hm; exact ht t (by simp [hm])
    have hpc : ∀ t ∈ ts, (maxPrefixState ops input a s).pc t = 0 := by
      intro t hm
      have hne : t ≠ a := by intro he; subst t; exact hnot hm
      exact (max_prefix_other ops input a t s hne).1.trans (hp t (by simp [hm]))
    have headReads : Reads p input (maxPrefixState ops input a s) := by
      intro offset hb
      rewrite [(max_prefix_frames ops input a s).1]
      exact reads offset hb
    rewrite [List.foldlM_cons,max_prefix_run p guarded ops input a s (ht a (by simp)) (hp a (by simp)) reads good]
    simp only [bind,Option.some_bind]
    exact ih _ hnodup hbound hpc headReads (max_prefix_good p ops input a s reads good)

theorem max_fold_member (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (ts : List Nat) (s : State α) (hn : ts.Nodup)
    (reads : Reads p input s) (good : ∀ a ∈ s.trace, Good a) (t : Nat) (hm : t ∈ ts) :
    MaxLaneReady ops input t (maxPrefixFold ops input ts s) := by
  induction ts generalizing s with
  | nil => simp at hm
  | cons a ts ih =>
    obtain ⟨hnot,hnodup⟩ := List.nodup_cons.mp hn
    rcases List.mem_cons.mp hm with he | hm
    · subst t
      exact max_fold_ready_other ops input ts a _ hnot (max_lane_ready p ops input a s reads good)
    · have headReads : Reads p input (maxPrefixState ops input a s) := by
        intro offset hb
        rewrite [(max_prefix_frames ops input a s).1]
        exact reads offset hb
      exact ih _ hnodup headReads (max_prefix_good p ops input a s reads good) hm

#print axioms max_lane_ready
#print axioms max_lane_ready_other
#print axioms max_fold_frames
#print axioms max_fold_reads
#print axioms max_fold_good
#print axioms max_fold_inputs
#print axioms max_fold_ready_other
#print axioms max_fold_run
#print axioms max_fold_member
end LarkNativeSoftmax
