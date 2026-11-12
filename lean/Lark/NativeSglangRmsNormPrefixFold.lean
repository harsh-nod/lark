import Lark.NativeSglangRmsNormIndices

/-! Actual sequential native preparation, with private caches and prior trace
carried through every thread. No premise classifies the prior trace. -/
namespace LarkNativeSglangRmsNorm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

structure PrefixReady (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) : Prop
    extends PrefixData p ops input t s where
  indices : NativeIndices t s

theorem carried_prefix_ready (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t : Nat) (s : State α) (reads : Reads p input s) :
    PrefixReady p ops input t (prefixState ops input t s) :=
  ⟨carried_prefix_data p ops input t s reads,prefix_native_indices ops input t s⟩

theorem prefix_ready_other (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t u : Nat) (s : State α) (hu : u ≠ t) (ready : PrefixReady p ops input u s) :
    PrefixReady p ops input u (prefixState ops input t s) :=
  ⟨prefix_data_other p ops input t u s hu ready.toPrefixData,
    prefix_native_other ops input t u s hu ready.indices⟩

def prefixFold (ops : Ops α) (input : Nat → Nat → α) (ts : List Nat) (s : State α) : State α :=
  ts.foldl (fun s t => prefixState ops input t s) s

theorem prefix_fold_other (ops : Ops α) (input : Nat → Nat → α)
    (ts : List Nat) (t : Nat) (s : State α) (ht : t ∉ ts) :
    (prefixFold ops input ts s).pc t = s.pc t ∧
    (prefixFold ops input ts s).indices t = s.indices t ∧
    (prefixFold ops input ts s).regs t = s.regs t := by
  induction ts generalizing s with
  | nil => exact ⟨rfl,rfl,rfl⟩
  | cons a ts ih =>
      have hne : t ≠ a := by intro he; subst t; simp at ht
      have hn : t ∉ ts := by intro hm; exact ht (by simp [hm])
      have f := prefix_frame ops input a s
      have h := ih (prefixState ops input a s) hn
      exact ⟨h.1.trans (f.pc t hne),h.2.1.trans (f.indices t hne),h.2.2.trans (f.regs t hne)⟩

theorem prefix_fold_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (ts : List Nat) (s : State α) (reads : Reads p input s) :
    Reads p input (prefixFold ops input ts s) := by
  induction ts generalizing s with
  | nil => exact reads
  | cons a ts ih => exact ih (prefixState ops input a s) (prefix_reads_frame p ops input a s reads)

theorem prefix_fold_ready_other (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (ts : List Nat) (t : Nat) (s : State α) (ht : t ∉ ts) (ready : PrefixReady p ops input t s) :
    PrefixReady p ops input t (prefixFold ops input ts s) := by
  induction ts generalizing s with
  | nil => exact ready
  | cons a ts ih =>
      have hne : t ≠ a := by intro he; subst t; simp at ht
      have hn : t ∉ ts := by intro hm; exact ht (by simp [hm])
      exact ih (prefixState ops input a s) hn (prefix_ready_other p ops input a t s hne ready)

theorem prefix_fold_epochs (ops : Ops α) (input : Nat → Nat → α) (ts : List Nat) (s : State α) :
    (prefixFold ops input ts s).epochs = s.epochs := by
  induction ts generalizing s with
  | nil => rfl
  | cons a ts ih => exact (ih (prefixState ops input a s)).trans (prefix_epochs ops input a s)

theorem prefix_fold_memory (ops : Ops α) (input : Nat → Nat → α)
    (ts : List Nat) (s : State α) (l : Location) (outside : ∀ t ∈ ts, OutsidePrivate t l) :
    (prefixFold ops input ts s).memory l = s.memory l := by
  induction ts generalizing s with
  | nil => rfl
  | cons a ts ih =>
      have h := ih (prefixState ops input a s) (by intro t ht; exact outside t (by simp [ht]))
      exact h.trans ((prefix_frame ops input a s).memory l (outside a (by simp)))

theorem prefix_fold_trace_length (ops : Ops α) (input : Nat → Nat → α) (ts : List Nat) (s : State α) :
    (prefixFold ops input ts s).trace.length = s.trace.length + 80 * ts.length := by
  induction ts generalizing s with
  | nil => simp [prefixFold]
  | cons a ts ih =>
      change (prefixFold ops input ts (prefixState ops input a s)).trace.length = _
      rewrite [ih,prefix_trace_length,List.length_cons]
      omega

theorem prefix_fold_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (ts : List Nat) (s : State α) (reads : Reads p input s) (good : ∀ a ∈ s.trace, Good a) :
    ∀ a ∈ (prefixFold ops input ts s).trace, Good a := by
  induction ts generalizing s with
  | nil => exact good
  | cons a ts ih =>
      exact ih (prefixState ops input a s) (prefix_reads_frame p ops input a s reads)
        (general_prefix_ready p ops input a s reads good).good

theorem prefix_fold_run (p : Shape) (repaired : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (ts : List Nat) (s : State α) (hn : ts.Nodup)
    (ht : ∀ t ∈ ts, t < p.rows * 1024) (hp : ∀ t ∈ ts, s.pc t = 0) (reads : Reads p input s) :
    ts.foldlM (fun s t => LarkCollective.runLane ops (layout p) (geometry p) (program repaired) t fuel.lane s) s =
      some (prefixFold ops input ts s) := by
  induction ts generalizing s with
  | nil => rfl
  | cons a ts ih =>
      obtain ⟨hnot,hnodup⟩ := List.nodup_cons.mp hn
      have hbound : ∀ t ∈ ts, t < p.rows * 1024 := by intro t hm; exact ht t (by simp [hm])
      have hpc : ∀ t ∈ ts, (prefixState ops input a s).pc t = 0 := by
        intro t hm
        have hne : t ≠ a := by intro he; subst t; exact hnot hm
        exact ((prefix_frame ops input a s).pc t hne).trans (hp t (by simp [hm]))
      rewrite [List.foldlM_cons,
        carried_prefix_run p repaired ops input a s (ht a (by simp)) (hp a (by simp)) reads]
      simp only [bind,Option.some_bind]
      exact ih (prefixState ops input a s) hnodup hbound hpc (prefix_reads_frame p ops input a s reads)

theorem prefix_fold_member (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (ts : List Nat) (s : State α) (hn : ts.Nodup) (reads : Reads p input s) (t : Nat) (hm : t ∈ ts) :
    PrefixReady p ops input t (prefixFold ops input ts s) := by
  induction ts generalizing s with
  | nil => simp at hm
  | cons a ts ih =>
      obtain ⟨hnot,hnodup⟩ := List.nodup_cons.mp hn
      rcases List.mem_cons.mp hm with he | hmem
      · subst t
        exact prefix_fold_ready_other p ops input ts a (prefixState ops input a s) hnot
          (carried_prefix_ready p ops input a s reads)
      · exact ih (prefixState ops input a s) hnodup (prefix_reads_frame p ops input a s reads) hmem

theorem initial_prefix_fold_run (p : Shape) (repaired : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (ts : List Nat) (hn : ts.Nodup)
    (ht : ∀ t ∈ ts, t < p.rows * 1024) :
    ts.foldlM (fun s t => LarkCollective.runLane ops (layout p) (geometry p) (program repaired) t fuel.lane s)
      (initial p input outside) = some (prefixFold ops input ts (initial p input outside)) :=
  prefix_fold_run p repaired ops input ts _ hn ht (by intro t hm; rfl) (initial_reads p input outside)

theorem initial_prefix_fold_member (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (ts : List Nat) (hn : ts.Nodup) (t : Nat) (hm : t ∈ ts) :
    PrefixReady p ops input t (prefixFold ops input ts (initial p input outside)) :=
  prefix_fold_member p ops input ts _ hn (initial_reads p input outside) t hm

theorem initial_prefix_fold_race_free (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (ts : List Nat) :
    raceFree (geometry p) (prefixFold ops input ts (initial p input outside)).trace = true :=
  race_free p _ (prefix_fold_good p ops input ts _ (initial_reads p input outside) (by intro a ha; cases ha))

#print axioms carried_prefix_ready
#print axioms prefix_ready_other
#print axioms prefix_fold_other
#print axioms prefix_fold_reads
#print axioms prefix_fold_ready_other
#print axioms prefix_fold_epochs
#print axioms prefix_fold_memory
#print axioms prefix_fold_trace_length
#print axioms prefix_fold_good
#print axioms prefix_fold_run
#print axioms prefix_fold_member
#print axioms initial_prefix_fold_run
#print axioms initial_prefix_fold_member
#print axioms initial_prefix_fold_race_free
end LarkNativeSglangRmsNorm
