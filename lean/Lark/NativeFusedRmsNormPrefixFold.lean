import Lark.NativeFusedRmsNormFrame

/-! Compose the actual mutable prefix through the scheduler's sequential lane
fold. Earlier stores are retained; unread and completed cells of other lanes are
framed, rather than restoring a read-only initial memory between lane calls.
-/
namespace LarkNativeFusedRmsNorm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def NativeIndices (t : Nat) (s : State α) : Prop :=
  s.indices t 0 = some ((t / 1024 : Nat) : Int) ∧
  s.indices t 1 = some ((t % 1024 : Nat) : Int) ∧
  s.indices t 2 = some (((t % 1024) % 32 : Nat) : Int) ∧
  s.indices t 3 = some (((t % 1024) / 32 : Nat) : Int)

theorem prefix_index_initial (ops : Ops α) (input : Nat → Nat → α)
    (t q : Nat) (s : State α) (hq : q < 4) :
    (prefixState ops input t s).indices t q = (initialized ops t s).indices t q := by
  have h1 := round_index_frame ops input (t / 1024) (t % 1024) 0 t q (ops.literal 0 1)
    (initialized ops t s) (by omega) (by omega) (by omega) (by omega)
  have h2 := round_index_frame ops input (t / 1024) (t % 1024) 1 t q
    (folded ops input (t / 1024) (t % 1024) 0 0 8 (ops.literal 0 1))
    (roundAfter ops input (t / 1024) (t % 1024) 0 t (ops.literal 0 1) (initialized ops t s))
    (by omega) (by omega) (by omega) (by omega)
  exact h2.trans h1

theorem prefix_indices (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) :
    NativeIndices t (prefixState ops input t s) := by
  simp only [NativeIndices,
    prefix_index_initial ops input t 0 s (by decide), prefix_index_initial ops input t 1 s (by decide),
    prefix_index_initial ops input t 2 s (by decide), prefix_index_initial ops input t 3 s (by decide)]
  simp [initialized, indexedAt, LarkReduction.setIndex, LarkReduction.setReg, advance]

structure PrefixReady (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) : Prop where
  pc : s.pc t = 23
  accumulator : s.regs t 0 = some (threadSum ops input (t / 1024) (t % 1024))
  indices : NativeIndices t s
  pending : Pending input (t / 1024) (t % 1024) 16 s
  completed : Completed ops input (t / 1024) (t % 1024) t 16 s

theorem prefix_ready (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t : Nat) (s : State α) (ht : t < p.rows * 1024)
    (pending : Pending input (t / 1024) (t % 1024) 0 s) (good : ∀ a ∈ s.trace, Good a) :
    PrefixReady ops input t (prefixState ops input t s) := by
  have values := prefix_values p ops input t s ht pending good
  exact ⟨prefix_pc ops input t s, values.1, prefix_indices ops input t s, values.2.1, values.2.2⟩

theorem prefix_ready_other (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t u : Nat) (s : State α) (hu : u ≠ t) (ready : PrefixReady ops input u s) :
    PrefixReady ops input u (prefixState ops input t s) := by
  have h := prefix_other ops input t u s hu
  exact {
    pc := h.1.trans ready.pc
    accumulator := (congrFun h.2.2 0).trans ready.accumulator
    indices := by simpa only [NativeIndices, h.2.1] using ready.indices
    pending := prefix_pending_other p ops input t u 16 s hu ready.pending
    completed := prefix_completed_other p ops input t u 16 s hu (by decide) ready.completed }

def prefixFold (ops : Ops α) (input : Nat → Nat → α) (ts : List Nat) (s : State α) : State α :=
  ts.foldl (fun s t => prefixState ops input t s) s

theorem prefix_fold_other (ops : Ops α) (input : Nat → Nat → α)
    (ts : List Nat) (t : Nat) (s : State α) (ht : t ∉ ts) :
    (prefixFold ops input ts s).pc t = s.pc t ∧
    (prefixFold ops input ts s).indices t = s.indices t ∧
    (prefixFold ops input ts s).regs t = s.regs t := by
  induction ts generalizing s with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons a ts ih =>
      have hne : t ≠ a := by intro he; subst t; simp at ht
      have hn : t ∉ ts := by intro hm; exact ht (by simp [hm])
      have h := ih (prefixState ops input a s) hn
      have h1 := prefix_other ops input a t s hne
      exact ⟨h.1.trans h1.1, h.2.1.trans h1.2.1, h.2.2.trans h1.2.2⟩

theorem prefix_fold_ready_other (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (ts : List Nat) (t : Nat) (s : State α) (ht : t ∉ ts) (ready : PrefixReady ops input t s) :
    PrefixReady ops input t (prefixFold ops input ts s) := by
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

theorem prefix_fold_frame (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (ts : List Nat) (s : State α) (l : Location) (hl : ∀ t ∈ ts, ¬ Owns t l) :
    (prefixFold ops input ts s).memory l = s.memory l := by
  induction ts generalizing s with
  | nil => rfl
  | cons a ts ih =>
      exact (ih (prefixState ops input a s) (by intro t ht; exact hl t (by simp [ht]))).trans
        (prefix_frame p ops input a s l (hl a (by simp)))

theorem prefix_fold_trace_length (ops : Ops α) (input : Nat → Nat → α) (ts : List Nat) (s : State α) :
    (prefixFold ops input ts s).trace.length = s.trace.length + 64 * ts.length := by
  induction ts generalizing s with
  | nil => simp [prefixFold]
  | cons a ts ih =>
      change (prefixFold ops input ts (prefixState ops input a s)).trace.length = _
      rewrite [ih, prefix_trace_length, List.length_cons]
      omega

theorem prefix_fold_pending_tail (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (a : Nat) (ts : List Nat) (s : State α) (hn : a ∉ ts)
    (pending : ∀ t ∈ a :: ts, Pending input (t / 1024) (t % 1024) 0 s) :
    ∀ t ∈ ts, Pending input (t / 1024) (t % 1024) 0 (prefixState ops input a s) := by
  intro t ht
  have hne : t ≠ a := by intro he; subst t; exact hn ht
  exact prefix_pending_other p ops input a t 0 s hne (pending t (by simp [ht]))

theorem prefix_fold_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (ts : List Nat) (s : State α) (hn : ts.Nodup)
    (ht : ∀ t ∈ ts, t < p.rows * 1024)
    (pending : ∀ t ∈ ts, Pending input (t / 1024) (t % 1024) 0 s)
    (good : ∀ a ∈ s.trace, Good a) :
    ∀ a ∈ (prefixFold ops input ts s).trace, Good a := by
  induction ts generalizing s with
  | nil => exact good
  | cons a ts ih =>
      obtain ⟨hnot, hnodup⟩ := List.nodup_cons.mp hn
      exact ih (prefixState ops input a s) hnodup (by intro t hm; exact ht t (by simp [hm]))
        (prefix_fold_pending_tail p ops input a ts s hnot pending)
        (prefix_good p ops input a s (ht a (by simp)) (pending a (by simp)) good)

/-- The actual sequential `foldlM runLane`, retaining prior in-place writes. -/
theorem prefix_fold_run (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (ts : List Nat) (s : State α) (hn : ts.Nodup)
    (ht : ∀ t ∈ ts, t < p.rows * 1024) (hp : ∀ t ∈ ts, s.pc t = 0)
    (pending : ∀ t ∈ ts, Pending input (t / 1024) (t % 1024) 0 s)
    (good : ∀ a ∈ s.trace, Good a) :
    ts.foldlM (fun s t => LarkCollective.runLane ops (layout p) (geometry p) program t fuel.lane s) s =
      some (prefixFold ops input ts s) := by
  induction ts generalizing s with
  | nil => rfl
  | cons a ts ih =>
      obtain ⟨hnot, hnodup⟩ := List.nodup_cons.mp hn
      have hbound : ∀ t ∈ ts, t < p.rows * 1024 := by intro t hm; exact ht t (by simp [hm])
      have hpc : ∀ t ∈ ts, (prefixState ops input a s).pc t = 0 := by
        intro t hm
        have hne : t ≠ a := by intro he; subst t; exact hnot hm
        exact (prefix_other ops input a t s hne).1.trans (hp t (by simp [hm]))
      rewrite [List.foldlM_cons,
        prefix_run p ops input a s (ht a (by simp)) (hp a (by simp)) (pending a (by simp)) good]
      simp only [bind, Option.some_bind]
      exact ih (prefixState ops input a s) hnodup hbound hpc
        (prefix_fold_pending_tail p ops input a ts s hnot pending)
        (prefix_good p ops input a s (ht a (by simp)) (pending a (by simp)) good)

theorem prefix_fold_member (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (ts : List Nat) (s : State α) (hn : ts.Nodup)
    (ht : ∀ t ∈ ts, t < p.rows * 1024)
    (pending : ∀ t ∈ ts, Pending input (t / 1024) (t % 1024) 0 s)
    (good : ∀ a ∈ s.trace, Good a) (t : Nat) (hm : t ∈ ts) :
    PrefixReady ops input t (prefixFold ops input ts s) := by
  induction ts generalizing s with
  | nil => simp at hm
  | cons a ts ih =>
      obtain ⟨hnot, hnodup⟩ := List.nodup_cons.mp hn
      rcases List.mem_cons.mp hm with he | hmem
      · subst t
        exact prefix_fold_ready_other p ops input ts a (prefixState ops input a s) hnot
          (prefix_ready p ops input a s (ht a (by simp)) (pending a (by simp)) good)
      · exact ih (prefixState ops input a s) hnodup (by intro t hm; exact ht t (by simp [hm]))
          (prefix_fold_pending_tail p ops input a ts s hnot pending)
          (prefix_good p ops input a s (ht a (by simp)) (pending a (by simp)) good) hmem

theorem initial_pending_lanes (p : Shape) (input : Nat → Nat → α) (outside : Location → Option α)
    (ts : List Nat) (ht : ∀ t ∈ ts, t < p.rows * 1024) :
    ∀ t ∈ ts, Pending input (t / 1024) (t % 1024) 0 (initial p input outside) := by
  intro t hm
  have hb := ht t hm
  exact initial_pending p input outside (t / 1024) (t % 1024) (by omega) (Nat.mod_lt _ (by decide))

theorem initial_prefix_fold_run (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (ts : List Nat) (hn : ts.Nodup)
    (ht : ∀ t ∈ ts, t < p.rows * 1024) :
    ts.foldlM (fun s t => LarkCollective.runLane ops (layout p) (geometry p) program t fuel.lane s)
      (initial p input outside) = some (prefixFold ops input ts (initial p input outside)) :=
  prefix_fold_run p ops input ts _ hn ht (by intro t hm; rfl)
    (initial_pending_lanes p input outside ts ht) (by intro a ha; cases ha)

theorem initial_prefix_fold_member (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (ts : List Nat) (hn : ts.Nodup)
    (ht : ∀ t ∈ ts, t < p.rows * 1024) (t : Nat) (hm : t ∈ ts) :
    PrefixReady ops input t (prefixFold ops input ts (initial p input outside)) :=
  prefix_fold_member p ops input ts _ hn ht
    (initial_pending_lanes p input outside ts ht) (by intro a ha; cases ha) t hm

theorem initial_prefix_fold_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (ts : List Nat) (hn : ts.Nodup)
    (ht : ∀ t ∈ ts, t < p.rows * 1024) :
    ∀ a ∈ (prefixFold ops input ts (initial p input outside)).trace, Good a :=
  prefix_fold_good p ops input ts _ hn ht
    (initial_pending_lanes p input outside ts ht) (by intro a ha; cases ha)

theorem initial_prefix_fold_race_free (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (ts : List Nat) (hn : ts.Nodup)
    (ht : ∀ t ∈ ts, t < p.rows * 1024) :
    raceFree (geometry p) (prefixFold ops input ts (initial p input outside)).trace = true :=
  race_free p _ (initial_prefix_fold_good p ops input outside ts hn ht)

#print axioms prefix_indices
#print axioms prefix_ready
#print axioms prefix_ready_other
#print axioms prefix_fold_other
#print axioms prefix_fold_ready_other
#print axioms prefix_fold_epochs
#print axioms prefix_fold_frame
#print axioms prefix_fold_trace_length
#print axioms prefix_fold_good
#print axioms prefix_fold_run
#print axioms prefix_fold_member
#print axioms initial_prefix_fold_run
#print axioms initial_prefix_fold_member
#print axioms initial_prefix_fold_good
#print axioms initial_prefix_fold_race_free
end LarkNativeFusedRmsNorm
