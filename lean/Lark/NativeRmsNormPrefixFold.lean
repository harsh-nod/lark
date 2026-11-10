import Lark.NativeRmsNormPrefix

/-! Compose the actual prefix through the scheduler's sequential lane fold.
This covers arbitrary distinct cohorts without assuming simultaneous lane updates.
-/
namespace LarkNativeRmsNorm
open LarkNonlinear
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def NativeIndices (t : Nat) (s : State α) : Prop :=
  s.indices t 0 = some ((t / 1024 : Nat) : Int) ∧
  s.indices t 1 = some ((t % 1024 : Nat) : Int) ∧
  s.indices t 2 = some (((t % 1024) % 64 : Nat) : Int) ∧
  s.indices t 3 = some (((t % 1024) / 64 : Nat) : Int) ∧
  s.indices t 4 = some (1024 - (((t % 1024) / 64 : Nat) : Int) * 64)

def PrefixReady (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) : Prop :=
  s.pc t = 18 ∧ s.regs t 0 = some (threadSum ops input (t / 1024) (t % 1024)) ∧ NativeIndices t s

theorem prefix_ready (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) :
    PrefixReady ops input t (prefixState ops input t s) :=
  ⟨prefix_pc ops input t s, prefix_acc ops input t s, prefix_indices ops input t s⟩

def prefixFold (ops : Ops α) (input : Nat → Nat → α) (ts : List Nat) (s : State α) : State α :=
  ts.foldl (fun s t => prefixState ops input t s) s

theorem prefix_fold_preserves (ops : Ops α) (input : Nat → Nat → α) (ts : List Nat) (s : State α) :
    (prefixFold ops input ts s).memory = s.memory ∧ (prefixFold ops input ts s).epochs = s.epochs := by
  induction ts generalizing s with
  | nil => exact ⟨rfl, rfl⟩
  | cons a ts ih =>
      have h := ih (prefixState ops input a s)
      have h1 := prefix_preserves ops input a s
      exact ⟨h.1.trans h1.1, h.2.trans h1.2⟩

theorem prefix_fold_other (ops : Ops α) (input : Nat → Nat → α) (ts : List Nat) (t : Nat)
    (s : State α) (ht : t ∉ ts) :
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

theorem prefix_fold_member (ops : Ops α) (input : Nat → Nat → α) (ts : List Nat)
    (s : State α) (hn : ts.Nodup) (t : Nat) (ht : t ∈ ts) :
    PrefixReady ops input t (prefixFold ops input ts s) := by
  induction ts generalizing s with
  | nil => simp at ht
  | cons a ts ih =>
      rcases List.nodup_cons.mp hn with ⟨hnot, hnodup⟩
      rcases List.mem_cons.mp ht with he | hm
      · subst t
        have h := prefix_fold_other ops input ts a (prefixState ops input a s) hnot
        have hr := prefix_ready ops input a s
        change PrefixReady ops input a (prefixFold ops input ts (prefixState ops input a s))
        simpa only [PrefixReady, NativeIndices, h.1, h.2.1, h.2.2] using hr
      · exact ih (prefixState ops input a s) hnodup hm

theorem prefix_fold_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (ts : List Nat) (s : State α)
    (hg : ∀ a ∈ s.trace, LarkReductionFootprint.Good (traversal p) 0 a) :
    ∀ a ∈ (prefixFold ops input ts s).trace, LarkReductionFootprint.Good (traversal p) 0 a := by
  induction ts generalizing s with
  | nil => exact hg
  | cons t ts ih => exact ih (prefixState ops input t s) (prefix_good p ops input t s hg)

/-- Equality for the actual `foldlM runLane`, not a simultaneous-state shortcut. -/
theorem prefix_fold_run (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (ts : List Nat)
    (s : State α) (hn : ts.Nodup) (reads : Reads p input s)
    (ht : ∀ t ∈ ts, t < p.rows * 1024) (hp : ∀ t ∈ ts, s.pc t = 0) :
    ts.foldlM (fun s t => LarkCollective.runLane ops (layout p) (geometry p) program t fuel.lane s) s =
      some (prefixFold ops input ts s) := by
  induction ts generalizing s with
  | nil => rfl
  | cons a ts ih =>
      rcases List.nodup_cons.mp hn with ⟨hnot, hnodup⟩
      have hread := reads_of_memory p input s (prefixState ops input a s) reads (prefix_preserves ops input a s).1
      have hbound : ∀ t ∈ ts, t < p.rows * 1024 := by intro t hm; exact ht t (by simp [hm])
      have hpc : ∀ t ∈ ts, (prefixState ops input a s).pc t = 0 := by
        intro t hm
        have hne : t ≠ a := by intro he; subst t; exact hnot hm
        exact (prefix_other ops input a t s hne).1.trans (hp t (by simp [hm]))
      rewrite [List.foldlM_cons, prefix_lane p ops input a s reads (ht a (by simp)) (hp a (by simp))]
      simp only [bind, Option.some_bind]
      exact ih (prefixState ops input a s) hnodup hread hbound hpc

#print axioms prefix_fold_run
#print axioms prefix_fold_member
#print axioms prefix_fold_good
end LarkNativeRmsNorm
