import Lark.NativeAttentionFirstBlock

/-! The first actual block-barrier resume, using the original scheduler. -/
namespace LarkNativeAttention
open LarkNonlinear
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def firstResumed (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (b : Nat) (s : State α) : State α :=
  resume (blockThreads (geometry p) b) .block (firstBlock p ops input b s)

theorem resume_native_of (ts : List Nat) (cut : Cut) (t : Nat) (s : State α) (hn : NativeIndices t s) :
    NativeIndices t (resume ts cut s) := hn
theorem resume_reads_of (p : Shape) (input : Nat → Nat → α) (ts : List Nat) (cut : Cut)
    (s : State α) (hr : Reads p input s) : Reads p input (resume ts cut s) := hr
theorem resume_good_of (ts : List Nat) (cut : Cut) (s : State α) (hg : TraceGood s) :
    TraceGood (resume ts cut s) := hg
theorem resume_memory_of (ts : List Nat) (cut : Cut) (s : State α) (l : Location) :
    (resume ts cut s).memory l = s.memory l := rfl
theorem first_resumed_eq (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (b : Nat) (s : State α) :
    firstResumed p ops input b s = resume (blockThreads (geometry p) b) .block (firstBlock p ops input b s) := rfl

theorem resume_epoch_member (ts : List Nat) (s : State α) (t : Nat) (cut : Cut) (ht : t ∈ ts) :
    (resume ts cut s).epochs t = bumpEpoch (s.epochs t) cut := by
  simp [resume, ht]

#print axioms resume_epoch_member

theorem resume_epoch_of_epochs (ts : List Nat) (s : State α) (t : Nat) (cut : Cut)
    (epochs : Nat → Epoch) (he : s.epochs = epochs) (ht : t ∈ ts) :
    (resume ts cut s).epochs t = bumpEpoch (epochs t) cut := by
  rw [resume_epoch_member ts s t cut ht, he]

#print axioms resume_epoch_of_epochs

theorem first_block_step (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (b extra : Nat) (s : State α) (hb : b < p.groups) (hr : Reads p input s)
    (hp : ∀ t ∈ blockThreads (geometry p) b, s.pc t = 0) :
    runBlock ops (layout p) (geometry p) fuel program b (extra + 1) s =
      runBlock ops (layout p) (geometry p) fuel program b extra (firstResumed p ops input b s) := by
  have hf := first_block_fold_run p ops input b s hb hr hp
  rw [runBlock, hf]
  simp only [bind, Option.some_bind]
  rw [first_block_cut p ops input b s]
  rfl

#print axioms first_block_step

theorem first_resumed_pc (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (b t : Nat) (s : State α) (ht : t ∈ blockThreads (geometry p) b) :
    (firstResumed p ops input b s).pc t = 21 := by
  have hp := (first_fold_member ops input _ t s (block_nodup p b) ht).1
  change (if (blockThreads (geometry p) b).contains t then (firstBlock p ops input b s).pc t + 1
    else (firstBlock p ops input b s).pc t) = 21
  rw [show (blockThreads (geometry p) b).contains t = true from List.contains_iff_mem.mpr ht]
  change (firstFold ops input (blockThreads (geometry p) b) s).pc t + 1 = 21
  rw [hp]

#print axioms first_resumed_pc

theorem first_resumed_epoch (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (b t : Nat) (s : State α) (ht : t ∈ blockThreads (geometry p) b) :
    (firstResumed p ops input b s).epochs t = bumpEpoch (s.epochs t) .block := by
  have hs : firstResumed p ops input b s =
      resume (blockThreads (geometry p) b) .block (firstBlock p ops input b s) := rfl
  have hm := resume_epoch_of_epochs (blockThreads (geometry p) b) (firstBlock p ops input b s) t .block
    s.epochs (first_block_epochs p ops input b s) ht
  exact (congrArg (fun state : State α => state.epochs t) hs).trans hm

#print axioms first_resumed_epoch

theorem first_resumed_native (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (b t : Nat) (s : State α) (ht : t ∈ blockThreads (geometry p) b) :
    NativeIndices t (firstResumed p ops input b s) := by
  have hn : NativeIndices t (firstBlock p ops input b s) :=
    (first_fold_member ops input _ t s (block_nodup p b) ht).2
  exact Eq.mpr (congrArg (NativeIndices t) (first_resumed_eq p ops input b s))
    (resume_native_of _ .block t _ hn)

#print axioms first_resumed_native

theorem first_resumed_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (b : Nat) (s : State α) (hr : Reads p input s) : Reads p input (firstResumed p ops input b s) := by
  have hr1 : Reads p input (firstBlock p ops input b s) := first_fold_reads p ops input _ s hr
  exact Eq.mpr (congrArg (Reads p input) (first_resumed_eq p ops input b s))
    (resume_reads_of p input _ .block _ hr1)

#print axioms first_resumed_reads

theorem first_resumed_output (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (b t tile col : Nat) (s : State α) (ht : t ∈ blockThreads (geometry p) b)
    (hi : tile < 4) (hc : col < 256) :
    (firstResumed p ops input b s).memory (globalCell 0 (globalAddress t tile col)) = some (zeroValue ops) := by
  have hm : (firstBlock p ops input b s).memory (globalCell 0 (globalAddress t tile col)) = some (zeroValue ops) :=
    first_fold_output ops input _ t tile col s (block_nodup p b) ht hi hc
  exact (congrArg (fun state : State α => state.memory (globalCell 0 (globalAddress t tile col)))
    (first_resumed_eq p ops input b s)).trans ((resume_memory_of _ .block _ _).trans hm)

#print axioms first_resumed_output

theorem first_resumed_tile (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (b t buffer col : Nat) (s : State α) (ht : t ∈ blockThreads (geometry p) b)
    (hbuffer : buffer = 1 ∨ buffer = 2) (hc : col < 256) :
    (firstResumed p ops input b s).memory (sharedCell t buffer (sharedAddress t col)) =
      some (ops.fromHalf (input (buffer + 1) (globalAddress t 0 col))) := by
  have hm : (firstBlock p ops input b s).memory (sharedCell t buffer (sharedAddress t col)) =
      some (ops.fromHalf (input (buffer + 1) (globalAddress t 0 col))) :=
    first_fold_tile ops input _ t buffer col s (block_nodup p b) ht hbuffer hc
  exact (congrArg (fun state : State α => state.memory (sharedCell t buffer (sharedAddress t col)))
    (first_resumed_eq p ops input b s)).trans ((resume_memory_of _ .block _ _).trans hm)

#print axioms first_resumed_tile

theorem first_resumed_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (b : Nat) (s : State α) (he : ∀ t ∈ blockThreads (geometry p) b, (s.epochs t).block % 2 = 0)
    (hg : TraceGood s) : TraceGood (firstResumed p ops input b s) := by
  have hg1 : TraceGood (firstBlock p ops input b s) := first_fold_good ops input _ s he hg
  exact Eq.mpr (congrArg TraceGood (first_resumed_eq p ops input b s))
    (resume_good_of _ .block _ hg1)

#print axioms first_resumed_good
end LarkNativeAttention
