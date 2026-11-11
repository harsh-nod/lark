import Lark.NativeAttentionKeyCycle

/-! Complete actual native block execution through all four keys and halt.
The output reference retains the source's arbitrary scalar operations and half casts. -/
namespace LarkNativeAttention
open LarkNonlinear
set_option maxRecDepth 1000
set_option maxHeartbeats 2000000

def finalBlock (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (b : Nat) (s : State α) : State α :=
  haltBlock p b (keysCompleted p ops input b 3 (firstResumed p ops input b s))
theorem final_block_state (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (b : Nat) (s : State α) :
    finalBlock p ops input b s = haltFold (blockThreads (geometry p) b) (keysCompleted p ops input b 3 (firstResumed p ops input b s)) := rfl

theorem final_block_run (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (b : Nat) (s : State α)
    (hb : b < p.groups) (hr : Reads p input s) (hp : ∀ t ∈ blockThreads (geometry p) b, s.pc t = 0)
    (he : ∀ t ∈ blockThreads (geometry p) b, (s.epochs t).block % 2 = 0) (hg : TraceGood s) :
    runBlock ops (layout p) (geometry p) fuel program b fuel.block s = some (finalBlock p ops input b s) := by
  have start := initial_query_start p ops input b s hb hr he hg
  have done := keys_completed_spec p ops input b 3 (firstResumed p ops input b s) start
  have h1 := first_block_step p ops input b 8 s hb hr hp
  have h2 := keys_completed_reduction p ops input b 3 1 (firstResumed p ops input b s) (by decide) start
  have h3 := halt_block_run p ops b 0 (keysCompleted p ops input b 3 (firstResumed p ops input b s))
    (by intro t ht; exact ⟨(done.ready t ht).pc, (done.ready t ht).keyIndex⟩)
  exact h1.trans (h2.trans h3)

theorem final_block_frames (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (b : Nat) (s : State α) :
    (finalBlock p ops input b s).memory = (keysCompleted p ops input b 3 (firstResumed p ops input b s)).memory ∧
    (finalBlock p ops input b s).epochs = (keysCompleted p ops input b 3 (firstResumed p ops input b s)).epochs ∧
    (finalBlock p ops input b s).trace = (keysCompleted p ops input b 3 (firstResumed p ops input b s)).trace := by
  have hs := final_block_state p ops input b s
  have hf := halt_fold_frames (blockThreads (geometry p) b) (keysCompleted p ops input b 3 (firstResumed p ops input b s))
  exact ⟨(congrArg (fun state : State α => state.memory) hs).trans hf.1,
    (congrArg (fun state : State α => state.epochs) hs).trans hf.2.1,
    (congrArg (fun state : State α => state.trace) hs).trans hf.2.2⟩

theorem final_block_member (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (b t : Nat) (s : State α)
    (ht : t ∈ blockThreads (geometry p) b) :
    (finalBlock p ops input b s).pc t = 90 ∧ (finalBlock p ops input b s).indices t 5 = some 4 :=
  Eq.mpr (congrArg (fun state : State α => state.pc t = 90 ∧ state.indices t 5 = some 4) (final_block_state p ops input b s))
    (halt_fold_member (blockThreads (geometry p) b) t (keysCompleted p ops input b 3 (firstResumed p ops input b s)) (block_nodup p b) ht)

theorem final_block_values (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (b t qi col : Nat) (s : State α)
    (hb : b < p.groups) (hr : Reads p input s)
    (he : ∀ u ∈ blockThreads (geometry p) b, (s.epochs u).block % 2 = 0) (hg : TraceGood s)
    (ht : t ∈ blockThreads (geometry p) b) (hi : qi < 4) (hc : col < 256) :
    (finalBlock p ops input b s).memory (globalCell 0 (globalAddress t qi col)) = some ((onlineValues ops input 4 t qi).stored col) := by
  have done := keys_completed_spec p ops input b 3 (firstResumed p ops input b s) (initial_query_start p ops input b s hb hr he hg)
  exact (congrArg (fun memory => memory (globalCell 0 (globalAddress t qi col))) (final_block_frames p ops input b s).1).trans
    ((done.values t ht qi (by omega) hi).1 col (by omega) hc)

theorem final_block_private (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (b t qi : Nat) (s : State α)
    (hb : b < p.groups) (hr : Reads p input s)
    (he : ∀ u ∈ blockThreads (geometry p) b, (s.epochs u).block % 2 = 0) (hg : TraceGood s)
    (ht : t ∈ blockThreads (geometry p) b) (hi : qi < 4) :
    (finalBlock p ops input b s).memory (privateCell t 0 qi) = some (onlineValues ops input 4 t qi).maximum ∧
    (finalBlock p ops input b s).memory (privateCell t 1 qi) = some (onlineValues ops input 4 t qi).mass := by
  have done := keys_completed_spec p ops input b 3 (firstResumed p ops input b s) (initial_query_start p ops input b s hb hr he hg)
  have hv := (done.values t ht qi (by omega) hi).2 (by decide)
  have hm := (final_block_frames p ops input b s).1
  exact ⟨(congrArg (fun memory => memory (privateCell t 0 qi)) hm).trans hv.1,
    (congrArg (fun memory => memory (privateCell t 1 qi)) hm).trans hv.2⟩

theorem final_block_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (b : Nat) (s : State α)
    (hb : b < p.groups) (hr : Reads p input s)
    (he : ∀ u ∈ blockThreads (geometry p) b, (s.epochs u).block % 2 = 0) (hg : TraceGood s) :
    Reads p input (finalBlock p ops input b s) :=
  reads_of_memory p input (keysCompleted p ops input b 3 (firstResumed p ops input b s)) (finalBlock p ops input b s)
    (keys_completed_spec p ops input b 3 (firstResumed p ops input b s) (initial_query_start p ops input b s hb hr he hg)).reads
    (final_block_frames p ops input b s).1

theorem final_block_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (b : Nat) (s : State α)
    (hb : b < p.groups) (hr : Reads p input s)
    (he : ∀ u ∈ blockThreads (geometry p) b, (s.epochs u).block % 2 = 0) (hg : TraceGood s) :
    TraceGood (finalBlock p ops input b s) := by
  have done := keys_completed_spec p ops input b 3 (firstResumed p ops input b s) (initial_query_start p ops input b s hb hr he hg)
  intro a ha
  exact done.good a ((final_block_frames p ops input b s).2.2 ▸ ha)

/-- Every active block runs all nine native phases, all four keys and the real
halt, for all allowed shapes, scalar operations, input and outside memory. -/
theorem final_block_initial (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (b : Nat) (hb : b < p.groups) :
    ∃ final,
      runBlock ops (layout p) (geometry p) fuel program b fuel.block (initial (layout p) input outside) = some final ∧
      (∀ t ∈ blockThreads (geometry p) b, final.pc t = 90 ∧ final.indices t 5 = some 4) ∧
      (∀ t ∈ blockThreads (geometry p) b, ∀ qi, qi < 4 → ∀ col, col < 256 →
        final.memory (globalCell 0 (globalAddress t qi col)) = some ((onlineValues ops input 4 t qi).stored col)) ∧
      Reads p input final ∧ raceFree (geometry p) final.trace = true := by
  exact ⟨finalBlock p ops input b (initial (layout p) input outside),
    final_block_run p ops input b (initial (layout p) input outside) hb (initial_reads p input outside)
      (by intro t ht; rfl) (by intro t ht; rfl) (by intro a ha; cases ha),
    (by intro t ht; exact final_block_member p ops input b t (initial (layout p) input outside) ht),
    (by
      intro t ht qi hi col hc
      exact final_block_values p ops input b t qi col (initial (layout p) input outside)
        hb (initial_reads p input outside) (by intro u hu; rfl) (by intro a ha; cases ha) ht hi hc),
    final_block_reads p ops input b (initial (layout p) input outside) hb (initial_reads p input outside)
      (by intro u hu; rfl) (by intro a ha; cases ha),
    race_free p _ (final_block_good p ops input b (initial (layout p) input outside) hb (initial_reads p input outside)
      (by intro u hu; rfl) (by intro a ha; cases ha))⟩

#print axioms final_block_run
#print axioms final_block_member
#print axioms final_block_values
#print axioms final_block_private
#print axioms final_block_reads
#print axioms final_block_good
#print axioms final_block_initial
end LarkNativeAttention
