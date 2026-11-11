import Lark.NativeAttentionQueryBlock

/-! The actual first two block phases: native initialization and a full key tile. -/
namespace LarkNativeAttention
open LarkNonlinear
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def firstKeyResumed (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (b : Nat) (s : State α) : State α :=
  queryResumed p ops input 0 b (fun _ _ => initialQueryValue ops) (firstResumed p ops input b s)
theorem first_key_resumed_state (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (b : Nat) (s : State α) :
    firstKeyResumed p ops input b s =
      queryResumed p ops input 0 b (fun _ _ => initialQueryValue ops) (firstResumed p ops input b s) := rfl

theorem first_key_ready (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (b : Nat) (s : State α) (hb : b < p.groups) :
    ∀ t ∈ blockThreads (geometry p) b,
      QueryLaneReady p ops input t 0 (fun _ => initialQueryValue ops) (firstResumed p ops input b s) := by
  intro t ht
  have hbound : t < p.groups * 32 := by
    obtain ⟨lane, hl, rfl⟩ := (block_mem p b t).mp ht
    omega
  exact ⟨hbound, first_resumed_native p ops input b t s ht, first_resumed_tiles p ops input b t s ht,
    first_resumed_key p ops input b t s ht, first_resumed_pc p ops input b t s ht, first_resumed_queries p ops input b t s ht⟩

theorem first_key_block_reduction (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (b : Nat) (hb : b < p.groups) :
    runBlock ops (layout p) (geometry p) fuel program b fuel.block (initial (layout p) input outside) =
      runBlock ops (layout p) (geometry p) fuel program b 7 (firstKeyResumed p ops input b (initial (layout p) input outside)) := by
  let start := initial (layout p) input outside
  have hr := initial_reads p input outside
  have h1 := first_block_step p ops input b 8 start hb hr (by intro t ht; rfl)
  have h2 := query_block_step p ops input 0 b 7 (fun _ _ => initialQueryValue ops) (firstResumed p ops input b start)
    (first_resumed_reads p ops input b start hr) (first_key_ready p ops input b start hb)
  exact h1.trans h2

theorem first_key_resumed_epoch (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (b t : Nat)
    (s : State α) (ht : t ∈ blockThreads (geometry p) b) :
    (firstKeyResumed p ops input b s).epochs t = bumpEpoch (bumpEpoch (s.epochs t) .block) .block :=
  (congrArg (fun state : State α => state.epochs t) (first_key_resumed_state p ops input b s)).trans
    ((query_resumed_epoch p ops input 0 b t (fun _ _ => initialQueryValue ops) (firstResumed p ops input b s) ht).trans
      (congrArg (fun epoch => bumpEpoch epoch .block) (first_resumed_epoch p ops input b t s ht)))

theorem first_key_resumed_member (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (b t : Nat) (hb : b < p.groups) (ht : t ∈ blockThreads (geometry p) b) :
    (firstKeyResumed p ops input b (initial (layout p) input outside)).pc t = 88 ∧
    NativeIndices t (firstKeyResumed p ops input b (initial (layout p) input outside)) ∧
    (firstKeyResumed p ops input b (initial (layout p) input outside)).indices t 5 = some 0 ∧
    ((firstKeyResumed p ops input b (initial (layout p) input outside)).epochs t).block = 2 := by
  have hr := first_resumed_reads p ops input b (initial (layout p) input outside) (initial_reads p input outside)
  have ready := first_key_ready p ops input b (initial (layout p) input outside) hb
  have hs := first_key_resumed_state p ops input b (initial (layout p) input outside)
  have hm := query_resumed_member p ops input 0 b t (fun _ _ => initialQueryValue ops)
    (firstResumed p ops input b (initial (layout p) input outside)) hr ready ht
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (congrArg (fun state : State α => state.pc t) hs).trans
      (query_resumed_pc p ops input 0 b t (fun _ _ => initialQueryValue ops)
        (firstResumed p ops input b (initial (layout p) input outside)) hr ready ht)
  · exact Eq.mpr (congrArg (NativeIndices t) hs) hm.1
  · exact (congrArg (fun state : State α => state.indices t 5) hs).trans hm.2
  · exact (congrArg Epoch.block (first_key_resumed_epoch p ops input b t (initial (layout p) input outside) ht)).trans rfl

theorem first_key_resumed_value (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (b t qi col : Nat)
    (s : State α) (ht : t ∈ blockThreads (geometry p) b) (hi : qi < 4) (hc : col < 256) :
    (firstKeyResumed p ops input b s).memory (globalCell 0 (globalAddress t qi col)) =
      some ((firstKeyValues ops input t qi).stored col) :=
  (congrArg (fun state : State α => state.memory (globalCell 0 (globalAddress t qi col))) (first_key_resumed_state p ops input b s)).trans
    (query_resumed_value p ops input 0 b t qi col (fun _ _ => initialQueryValue ops) (firstResumed p ops input b s) ht hi hc)

theorem first_key_resumed_private (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (b t qi : Nat)
    (s : State α) (ht : t ∈ blockThreads (geometry p) b) (hi : qi < 4) :
    (firstKeyResumed p ops input b s).memory (privateCell t 0 qi) = some (firstKeyValues ops input t qi).maximum ∧
    (firstKeyResumed p ops input b s).memory (privateCell t 1 qi) = some (firstKeyValues ops input t qi).mass := by
  have hs := first_key_resumed_state p ops input b s
  have hf := query_resumed_private p ops input 0 b t qi (fun _ _ => initialQueryValue ops) (firstResumed p ops input b s) ht hi
  exact ⟨(congrArg (fun state : State α => state.memory (privateCell t 0 qi)) hs).trans hf.1,
    (congrArg (fun state : State α => state.memory (privateCell t 1 qi)) hs).trans hf.2⟩

theorem first_key_resumed_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (b : Nat)
    (s : State α) (hr : Reads p input s) : Reads p input (firstKeyResumed p ops input b s) :=
  Eq.mpr (congrArg (Reads p input) (first_key_resumed_state p ops input b s))
    (query_resumed_reads p ops input 0 b (fun _ _ => initialQueryValue ops) _ (first_resumed_reads p ops input b s hr))

theorem first_key_resumed_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (b : Nat)
    (inputState : State α) (he : ∀ t ∈ blockThreads (geometry p) b, (inputState.epochs t).block % 2 = 0)
    (hg : TraceGood inputState) : TraceGood (firstKeyResumed p ops input b inputState) := by
  have he' : ∀ t ∈ blockThreads (geometry p) b, ((firstResumed p ops input b inputState).epochs t).block % 2 = 1 := by
    intro t ht
    rw [first_resumed_epoch p ops input b t inputState ht]
    change ((inputState.epochs t).block + 1) % 2 = 1
    have prior := he t ht
    omega
  exact Eq.mpr (congrArg TraceGood (first_key_resumed_state p ops input b inputState))
    (query_resumed_good p ops input 0 b (fun _ _ => initialQueryValue ops) _ he' (first_resumed_good p ops input b inputState he hg))

/-- Both actual native block phases and both barrier resumes. All 32 lanes
complete all four query rows for key tile zero. Three key tiles still follow. -/
theorem first_key_block_initial (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (b : Nat) (hb : b < p.groups) :
    ∃ final,
      runBlock ops (layout p) (geometry p) fuel program b fuel.block (initial (layout p) input outside) =
        runBlock ops (layout p) (geometry p) fuel program b 7 final ∧
      (∀ t ∈ blockThreads (geometry p) b, final.pc t = 88 ∧ NativeIndices t final ∧
        final.indices t 5 = some 0 ∧ (final.epochs t).block = 2) ∧
      (∀ t ∈ blockThreads (geometry p) b, ∀ qi, qi < 4 → ∀ col, col < 256 →
        final.memory (globalCell 0 (globalAddress t qi col)) = some ((firstKeyValues ops input t qi).stored col)) ∧
      (∀ t ∈ blockThreads (geometry p) b, ∀ qi, qi < 4 →
        final.memory (privateCell t 0 qi) = some (firstKeyValues ops input t qi).maximum ∧
        final.memory (privateCell t 1 qi) = some (firstKeyValues ops input t qi).mass) ∧
      Reads p input final ∧ raceFree (geometry p) final.trace = true := by
  exact ⟨firstKeyResumed p ops input b (initial (layout p) input outside), first_key_block_reduction p ops input outside b hb,
    (by intro t ht; exact first_key_resumed_member p ops input outside b t hb ht),
    (by intro t ht qi hi col hc; exact first_key_resumed_value p ops input b t qi col (initial (layout p) input outside) ht hi hc),
    (by intro t ht qi hi; exact first_key_resumed_private p ops input b t qi (initial (layout p) input outside) ht hi),
    first_key_resumed_reads p ops input b (initial (layout p) input outside) (initial_reads p input outside),
    race_free p _ (first_key_resumed_good p ops input b (initial (layout p) input outside) (by intro t ht; rfl) (by intro a ha; cases ha))⟩

#print axioms first_key_ready
#print axioms first_key_block_reduction
#print axioms first_key_resumed_epoch
#print axioms first_key_resumed_member
#print axioms first_key_resumed_value
#print axioms first_key_resumed_private
#print axioms first_key_resumed_reads
#print axioms first_key_resumed_good
#print axioms first_key_block_initial
end LarkNativeAttention
