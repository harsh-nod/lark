import Lark.NativeAttentionHalt

/-! Online values and state invariants for composing every key tile. -/
namespace LarkNativeAttention
open LarkNonlinear
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def onlineValues (ops : Ops α) (input : Nat → Nat → α) : Nat → Nat → Nat → QueryValue α
  | 0, _, _ => initialQueryValue ops
  | key + 1, t, qi => nextQueryValue ops input t qi key (onlineValues ops input key t qi)

structure QueryStart (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (b key : Nat) (s : State α) : Prop where
  reads : Reads p input s
  ready : ∀ t ∈ blockThreads (geometry p) b, QueryLaneReady p ops input t key (onlineValues ops input key t) s
  odd : ∀ t ∈ blockThreads (geometry p) b, (s.epochs t).block % 2 = 1
  good : TraceGood s

structure KeyDone (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (b key : Nat) (s : State α) : Prop where
  reads : Reads p input s
  ready : ∀ t ∈ blockThreads (geometry p) b, CopyLaneReady p t key s
  values : ∀ t ∈ blockThreads (geometry p) b, QueriesRange t (key + 1) (onlineValues ops input (key + 1) t) 0 4 s
  even : ∀ t ∈ blockThreads (geometry p) b, (s.epochs t).block % 2 = 0
  good : TraceGood s

theorem query_phase_done (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (b key : Nat)
    (s : State α) (start : QueryStart p ops input b key s) :
    KeyDone p ops input b key (queryResumed p ops input key b (onlineValues ops input key) s) := by
  refine ⟨query_resumed_reads p ops input key b _ s start.reads, ?_, ?_, ?_,
    query_resumed_good p ops input key b _ s start.odd start.good⟩
  · intro t ht
    have hm := query_resumed_member p ops input key b t _ s start.reads start.ready ht
    exact ⟨(start.ready t ht).bound, hm.1, hm.2, query_resumed_pc p ops input key b t _ s start.reads start.ready ht⟩
  · intro t ht qi hq hi
    constructor
    · intro col hc hb
      exact query_resumed_value p ops input key b t qi col _ s ht hi hb
    · intro hj
      exact query_resumed_private p ops input key b t qi _ s ht hi
  · intro t ht
    rw [query_resumed_epoch p ops input key b t _ s ht]
    change ((s.epochs t).block + 1) % 2 = 0
    have old := start.odd t ht
    omega

theorem copy_phase_start (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (b key : Nat)
    (s : State α) (done : KeyDone p ops input b key s) :
    QueryStart p ops input b (key + 1) (nextResumed p ops input key b s) := by
  refine ⟨next_resumed_reads p ops input key b s done.reads, ?_, ?_, next_resumed_good p ops input key b s done.even done.good⟩
  · intro t ht
    have hm := next_resumed_member p ops input key b t s done.ready ht
    exact ⟨(done.ready t ht).bound, hm.1, next_resumed_tiles p ops input key b t s ht, hm.2,
      next_resumed_pc p ops input key b t s done.ready ht,
      next_resumed_queries p ops input key b t (key + 1) 0 4 _ s (done.values t ht)⟩
  · intro t ht
    rw [next_resumed_epoch p ops input key b t s ht]
    change ((s.epochs t).block + 1) % 2 = 1
    have old := done.even t ht
    omega

theorem initial_query_start (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (b : Nat) (s : State α)
    (hb : b < p.groups) (hr : Reads p input s)
    (he : ∀ t ∈ blockThreads (geometry p) b, (s.epochs t).block % 2 = 0) (hg : TraceGood s) :
    QueryStart p ops input b 0 (firstResumed p ops input b s) := by
  refine ⟨first_resumed_reads p ops input b s hr, first_key_ready p ops input b s hb, ?_, first_resumed_good p ops input b s he hg⟩
  intro t ht
  rw [first_resumed_epoch p ops input b t s ht]
  change ((s.epochs t).block + 1) % 2 = 1
  have old := he t ht
  omega

def keysCompleted (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (b : Nat) : Nat → State α → State α
  | 0, s => queryResumed p ops input 0 b (onlineValues ops input 0) s
  | key + 1, s => queryResumed p ops input (key + 1) b (onlineValues ops input (key + 1))
      (nextResumed p ops input key b (keysCompleted p ops input b key s))

theorem keys_completed_zero (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (b : Nat) (s : State α) :
    keysCompleted p ops input b 0 s = queryResumed p ops input 0 b (onlineValues ops input 0) s := rfl
theorem keys_completed_succ (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (b key : Nat) (s : State α) :
    keysCompleted p ops input b (key + 1) s = queryResumed p ops input (key + 1) b (onlineValues ops input (key + 1))
      (nextResumed p ops input key b (keysCompleted p ops input b key s)) := rfl

theorem keys_completed_spec (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (b key : Nat) (s : State α)
    (start : QueryStart p ops input b 0 s) : KeyDone p ops input b key (keysCompleted p ops input b key s) := by
  induction key with
  | zero =>
      exact Eq.mpr (congrArg (KeyDone p ops input b 0) (keys_completed_zero p ops input b s)) (query_phase_done p ops input b 0 s start)
  | succ key ih =>
      exact Eq.mpr (congrArg (KeyDone p ops input b (key + 1)) (keys_completed_succ p ops input b key s))
        (query_phase_done p ops input b (key + 1) _ (copy_phase_start p ops input b key _ ih))

theorem keys_completed_reduction (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (b key extra : Nat) (s : State α)
    (hk : key < 4) (start : QueryStart p ops input b 0 s) :
    runBlock ops (layout p) (geometry p) fuel program b (extra + (2 * key + 1)) s =
      runBlock ops (layout p) (geometry p) fuel program b extra (keysCompleted p ops input b key s) := by
  induction key generalizing extra with
  | zero => exact query_block_step p ops input 0 b extra (onlineValues ops input 0) s start.reads start.ready
  | succ key ih =>
      have done := keys_completed_spec p ops input b key s start
      have copied := copy_phase_start p ops input b key (keysCompleted p ops input b key s) done
      have h1 := ih (extra + 2) (by omega)
      have h2 := next_block_step p ops input key b (extra + 1) (keysCompleted p ops input b key s) hk done.reads done.ready
      have h3 := query_block_step p ops input (key + 1) b extra (onlineValues ops input (key + 1))
        (nextResumed p ops input key b (keysCompleted p ops input b key s)) copied.reads copied.ready
      have h3' := h3.trans (congrArg (fun state => runBlock ops (layout p) (geometry p) fuel program b extra state)
        (keys_completed_succ p ops input b key s).symm)
      have steps : extra + (2 * (key + 1) + 1) = (extra + 2) + (2 * key + 1) := by omega
      exact (congrArg (fun n => runBlock ops (layout p) (geometry p) fuel program b n s) steps).trans (h1.trans (h2.trans h3'))

#print axioms query_phase_done
#print axioms copy_phase_start
#print axioms initial_query_start
#print axioms keys_completed_spec
#print axioms keys_completed_reduction
end LarkNativeAttention
