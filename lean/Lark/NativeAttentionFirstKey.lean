import Lark.NativeAttentionQueryTile
import Lark.NativeAttentionFirstQueryComplete

/-! From real native initialization to all four first-key query rows for a lane.
Other lanes' query phases and subsequent block/key phases are not asserted. -/
namespace LarkNativeAttention
open LarkNonlinear
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def initialQueryValue (ops : Ops α) : QueryValue α :=
  ⟨ops.literal 0 1, ops.literal 0 1, fun _ => zeroValue ops⟩
def firstKeyValues (ops : Ops α) (input : Nat → Nat → α) (t qi : Nat) : QueryValue α :=
  nextQueryValue ops input t qi 0 (initialQueryValue ops)
def firstKeyLane (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) : State α :=
  queryTile ops input t 0 (fun _ => initialQueryValue ops) s
theorem first_key_lane_state (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) :
    firstKeyLane ops input t s = queryTile ops input t 0 (fun _ => initialQueryValue ops) s := rfl

theorem first_resumed_queries (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (b t : Nat) (s : State α) (ht : t ∈ blockThreads (geometry p) b) :
    QueriesRange t 0 (fun _ => initialQueryValue ops) 0 4 (firstResumed p ops input b s) := by
  intro qi hq hi
  constructor
  · intro col hc hb
    exact first_resumed_output p ops input b t qi col s ht hi hb
  · intro h
    exact False.elim (h rfl)

theorem first_key_lane_from_resumed (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (b t : Nat) (s : State α) (hb : b < p.groups) (ht : t ∈ blockThreads (geometry p) b) (hr : Reads p input s) :
    runLane ops (layout p) (geometry p) program t fuel.lane (firstResumed p ops input b s) =
      some (firstKeyLane ops input t (firstResumed p ops input b s)) := by
  have hbound : t < p.groups * 32 := by
    obtain ⟨lane, hl, rfl⟩ := (block_mem p b t).mp ht
    omega
  exact query_tile_run p ops input t 0 (fun _ => initialQueryValue ops) _ hbound
    (first_resumed_reads p ops input b s hr) (first_resumed_native p ops input b t s ht)
    (first_resumed_tiles p ops input b t s ht) (first_resumed_key p ops input b t s ht)
    (first_resumed_queries p ops input b t s ht) (first_resumed_pc p ops input b t s ht)

theorem first_key_lane_fields (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) :
    (firstKeyLane ops input t s).pc t = 87 ∧ (firstKeyLane ops input t s).epochs = s.epochs := by
  have hs := first_key_lane_state ops input t s
  have hf := query_tile_fields ops input t 0 (fun _ => initialQueryValue ops) s
  exact ⟨(congrArg (fun state : State α => state.pc t) hs).trans hf.1,
    (congrArg (fun state : State α => state.epochs) hs).trans hf.2⟩

theorem first_key_lane_value (ops : Ops α) (input : Nat → Nat → α) (t qi col : Nat) (s : State α)
    (hi : qi < 4) (hc : col < 256) :
    (firstKeyLane ops input t s).memory (globalCell 0 (globalAddress t qi col)) = some ((firstKeyValues ops input t qi).stored col) :=
  (congrArg (fun state : State α => state.memory (globalCell 0 (globalAddress t qi col))) (first_key_lane_state ops input t s)).trans
    (query_tile_value ops input t 0 qi col (fun _ => initialQueryValue ops) s hi hc)

theorem first_key_lane_private (ops : Ops α) (input : Nat → Nat → α) (t qi : Nat) (s : State α) (hi : qi < 4) :
    (firstKeyLane ops input t s).memory (privateCell t 0 qi) = some (firstKeyValues ops input t qi).maximum ∧
    (firstKeyLane ops input t s).memory (privateCell t 1 qi) = some (firstKeyValues ops input t qi).mass := by
  have hs := first_key_lane_state ops input t s
  have hf := query_tile_private ops input t 0 qi (fun _ => initialQueryValue ops) s hi
  exact ⟨(congrArg (fun state : State α => state.memory (privateCell t 0 qi)) hs).trans hf.1,
    (congrArg (fun state : State α => state.memory (privateCell t 1 qi)) hs).trans hf.2⟩

theorem first_key_lane_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (t : Nat)
    (s : State α) (hr : Reads p input s) : Reads p input (firstKeyLane ops input t s) :=
  Eq.mpr (congrArg (Reads p input) (first_key_lane_state ops input t s))
    (query_tile_reads p ops input t 0 (fun _ => initialQueryValue ops) s hr)

theorem first_key_lane_good (ops : Ops α) (input : Nat → Nat → α) (t : Nat)
    (s : State α) (he : (s.epochs t).block % 2 = 1) (hg : TraceGood s) : TraceGood (firstKeyLane ops input t s) :=
  Eq.mpr (congrArg TraceGood (first_key_lane_state ops input t s))
    (query_tile_good ops input t 0 (fun _ => initialQueryValue ops) s he hg)

/-- The actual first block resume followed by one member lane's entire first-key
phase, using the unchanged one-million instruction budget and real block cut.
This does not compose all lanes through the second block barrier. -/
theorem first_key_initial_prefix (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (b t : Nat) (hb : b < p.groups) (ht : t ∈ blockThreads (geometry p) b) :
    ∃ final,
      runBlock ops (layout p) (geometry p) fuel program b fuel.block (initial (layout p) input outside) =
        runBlock ops (layout p) (geometry p) fuel program b 8 (firstResumed p ops input b (initial (layout p) input outside)) ∧
      runLane ops (layout p) (geometry p) program t fuel.lane (firstResumed p ops input b (initial (layout p) input outside)) = some final ∧
      final.pc t = 87 ∧
      (∀ qi, qi < 4 → ∀ col, col < 256 → final.memory (globalCell 0 (globalAddress t qi col)) = some ((firstKeyValues ops input t qi).stored col)) ∧
      (∀ qi, qi < 4 → final.memory (privateCell t 0 qi) = some (firstKeyValues ops input t qi).maximum ∧
        final.memory (privateCell t 1 qi) = some (firstKeyValues ops input t qi).mass) ∧
      Reads p input final ∧ raceFree (geometry p) final.trace = true := by
  let start := initial (layout p) input outside
  let resumed := firstResumed p ops input b start
  have hr := initial_reads p input outside
  have hg : TraceGood resumed := first_resumed_good p ops input b start
    (by intro u hu; rfl) (by intro a ha; cases ha)
  have he : (resumed.epochs t).block % 2 = 1 :=
    congrArg (fun epoch : Epoch => epoch.block % 2) (first_resumed_epoch p ops input b t start ht)
  exact ⟨firstKeyLane ops input t resumed,
    first_block_step p ops input b 8 start hb hr (by intro u hu; rfl),
    first_key_lane_from_resumed p ops input b t start hb ht hr,
    (first_key_lane_fields ops input t resumed).1,
    (by intro qi hi col hc; exact first_key_lane_value ops input t qi col resumed hi hc),
    (by intro qi hi; exact first_key_lane_private ops input t qi resumed hi),
    first_key_lane_reads p ops input t resumed (first_resumed_reads p ops input b start hr),
    race_free p _ (first_key_lane_good ops input t resumed he hg)⟩

#print axioms first_resumed_queries
#print axioms first_key_lane_from_resumed
#print axioms first_key_lane_fields
#print axioms first_key_lane_value
#print axioms first_key_lane_private
#print axioms first_key_lane_reads
#print axioms first_key_lane_good
#print axioms first_key_initial_prefix
end LarkNativeAttention
