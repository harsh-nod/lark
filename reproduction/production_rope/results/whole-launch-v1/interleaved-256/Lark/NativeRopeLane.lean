import Lark.NativeRopeLaneProgram

/-! Complete source lane: initializer, four query rounds, query exit, key
initializer, one key round and halt. The native 256-step fuel is unchanged. -/
namespace LarkNativeRope
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def KeyInputs (input : Nat → Nat → α) (neox : Bool) (row tid : Nat) (s : State α) : Prop :=
  ∀ imaginary : Bool, s.memory (globalCell 1 (address 1 row tid neox imaginary)) =
    some (input 1 (address 1 row tid neox imaginary))

def laneQueries (ops : Ops α) (input : Nat → Nat → α) (neox : Bool)
    (row tid t : Nat) (s : State α) : State α :=
  querySequence ops input neox row tid t 4 (laneStarted row tid t s)
def laneKeyStart (ops : Ops α) (input : Nat → Nat → α) (neox : Bool)
    (row tid t : Nat) (s : State α) : State α :=
  beginKey tid t (laneQueries ops input neox row tid t s)
def laneKeyDone (ops : Ops α) (input : Nat → Nat → α) (neox : Bool)
    (row tid t : Nat) (s : State α) : State α :=
  keyRound ops input neox row tid t (laneKeyStart ops input neox row tid t s)
def laneFinished (ops : Ops α) (input : Nat → Nat → α) (neox : Bool)
    (row tid t : Nat) (s : State α) : State α :=
  advance (laneKeyDone ops input neox row tid t s) t 49

theorem lane_cycle (p : Shape) (neox : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid t extra : Nat) (s : State α) (hr : row < p.rows) (ht : tid < 512)
    (hthread : t = row * 512 + tid) (hp : s.pc t = 0)
    (hc : CacheReads p input s) (hq : QueryInputs input neox row tid s)
    (hk : KeyInputs input neox row tid s) :
    runLane ops (layout p) (geometry p) (program neox) t (extra + 120) s =
      runLane ops (layout p) (geometry p) (program neox) t extra
        (laneFinished ops input neox row tid t s) := by
  let started := laneStarted row tid t s
  let q := laneQueries ops input neox row tid t s
  let ks := laneKeyStart ops input neox row tid t s
  let k := laneKeyDone ops input neox row tid t s
  have startReady := lane_started_ready row tid t s
  have qReady := query_sequence_ready ops input neox row tid t 4 started startReady.1 startReady.2.1 startReady.2.2
  have ksReady := begin_key_ready row tid t q qReady.2.1
  have kReady := key_round_ready ops input neox row tid t ks ksReady.2.1
  have co := thread_coordinates row tid t ht hthread
  have hcacheStart : CacheReads p input started := hc
  have hqueryStart : QueryInputs input neox row tid started := hq
  have hcacheKey : CacheReads p input ks := by
    intro offset hoffset
    change (querySequence ops input neox row tid t 4 started).memory (globalCell 2 offset) = some (input 2 offset)
    rw [query_sequence_other_buffer ops input neox row tid t 4 2 offset started (by decide)]
    exact hc offset hoffset
  have hx : ks.memory (globalCell 1 (address 1 row tid neox false)) =
      some (input 1 (address 1 row tid neox false)) := by
    change (querySequence ops input neox row tid t 4 started).memory
      (globalCell 1 (address 1 row tid neox false)) = some (input 1 (address 1 row tid neox false))
    rw [query_sequence_other_buffer ops input neox row tid t 4 1 _ started (by decide)]
    exact hk false
  have hy : ks.memory (globalCell 1 (address 1 row tid neox true)) =
      some (input 1 (address 1 row tid neox true)) := by
    change (querySequence ops input neox row tid t 4 started).memory
      (globalCell 1 (address 1 row tid neox true)) = some (input 1 (address 1 row tid neox true))
    rw [query_sequence_other_buffer ops input neox row tid t 4 1 _ started (by decide)]
    exact hk true
  have cb := cache_bounds p row tid hr
  rewrite [lane_start_cycle p neox ops row tid t (extra + 118) s hr ht hthread hp]
  rewrite [query_sequence_cycle p neox ops input row tid t started hr ht
    startReady.1 startReady.2.1 startReady.2.2 hcacheStart hqueryStart 4 (by decide) (extra + 26)]
  change runLane ops (layout p) (geometry p) (program neox) t (extra + 26) q =
    runLane ops (layout p) (geometry p) (program neox) t extra (laneFinished ops input neox row tid t s)
  rewrite [query_exit_cycle p neox ops tid t (extra + 24) q ht co.2 qReady.1 (by simpa using qReady.2.2)]
  change runLane ops (layout p) (geometry p) (program neox) t (extra + 24) ks =
    runLane ops (layout p) (geometry p) (program neox) t extra (laneFinished ops input neox row tid t s)
  rewrite [key_round_cycle p neox ops input row tid t (extra + 1) ks hr ht ksReady.1 ksReady.2.1 ksReady.2.2
    (hcacheKey _ cb.1) (hcacheKey _ cb.2) hx hy]
  change runLane ops (layout p) (geometry p) (program neox) t (extra + 1) k =
    runLane ops (layout p) (geometry p) (program neox) t extra (advance k t 49)
  exact key_exit_cycle p neox ops tid t extra k kReady.1 kReady.2.2

theorem lane_execution (p : Shape) (neox : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid t : Nat) (s : State α) (hr : row < p.rows) (ht : tid < 512)
    (hthread : t = row * 512 + tid) (hp : s.pc t = 0)
    (hc : CacheReads p input s) (hq : QueryInputs input neox row tid s)
    (hk : KeyInputs input neox row tid s) :
    runLane ops (layout p) (geometry p) (program neox) t fuel.lane s =
      some (laneFinished ops input neox row tid t s) := by
  change runLane ops (layout p) (geometry p) (program neox) t 256 s =
    some (laneFinished ops input neox row tid t s)
  rewrite [lane_cycle p neox ops input row tid t 136 s hr ht hthread hp hc hq hk]
  exact halted_lane p neox ops t 135 (laneFinished ops input neox row tid t s)
    (by simp [laneFinished, advance])

#print axioms lane_cycle
#print axioms lane_execution
end LarkNativeRope
