import Lark.NativeAttentionNextFold

/-! Actual subsequent K/V block-copy phase and resume to the query entry. -/
namespace LarkNativeAttention
open LarkNonlinear
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def nextBlock (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (key b : Nat) (s : State α) : State α :=
  nextFold ops input key (blockThreads (geometry p) b) s
def nextResumed (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (key b : Nat) (s : State α) : State α :=
  resume (blockThreads (geometry p) b) .block (nextBlock p ops input key b s)
theorem next_resumed_state (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (key b : Nat) (s : State α) :
    nextResumed p ops input key b s = resume (blockThreads (geometry p) b) .block (nextBlock p ops input key b s) := rfl

theorem next_block_cut (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (key b : Nat) (s : State α)
    (ready : ∀ t ∈ blockThreads (geometry p) b, CopyLaneReady p t key s) :
    converged program (blockThreads (geometry p) b) (nextBlock p ops input key b s) = some .block := by
  apply converged_block _ _ (block_nonempty p b)
  intro t ht
  exact (next_fold_member ops input key _ t s (block_nodup p b) ht (by intro u hu; exact (ready u hu).native)).1

theorem next_block_warp (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (key b : Nat) (s : State α)
    (hk : key + 1 < 4) (hr : Reads p input s) (ready : ∀ t ∈ blockThreads (geometry p) b, CopyLaneReady p t key s) :
    runWarp ops (layout p) (geometry p) fuel program (warpThreads (geometry p) b 0) fuel.warp s = some (nextBlock p ops input key b s) := by
  have hf := next_fold_run p ops input key (blockThreads (geometry p) b) s hk (block_nodup p b) hr ready
  rw [native_warp_threads]
  change runWarp ops (layout p) (geometry p) fuel program (blockThreads (geometry p) b) 1 s = _
  rw [runWarp, hf]
  simp only [bind, Option.some_bind]
  have hc := next_block_cut p ops input key b s ready
  change converged program (blockThreads (geometry p) b) (nextFold ops input key (blockThreads (geometry p) b) s) = some .block at hc
  rw [hc]
  rfl

theorem next_block_fold_run (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (key b : Nat) (s : State α)
    (hk : key + 1 < 4) (hr : Reads p input s) (ready : ∀ t ∈ blockThreads (geometry p) b, CopyLaneReady p t key s) :
    (List.range (((geometry p).block + (geometry p).warp - 1) / (geometry p).warp)).foldlM
      (fun s w => runWarp ops (layout p) (geometry p) fuel program (warpThreads (geometry p) b w) fuel.warp s) s =
        some (nextBlock p ops input key b s) := by
  have hcount : ((geometry p).block + (geometry p).warp - 1) / (geometry p).warp = 1 := by change (32 + 64 - 1) / 64 = 1; decide
  rw [hcount, show List.range 1 = [0] by decide, List.foldlM_cons, next_block_warp p ops input key b s hk hr ready]
  rfl

theorem next_block_step (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (key b extra : Nat) (s : State α)
    (hk : key + 1 < 4) (hr : Reads p input s) (ready : ∀ t ∈ blockThreads (geometry p) b, CopyLaneReady p t key s) :
    runBlock ops (layout p) (geometry p) fuel program b (extra + 1) s =
      runBlock ops (layout p) (geometry p) fuel program b extra (nextResumed p ops input key b s) := by
  have hf := next_block_fold_run p ops input key b s hk hr ready
  rw [runBlock, hf]
  simp only [bind, Option.some_bind]
  rw [next_block_cut p ops input key b s ready]
  rfl

theorem next_resumed_pc (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (key b t : Nat) (s : State α)
    (ready : ∀ u ∈ blockThreads (geometry p) b, CopyLaneReady p u key s) (ht : t ∈ blockThreads (geometry p) b) :
    (nextResumed p ops input key b s).pc t = 21 := by
  have hp := (next_fold_member ops input key _ t s (block_nodup p b) ht (by intro u hu; exact (ready u hu).native)).1
  change (if (blockThreads (geometry p) b).contains t then (nextBlock p ops input key b s).pc t + 1
    else (nextBlock p ops input key b s).pc t) = 21
  rw [show (blockThreads (geometry p) b).contains t = true from List.contains_iff_mem.mpr ht]
  change (nextFold ops input key (blockThreads (geometry p) b) s).pc t + 1 = 21
  rw [hp]

theorem next_resumed_member (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (key b t : Nat) (s : State α)
    (ready : ∀ u ∈ blockThreads (geometry p) b, CopyLaneReady p u key s) (ht : t ∈ blockThreads (geometry p) b) :
    NativeIndices t (nextResumed p ops input key b s) ∧ (nextResumed p ops input key b s).indices t 5 = some ((key + 1 : Nat) : Int) := by
  have hf := (next_fold_member ops input key _ t s (block_nodup p b) ht (by intro u hu; exact (ready u hu).native)).2
  have hn := resume_native_of (blockThreads (geometry p) b) .block t (nextBlock p ops input key b s) hf.1
  have hi : (resume (blockThreads (geometry p) b) .block (nextBlock p ops input key b s)).indices t 5 = some ((key + 1 : Nat) : Int) := hf.2
  exact ⟨Eq.mpr (congrArg (NativeIndices t) (next_resumed_state p ops input key b s)) hn,
    (congrArg (fun state : State α => state.indices t 5) (next_resumed_state p ops input key b s)).trans hi⟩

theorem next_resumed_epoch (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (key b t : Nat) (s : State α)
    (ht : t ∈ blockThreads (geometry p) b) : (nextResumed p ops input key b s).epochs t = bumpEpoch (s.epochs t) .block :=
  (congrArg (fun state : State α => state.epochs t) (next_resumed_state p ops input key b s)).trans
    (resume_epoch_of_epochs _ (nextBlock p ops input key b s) t .block s.epochs (next_fold_epochs ops input key _ s) ht)

theorem next_resumed_memory_other (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (key b : Nat)
    (s : State α) (l : Location) (hl : l.space ≠ .shared) : (nextResumed p ops input key b s).memory l = s.memory l :=
  (congrArg (fun state : State α => state.memory l) (next_resumed_state p ops input key b s)).trans
    ((resume_memory_of _ .block _ l).trans
      (next_fold_memory_other ops input key _ s l (by intro t ht c hc; constructor <;> intro he <;> exact hl (congrArg Location.space he))))

theorem next_resumed_queries (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (key b t wanted start stop : Nat)
    (old : Nat → QueryValue α) (s : State α) (ho : QueriesRange t wanted old start stop s) :
    QueriesRange t wanted old start stop (nextResumed p ops input key b s) := by
  intro qi hq hi
  constructor
  · intro col hc hb
    exact (next_resumed_memory_other p ops input key b s (globalCell 0 (globalAddress t qi col)) (by simp [globalCell])).trans ((ho qi hq hi).1 col hc hb)
  · intro hj
    exact ⟨(next_resumed_memory_other p ops input key b s (privateCell t 0 qi) (by simp [privateCell])).trans ((ho qi hq hi).2 hj).1,
      (next_resumed_memory_other p ops input key b s (privateCell t 1 qi) (by simp [privateCell])).trans ((ho qi hq hi).2 hj).2⟩

theorem next_resumed_tiles (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (key b t : Nat)
    (s : State α) (ht : t ∈ blockThreads (geometry p) b) : Tiles ops input t (key + 1) (nextResumed p ops input key b s) := by
  obtain ⟨lane, hl, he⟩ := (block_mem p b t).mp ht
  have ho : t / 32 = b := by omega
  intro buffer hb row hr col hc
  have hm : peer t row ∈ blockThreads (geometry p) b := (block_mem p b _).mpr ⟨row, hr, by simp [peer, ho]⟩
  have hv := next_fold_tile ops input key (blockThreads (geometry p) b) (peer t row) buffer col s (block_nodup p b) hm hb hc
  have hv' : (nextBlock p ops input key b s).memory (sharedCell t buffer (row * 256 + col)) =
      some (ops.fromHalf (input (buffer + 1) (tileAddress t (key + 1) row col))) := by
    simpa only [peer_shared t buffer row col hr, peer_global t (key + 1) row col hr] using hv
  exact (congrArg (fun state : State α => state.memory (sharedCell t buffer (row * 256 + col)))
    (next_resumed_state p ops input key b s)).trans ((resume_memory_of _ .block _ _).trans hv')

theorem next_resumed_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (key b : Nat)
    (s : State α) (hr : Reads p input s) : Reads p input (nextResumed p ops input key b s) :=
  Eq.mpr (congrArg (Reads p input) (next_resumed_state p ops input key b s))
    (resume_reads_of p input _ .block _ (next_fold_reads p ops input key _ s hr))

theorem next_resumed_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (key b : Nat) (s : State α)
    (he : ∀ t ∈ blockThreads (geometry p) b, (s.epochs t).block % 2 = 0) (hg : TraceGood s) :
    TraceGood (nextResumed p ops input key b s) :=
  Eq.mpr (congrArg TraceGood (next_resumed_state p ops input key b s))
    (resume_good_of _ .block _ (next_fold_good ops input key _ s he hg))

#print axioms next_block_warp
#print axioms next_block_step
#print axioms next_resumed_pc
#print axioms next_resumed_epoch
#print axioms next_resumed_queries
#print axioms next_resumed_tiles
#print axioms next_resumed_good
end LarkNativeAttention
