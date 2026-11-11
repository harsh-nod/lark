import Lark.NativeAttentionQueryFold

/-! A full native block query phase and actual resume at the source's PC 87. -/
namespace LarkNativeAttention
open LarkNonlinear
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def queryBlock (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (key b : Nat)
    (old : Nat → Nat → QueryValue α) (s : State α) : State α := queryFold ops input key old (blockThreads (geometry p) b) s
def queryResumed (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (key b : Nat)
    (old : Nat → Nat → QueryValue α) (s : State α) : State α := resume (blockThreads (geometry p) b) .block (queryBlock p ops input key b old s)
theorem query_resumed_state (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (key b : Nat)
    (old : Nat → Nat → QueryValue α) (s : State α) :
    queryResumed p ops input key b old s = resume (blockThreads (geometry p) b) .block (queryBlock p ops input key b old s) := rfl

theorem converged_query_block (ts : List Nat) (s : State α) (hne : ts ≠ [])
    (hp : ∀ t ∈ ts, s.pc t = 87) : converged program ts s = some .block := by
  cases ts with
  | nil => contradiction
  | cons t ts =>
      have ht := hp t (by simp)
      have hall : (t :: ts).all (fun u => s.pc u == s.pc t) = true := by
        apply List.all_eq_true.mpr
        intro u hu
        simp [hp u hu, ht]
      have hall' : (t :: ts).all (fun u => s.pc u == 87) = true := by simpa [ht] using hall
      simp only [converged, List.head?_cons, bind, pure, Option.bind, hall, ↓reduceIte, parked, ht, hall']
      rfl

theorem query_block_cut (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (key b : Nat)
    (old : Nat → Nat → QueryValue α) (s : State α) (hr : Reads p input s)
    (ready : ∀ t ∈ blockThreads (geometry p) b, QueryLaneReady p ops input t key (old t) s) :
    converged program (blockThreads (geometry p) b) (queryBlock p ops input key b old s) = some .block := by
  apply converged_query_block _ _ (block_nonempty p b)
  intro t ht
  exact (query_fold_member p ops input key old _ t s (block_nodup p b) hr ready ht).1

theorem query_block_warp (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (key b : Nat)
    (old : Nat → Nat → QueryValue α) (s : State α) (hr : Reads p input s)
    (ready : ∀ t ∈ blockThreads (geometry p) b, QueryLaneReady p ops input t key (old t) s) :
    runWarp ops (layout p) (geometry p) fuel program (warpThreads (geometry p) b 0) fuel.warp s =
      some (queryBlock p ops input key b old s) := by
  have hf := query_fold_run p ops input key old (blockThreads (geometry p) b) s (block_nodup p b) hr ready
  rw [native_warp_threads]
  change runWarp ops (layout p) (geometry p) fuel program (blockThreads (geometry p) b) 1 s = _
  rw [runWarp, hf]
  simp only [bind, Option.some_bind]
  have hc := query_block_cut p ops input key b old s hr ready
  change converged program (blockThreads (geometry p) b) (queryFold ops input key old (blockThreads (geometry p) b) s) = some .block at hc
  rw [hc]
  rfl

theorem query_block_fold_run (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (key b : Nat)
    (old : Nat → Nat → QueryValue α) (s : State α) (hr : Reads p input s)
    (ready : ∀ t ∈ blockThreads (geometry p) b, QueryLaneReady p ops input t key (old t) s) :
    (List.range (((geometry p).block + (geometry p).warp - 1) / (geometry p).warp)).foldlM
      (fun s w => runWarp ops (layout p) (geometry p) fuel program (warpThreads (geometry p) b w) fuel.warp s) s =
        some (queryBlock p ops input key b old s) := by
  have hcount : ((geometry p).block + (geometry p).warp - 1) / (geometry p).warp = 1 := by change (32 + 64 - 1) / 64 = 1; decide
  rw [hcount, show List.range 1 = [0] by decide, List.foldlM_cons, query_block_warp p ops input key b old s hr ready]
  rfl

theorem query_block_step (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (key b extra : Nat)
    (old : Nat → Nat → QueryValue α) (s : State α) (hr : Reads p input s)
    (ready : ∀ t ∈ blockThreads (geometry p) b, QueryLaneReady p ops input t key (old t) s) :
    runBlock ops (layout p) (geometry p) fuel program b (extra + 1) s =
      runBlock ops (layout p) (geometry p) fuel program b extra (queryResumed p ops input key b old s) := by
  have hf := query_block_fold_run p ops input key b old s hr ready
  rw [runBlock, hf]
  simp only [bind, Option.some_bind]
  rw [query_block_cut p ops input key b old s hr ready]
  rfl

theorem query_resumed_pc (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (key b t : Nat)
    (old : Nat → Nat → QueryValue α) (s : State α) (hr : Reads p input s)
    (ready : ∀ u ∈ blockThreads (geometry p) b, QueryLaneReady p ops input u key (old u) s)
    (ht : t ∈ blockThreads (geometry p) b) : (queryResumed p ops input key b old s).pc t = 88 := by
  have hp := (query_fold_member p ops input key old _ t s (block_nodup p b) hr ready ht).1
  change (if (blockThreads (geometry p) b).contains t then (queryBlock p ops input key b old s).pc t + 1
    else (queryBlock p ops input key b old s).pc t) = 88
  rw [show (blockThreads (geometry p) b).contains t = true from List.contains_iff_mem.mpr ht]
  change (queryFold ops input key old (blockThreads (geometry p) b) s).pc t + 1 = 88
  rw [hp]

theorem query_resumed_epoch (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (key b t : Nat)
    (old : Nat → Nat → QueryValue α) (s : State α) (ht : t ∈ blockThreads (geometry p) b) :
    (queryResumed p ops input key b old s).epochs t = bumpEpoch (s.epochs t) .block :=
  (congrArg (fun state : State α => state.epochs t) (query_resumed_state p ops input key b old s)).trans
    (resume_epoch_of_epochs _ (queryBlock p ops input key b old s) t .block s.epochs
      (query_fold_epochs ops input key old _ s) ht)

theorem query_resumed_member (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (key b t : Nat)
    (old : Nat → Nat → QueryValue α) (s : State α) (hr : Reads p input s)
    (ready : ∀ u ∈ blockThreads (geometry p) b, QueryLaneReady p ops input u key (old u) s)
    (ht : t ∈ blockThreads (geometry p) b) : NativeIndices t (queryResumed p ops input key b old s) ∧
      (queryResumed p ops input key b old s).indices t 5 = some (key : Int) := by
  have hf := (query_fold_member p ops input key old _ t s (block_nodup p b) hr ready ht).2
  have hn := resume_native_of (blockThreads (geometry p) b) .block t (queryBlock p ops input key b old s) hf.1
  have hi : (resume (blockThreads (geometry p) b) .block (queryBlock p ops input key b old s)).indices t 5 = some (key : Int) := hf.2
  exact ⟨Eq.mpr (congrArg (NativeIndices t) (query_resumed_state p ops input key b old s)) hn,
    (congrArg (fun state : State α => state.indices t 5) (query_resumed_state p ops input key b old s)).trans hi⟩

theorem query_resumed_value (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (key b t qi col : Nat)
    (old : Nat → Nat → QueryValue α) (s : State α) (ht : t ∈ blockThreads (geometry p) b) (hi : qi < 4) (hc : col < 256) :
    (queryResumed p ops input key b old s).memory (globalCell 0 (globalAddress t qi col)) =
      some ((nextQueryValue ops input t qi key (old t qi)).stored col) :=
  (congrArg (fun state : State α => state.memory (globalCell 0 (globalAddress t qi col))) (query_resumed_state p ops input key b old s)).trans
    ((resume_memory_of _ .block _ _).trans (query_fold_value ops input key old _ t qi col s (block_nodup p b) ht hi hc))

theorem query_resumed_private (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (key b t qi : Nat)
    (old : Nat → Nat → QueryValue α) (s : State α) (ht : t ∈ blockThreads (geometry p) b) (hi : qi < 4) :
    (queryResumed p ops input key b old s).memory (privateCell t 0 qi) = some (nextQueryValue ops input t qi key (old t qi)).maximum ∧
    (queryResumed p ops input key b old s).memory (privateCell t 1 qi) = some (nextQueryValue ops input t qi key (old t qi)).mass := by
  have hf := query_fold_private ops input key old _ t qi s (block_nodup p b) ht hi
  have hs := query_resumed_state p ops input key b old s
  exact ⟨(congrArg (fun state : State α => state.memory (privateCell t 0 qi)) hs).trans ((resume_memory_of _ .block _ _).trans hf.1),
    (congrArg (fun state : State α => state.memory (privateCell t 1 qi)) hs).trans ((resume_memory_of _ .block _ _).trans hf.2)⟩

theorem query_resumed_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (key b : Nat)
    (old : Nat → Nat → QueryValue α) (s : State α) (hr : Reads p input s) : Reads p input (queryResumed p ops input key b old s) :=
  Eq.mpr (congrArg (Reads p input) (query_resumed_state p ops input key b old s))
    (resume_reads_of p input _ .block _ (query_fold_reads p ops input key old _ s hr))

theorem query_resumed_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (key b : Nat)
    (old : Nat → Nat → QueryValue α) (s : State α)
    (he : ∀ t ∈ blockThreads (geometry p) b, (s.epochs t).block % 2 = 1) (hg : TraceGood s) :
    TraceGood (queryResumed p ops input key b old s) :=
  Eq.mpr (congrArg TraceGood (query_resumed_state p ops input key b old s))
    (resume_good_of _ .block _ (query_fold_good ops input key old _ s he hg))

#print axioms query_block_warp
#print axioms query_block_step
#print axioms query_resumed_pc
#print axioms query_resumed_epoch
#print axioms query_resumed_member
#print axioms query_resumed_value
#print axioms query_resumed_private
#print axioms query_resumed_reads
#print axioms query_resumed_good
end LarkNativeAttention
