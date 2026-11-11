import Lark.NativeAttentionQueryPrepare

/-! Value predicates for the actual shared tiles, and first-query entry. -/
namespace LarkNativeAttention
open LarkNonlinear
open LarkReduction (setIndex execute_index_of)
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def peer (t row : Nat) : Nat := t / 32 * 32 + row
def tileAddress (t tile row col : Nat) : Nat := t / 32 * 32768 + tile * 8192 + row * 256 + col

def Tiles (ops : Ops α) (input : Nat → Nat → α) (t tile : Nat) (s : State α) : Prop :=
  ∀ buffer, buffer = 1 ∨ buffer = 2 → ∀ row, row < 32 → ∀ col, col < 256 →
    s.memory (sharedCell t buffer (row * 256 + col)) =
      some (ops.fromHalf (input (buffer + 1) (tileAddress t tile row col)))

def QiReady (ops : Ops α) (input : Nat → Nat → α) (t tile : Nat) (s : State α) : Prop :=
  ∀ col, col < 256 → s.memory (sharedCell t 0 (sharedAddress t col)) =
    some (ops.fromHalf (input 1 (globalAddress t tile col)))

theorem qi_of_memory (ops : Ops α) (input : Nat → Nat → α) (t tile : Nat) (s next : State α)
    (hq : QiReady ops input t tile s) (hm : next.memory = s.memory) : QiReady ops input t tile next := by
  intro col hc
  rw [hm]
  exact hq col hc

theorem tiles_of_memory (ops : Ops α) (input : Nat → Nat → α) (t tile : Nat) (s next : State α)
    (hk : Tiles ops input t tile s) (hm : next.memory = s.memory) : Tiles ops input t tile next := by
  intro buffer hb row hr col hc
  rw [hm]
  exact hk buffer hb row hr col hc

theorem reads_of_memory (p : Shape) (input : Nat → Nat → α) (s next : State α)
    (hr : Reads p input s) (hm : next.memory = s.memory) : Reads p input next := by
  intro b hb i hi
  rw [hm]
  exact hr b hb i hi

theorem peer_global (t tile row col : Nat) (hr : row < 32) :
    globalAddress (peer t row) tile col = tileAddress t tile row col := by
  have ho : peer t row / 32 = t / 32 := by unfold peer; omega
  have hl : peer t row % 32 = row := by unfold peer; omega
  simp [globalAddress, tileAddress, ho, hl]

theorem peer_shared (t buffer row col : Nat) (hr : row < 32) :
    sharedCell (peer t row) buffer (sharedAddress (peer t row) col) =
      sharedCell t buffer (row * 256 + col) := by
  have ho : peer t row / 32 = t / 32 := by unfold peer; omega
  have hl : peer t row % 32 = row := by unfold peer; omega
  simp [sharedCell, sharedAddress, ho, hl]

theorem first_resumed_tiles (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (b t : Nat) (s : State α) (ht : t ∈ blockThreads (geometry p) b) :
    Tiles ops input t 0 (firstResumed p ops input b s) := by
  obtain ⟨lane, hl, he⟩ := (block_mem p b t).mp ht
  have ho : t / 32 = b := by omega
  intro buffer hb row hr col hc
  have hm : peer t row ∈ blockThreads (geometry p) b :=
    (block_mem p b _).mpr ⟨row, hr, by simp [peer, ho]⟩
  have h := first_resumed_tile p ops input b (peer t row) buffer col s hm hb hc
  simpa only [peer_shared t buffer row col hr, peer_global t 0 row col hr] using h

theorem query_prepared_qi (ops : Ops α) (input : Nat → Nat → α) (t tile : Nat) (s : State α) :
    QiReady ops input t tile (queryPrepared ops input t tile s) := by
  intro col hc
  exact query_prepared_value ops input t tile col s hc

theorem query_prepared_tiles (ops : Ops α) (input : Nat → Nat → α) (t tile keyTile : Nat)
    (s : State α) (ht : Tiles ops input t keyTile s) : Tiles ops input t keyTile (queryPrepared ops input t tile s) := by
  intro buffer hb row hr col hc
  have hf := query_prepared_memory_other ops input t tile s (sharedCell t buffer (row * 256 + col))
    (by intro c hbound; rcases hb with rfl | rfl <;> simp [sharedCell])
  exact hf.trans (ht buffer hb row hr col hc)

def firstQuery (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) : State α :=
  queryPrepared ops input t 0 (setIndex s t 7 0 22)

theorem first_query_state (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) :
    firstQuery ops input t s = queryPrepared ops input t 0 (setIndex s t 7 0 22) := rfl

theorem first_query_fields (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) :
    (firstQuery ops input t s).pc t = 30 ∧ (firstQuery ops input t s).indices t 9 = some 0 ∧
    (firstQuery ops input t s).regs t 0 = some (ops.literal 0 1) ∧ (firstQuery ops input t s).epochs = s.epochs := by
  have hs := first_query_state ops input t s
  have h := query_prepared_fields ops input t 0 (setIndex s t 7 0 22)
  exact ⟨(congrArg (fun state : State α => state.pc t) hs).trans h.1,
    (congrArg (fun state : State α => state.indices t 9) hs).trans h.2.1,
    (congrArg (fun state : State α => state.regs t 0) hs).trans h.2.2.1,
    (congrArg (fun state : State α => state.epochs) hs).trans h.2.2.2⟩

theorem first_query_native (ops : Ops α) (input : Nat → Nat → α) (t : Nat)
    (s : State α) (hn : NativeIndices t s) : NativeIndices t (firstQuery ops input t s) :=
  Eq.mpr (congrArg (NativeIndices t) (first_query_state ops input t s))
    (query_prepared_native ops input t 0 (setIndex s t 7 0 22) (indices_set s t 7 22 0 (by decide) hn))

theorem first_query_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (t : Nat)
    (s : State α) (hr : Reads p input s) : Reads p input (firstQuery ops input t s) :=
  Eq.mpr (congrArg (Reads p input) (first_query_state ops input t s))
    (query_prepared_reads p ops input t 0 (setIndex s t 7 0 22) hr)

theorem first_query_good (ops : Ops α) (input : Nat → Nat → α) (t : Nat)
    (s : State α) (hg : TraceGood s) : TraceGood (firstQuery ops input t s) :=
  Eq.mpr (congrArg TraceGood (first_query_state ops input t s))
    (query_prepared_good ops input t 0 (setIndex s t 7 0 22) hg)

theorem first_query_eq (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t extra : Nat) (s : State α) (ht : t < p.groups * 32) (hr : Reads p input s)
    (hn : NativeIndices t s) (hp : s.pc t = 21) :
    runLane ops (layout p) (geometry p) program t (extra + 1030) s =
      runLane ops (layout p) (geometry p) program t extra (firstQuery ops input t s) := by
  let s1 := setIndex s t 7 0 22
  have he := execute_index_of ops (layout p) (geometry p) t 7 22 (.const 0) s 0 (by rfl) (by omega)
  have h1 := source_step p ops t 21 (extra + 1029) _ s s1 (by rfl) hp he
  have h2 := query_prepare_eq p ops input t 0 extra s1 ht (by decide) hr
    (indices_set s t 7 22 0 (by decide) hn)
    (by simp [s1, setIndex, advance]) (by simp [s1, setIndex, advance])
  exact h1.trans h2

theorem first_query_qi (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) :
    QiReady ops input t 0 (firstQuery ops input t s) := query_prepared_qi ops input t 0 _

theorem first_query_tiles (ops : Ops α) (input : Nat → Nat → α) (t keyTile : Nat)
    (s : State α) (ht : Tiles ops input t keyTile s) : Tiles ops input t keyTile (firstQuery ops input t s) :=
  query_prepared_tiles ops input t 0 keyTile (setIndex s t 7 0 22) ht

theorem first_query_from_resumed (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (b t extra : Nat) (s : State α) (hb : b < p.groups) (ht : t ∈ blockThreads (geometry p) b)
    (hr : Reads p input s) :
    runLane ops (layout p) (geometry p) program t (extra + 1030) (firstResumed p ops input b s) =
      runLane ops (layout p) (geometry p) program t extra
        (firstQuery ops input t (firstResumed p ops input b s)) := by
  have hbound : t < p.groups * 32 := by
    obtain ⟨lane, hl, rfl⟩ := (block_mem p b t).mp ht
    omega
  exact first_query_eq p ops input t extra _ hbound (first_resumed_reads p ops input b s hr)
    (first_resumed_native p ops input b t s ht) (first_resumed_pc p ops input b t s ht)

#print axioms first_resumed_tiles
#print axioms query_prepared_tiles
#print axioms first_query_eq
#print axioms first_query_from_resumed
end LarkNativeAttention
