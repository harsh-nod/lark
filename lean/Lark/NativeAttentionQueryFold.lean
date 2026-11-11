import Lark.NativeAttentionQueryTileFrame

/-! The unchanged scheduler's scalar lane fold for a complete key-tile phase. -/
namespace LarkNativeAttention
open LarkNonlinear
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def queryFold (ops : Ops α) (input : Nat → Nat → α) (key : Nat) (old : Nat → Nat → QueryValue α)
    (ts : List Nat) (s : State α) : State α := ts.foldl (fun s t => queryTile ops input t key (old t) s) s

theorem query_fold_epochs (ops : Ops α) (input : Nat → Nat → α) (key : Nat) (old : Nat → Nat → QueryValue α)
    (ts : List Nat) (s : State α) : (queryFold ops input key old ts s).epochs = s.epochs := by
  induction ts generalizing s with
  | nil => rfl
  | cons t ts ih => exact (ih (queryTile ops input t key (old t) s)).trans (query_tile_fields ops input t key (old t) s).2

theorem query_fold_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (key : Nat) (old : Nat → Nat → QueryValue α)
    (ts : List Nat) (s : State α) (hr : Reads p input s) : Reads p input (queryFold ops input key old ts s) := by
  induction ts generalizing s with
  | nil => exact hr
  | cons t ts ih => exact ih _ (query_tile_reads p ops input t key (old t) s hr)

theorem query_fold_tail_ready (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (key t : Nat) (old : Nat → Nat → QueryValue α)
    (ts : List Nat) (s : State α) (hn : (t :: ts).Nodup) (hr : Reads p input s)
    (ready : ∀ u ∈ t :: ts, QueryLaneReady p ops input u key (old u) s) :
    ∀ u ∈ ts, QueryLaneReady p ops input u key (old u) (queryTile ops input t key (old t) s) := by
  intro u hu
  exact query_tile_ready_other p ops input t key u (old t) (old u) s
    (by intro he; subst u; exact (List.nodup_cons.mp hn).1 hu) hr (ready t (by simp)) (ready u (by simp [hu]))

theorem query_fold_run (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (key : Nat) (old : Nat → Nat → QueryValue α)
    (ts : List Nat) (s : State α) (hn : ts.Nodup) (hr : Reads p input s)
    (ready : ∀ t ∈ ts, QueryLaneReady p ops input t key (old t) s) :
    ts.foldlM (fun s t => runLane ops (layout p) (geometry p) program t fuel.lane s) s = some (queryFold ops input key old ts s) := by
  induction ts generalizing s with
  | nil => rfl
  | cons t ts ih =>
      have ht := ready t (by simp)
      rw [List.foldlM_cons, query_tile_run p ops input t key (old t) s ht.bound hr ht.native ht.tiles ht.keyIndex ht.values ht.pc]
      simp only [bind, Option.some_bind]
      exact ih _ (List.nodup_cons.mp hn).2 (query_tile_reads p ops input t key (old t) s hr)
        (query_fold_tail_ready p ops input key t old ts s hn hr ready)

theorem query_fold_other (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (key : Nat) (old : Nat → Nat → QueryValue α)
    (ts : List Nat) (u : Nat) (s : State α) (hn : ts.Nodup) (hr : Reads p input s)
    (ready : ∀ t ∈ ts, QueryLaneReady p ops input t key (old t) s) (hu : u ∉ ts) :
    (queryFold ops input key old ts s).pc u = s.pc u ∧ (queryFold ops input key old ts s).indices u = s.indices u ∧
    (queryFold ops input key old ts s).regs u = s.regs u := by
  induction ts generalizing s with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons t ts ih =>
      have hf := query_tile_control_other p ops input t key u (old t) s
        (by intro he; exact hu (by simp [he])) hr (ready t (by simp))
      have ht := ih (queryTile ops input t key (old t) s) (List.nodup_cons.mp hn).2
        (query_tile_reads p ops input t key (old t) s hr) (query_fold_tail_ready p ops input key t old ts s hn hr ready)
        (by intro hm; exact hu (by simp [hm]))
      exact ⟨ht.1.trans hf.1, ht.2.1.trans hf.2.1, ht.2.2.trans hf.2.2⟩

theorem query_fold_member (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (key : Nat) (old : Nat → Nat → QueryValue α)
    (ts : List Nat) (u : Nat) (s : State α) (hn : ts.Nodup) (hr : Reads p input s)
    (ready : ∀ t ∈ ts, QueryLaneReady p ops input t key (old t) s) (hu : u ∈ ts) :
    (queryFold ops input key old ts s).pc u = 87 ∧ NativeIndices u (queryFold ops input key old ts s) ∧
    (queryFold ops input key old ts s).indices u 5 = some (key : Int) := by
  induction ts generalizing s with
  | nil => simp at hu
  | cons t ts ih =>
      have tailReady := query_fold_tail_ready p ops input key t old ts s hn hr ready
      have reads := query_tile_reads p ops input t key (old t) s hr
      rcases List.mem_cons.mp hu with he | hm
      · subst u
        have hf := query_fold_other p ops input key old ts t (queryTile ops input t key (old t) s)
          (List.nodup_cons.mp hn).2 reads tailReady (List.nodup_cons.mp hn).1
        have ht := ready t (by simp)
        refine ⟨hf.1.trans (query_tile_fields ops input t key (old t) s).1, ?_,
          (congrArg (fun indices => indices 5) hf.2.1).trans ((query_tile_key ops input t key (old t) s).trans ht.keyIndex)⟩
        change NativeIndices t (queryFold ops input key old ts (queryTile ops input t key (old t) s))
        simpa only [NativeIndices, hf.2.1] using query_tile_native ops input t key (old t) s ht.native
      · exact ih (queryTile ops input t key (old t) s) (List.nodup_cons.mp hn).2 reads tailReady hm

theorem query_fold_output_other (ops : Ops α) (input : Nat → Nat → α) (key : Nat) (old : Nat → Nat → QueryValue α)
    (ts : List Nat) (offset : Nat) (s : State α) (ho : writer offset ∉ ts) :
    (queryFold ops input key old ts s).memory (globalCell 0 offset) = s.memory (globalCell 0 offset) := by
  induction ts generalizing s with
  | nil => rfl
  | cons t ts ih =>
      exact (ih (queryTile ops input t key (old t) s) (by intro hm; exact ho (by simp [hm]))).trans
        (query_tile_output_other ops input t key offset (old t) s (by intro he; exact ho (by simp [he])))

theorem query_fold_private_other (ops : Ops α) (input : Nat → Nat → α) (key : Nat) (old : Nat → Nat → QueryValue α)
    (ts : List Nat) (u buffer qi : Nat) (s : State α) (hu : u ∉ ts) :
    (queryFold ops input key old ts s).memory (privateCell u buffer qi) = s.memory (privateCell u buffer qi) := by
  induction ts generalizing s with
  | nil => rfl
  | cons t ts ih =>
      exact (ih (queryTile ops input t key (old t) s) (by intro hm; exact hu (by simp [hm]))).trans
        (query_tile_private_other ops input t key u buffer qi (old t) s (by intro he; exact hu (by simp [he])))

theorem query_fold_value (ops : Ops α) (input : Nat → Nat → α) (key : Nat) (old : Nat → Nat → QueryValue α)
    (ts : List Nat) (t qi col : Nat) (s : State α) (hn : ts.Nodup) (ht : t ∈ ts) (hi : qi < 4) (hc : col < 256) :
    (queryFold ops input key old ts s).memory (globalCell 0 (globalAddress t qi col)) =
      some ((nextQueryValue ops input t qi key (old t qi)).stored col) := by
  induction ts generalizing s with
  | nil => simp at ht
  | cons u ts ih =>
      rcases List.mem_cons.mp ht with he | hm
      · subst t
        exact (query_fold_output_other ops input key old ts (globalAddress u qi col) (queryTile ops input u key (old u) s)
          (by simpa only [global_address_owner u qi col hi hc] using (List.nodup_cons.mp hn).1)).trans
          (query_tile_value ops input u key qi col (old u) s hi hc)
      · exact ih (queryTile ops input u key (old u) s) (List.nodup_cons.mp hn).2 hm

theorem query_fold_private (ops : Ops α) (input : Nat → Nat → α) (key : Nat) (old : Nat → Nat → QueryValue α)
    (ts : List Nat) (t qi : Nat) (s : State α) (hn : ts.Nodup) (ht : t ∈ ts) (hi : qi < 4) :
    (queryFold ops input key old ts s).memory (privateCell t 0 qi) = some (nextQueryValue ops input t qi key (old t qi)).maximum ∧
    (queryFold ops input key old ts s).memory (privateCell t 1 qi) = some (nextQueryValue ops input t qi key (old t qi)).mass := by
  induction ts generalizing s with
  | nil => simp at ht
  | cons u ts ih =>
      rcases List.mem_cons.mp ht with he | hm
      · subst t
        have hf := query_tile_private ops input u key qi (old u) s hi
        exact ⟨(query_fold_private_other ops input key old ts u 0 qi (queryTile ops input u key (old u) s) (List.nodup_cons.mp hn).1).trans hf.1,
          (query_fold_private_other ops input key old ts u 1 qi (queryTile ops input u key (old u) s) (List.nodup_cons.mp hn).1).trans hf.2⟩
      · exact ih (queryTile ops input u key (old u) s) (List.nodup_cons.mp hn).2 hm

theorem query_fold_tiles (ops : Ops α) (input : Nat → Nat → α) (key : Nat) (old : Nat → Nat → QueryValue α)
    (ts : List Nat) (u : Nat) (s : State α) (hk : Tiles ops input u key s) : Tiles ops input u key (queryFold ops input key old ts s) := by
  induction ts generalizing s with
  | nil => exact hk
  | cons t ts ih => exact ih _ (query_tile_tiles_other ops input t key u (old t) s hk)

theorem query_fold_good (ops : Ops α) (input : Nat → Nat → α) (key : Nat) (old : Nat → Nat → QueryValue α)
    (ts : List Nat) (s : State α) (he : ∀ t ∈ ts, (s.epochs t).block % 2 = 1) (hg : TraceGood s) :
    TraceGood (queryFold ops input key old ts s) := by
  induction ts generalizing s with
  | nil => exact hg
  | cons t ts ih =>
      exact ih _ (by intro u hu; rw [(query_tile_fields ops input t key (old t) s).2]; exact he u (by simp [hu]))
        (query_tile_good ops input t key (old t) s (he t (by simp)) hg)

#print axioms query_fold_run
#print axioms query_fold_member
#print axioms query_fold_value
#print axioms query_fold_private
#print axioms query_fold_reads
#print axioms query_fold_tiles
#print axioms query_fold_good
end LarkNativeAttention
