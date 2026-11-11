import Lark.NativeAttentionLaneFrame

/-! Control and memory frames for composing the 32 native query lanes. -/
namespace LarkNativeAttention
open LarkNonlinear
open LarkReduction (setIndex)
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem query_rows_memory_other (ops : Ops α) (input : Nat → Nat → α) (t key : Nat) (old : Nat → QueryValue α)
    (qi remaining : Nat) (s : State α) (l : Location)
    (hq : ∀ c, c < 256 → l ≠ sharedCell t 0 (sharedAddress t c))
    (hs : ∀ r, r < 32 → l ≠ sharedCell t 3 (scoreAddress t r))
    (ho : ∀ q, qi ≤ q → q < qi + remaining → ∀ c, c < 256 → l ≠ globalCell 0 (globalAddress t q c))
    (hm : ∀ q, qi ≤ q → q < qi + remaining → l ≠ privateCell t 0 q ∧ l ≠ privateCell t 1 q) :
    (queryRows ops input t key old qi remaining s).memory l = s.memory l := by
  induction remaining generalizing qi s with
  | zero => rfl
  | succ remaining ih =>
      exact (ih (qi + 1) (queryRow ops input t qi key (old qi) s)
        (by intro q hq hb; exact ho q (by omega) (by omega))
        (by intro q hq hb; exact hm q (by omega) (by omega))).trans
        (query_row_memory_other ops input t qi key (old qi) s l hq hs
          (ho qi (by omega) (by omega)) (hm qi (by omega) (by omega)).1 (hm qi (by omega) (by omega)).2)

theorem query_tile_memory_other (ops : Ops α) (input : Nat → Nat → α) (t key : Nat) (old : Nat → QueryValue α)
    (s : State α) (l : Location)
    (hq : ∀ c, c < 256 → l ≠ sharedCell t 0 (sharedAddress t c))
    (hs : ∀ r, r < 32 → l ≠ sharedCell t 3 (scoreAddress t r))
    (ho : ∀ q, q < 4 → ∀ c, c < 256 → l ≠ globalCell 0 (globalAddress t q c))
    (hm : ∀ q, q < 4 → l ≠ privateCell t 0 q ∧ l ≠ privateCell t 1 q) :
    (queryTile ops input t key old s).memory l = s.memory l :=
  (congrArg (fun state : State α => state.memory l) (query_tile_state ops input t key old s)).trans
    (query_rows_memory_other ops input t key old 0 4 (setIndex s t 7 0 22) l hq hs
      (by intro q hq hb; exact ho q hb) (by intro q hq hb; exact hm q hb))

theorem query_tile_output_other (ops : Ops α) (input : Nat → Nat → α) (t key offset : Nat) (old : Nat → QueryValue α)
    (s : State α) (hne : writer offset ≠ t) :
    (queryTile ops input t key old s).memory (globalCell 0 offset) = s.memory (globalCell 0 offset) := by
  apply query_tile_memory_other
  · intro c hc; simp [globalCell, sharedCell]
  · intro r hr; simp [globalCell, sharedCell]
  · intro q hq c hc he
    have he := congrArg Location.offset he
    change offset = globalAddress t q c at he
    exact hne ((congrArg writer he).trans (global_address_owner t q c hq hc))
  · intro q hq; simp [globalCell, privateCell]

theorem query_tile_private_other (ops : Ops α) (input : Nat → Nat → α) (t key u buffer q : Nat) (old : Nat → QueryValue α)
    (s : State α) (hne : u ≠ t) :
    (queryTile ops input t key old s).memory (privateCell u buffer q) = s.memory (privateCell u buffer q) := by
  apply query_tile_memory_other
  · intro c hc; simp [privateCell, sharedCell]
  · intro r hr; simp [privateCell, sharedCell]
  · intro q hq c hc; simp [privateCell, globalCell]
  · intro q hq; simp [privateCell, hne]

theorem query_tile_tiles_other (ops : Ops α) (input : Nat → Nat → α) (t key u : Nat) (old : Nat → QueryValue α)
    (s : State α) (hk : Tiles ops input u key s) : Tiles ops input u key (queryTile ops input t key old s) := by
  intro buffer hb row hr col hc
  have hm := query_tile_memory_other ops input t key old s (sharedCell u buffer (row * 256 + col))
    (by intro c hc; rcases hb with rfl | rfl <;> simp [sharedCell])
    (by intro r hr; rcases hb with rfl | rfl <;> simp [sharedCell])
    (by intro q hq c hc; simp [sharedCell, globalCell]) (by intro q hq; simp [sharedCell, privateCell])
  exact hm.trans (hk buffer hb row hr col hc)

theorem query_tile_old_other (ops : Ops α) (input : Nat → Nat → α) (t key u : Nat) (old other : Nat → QueryValue α)
    (s : State α) (hne : u ≠ t) (ho : QueriesRange u key other 0 4 s) :
    QueriesRange u key other 0 4 (queryTile ops input t key old s) := by
  intro qi hq hi
  constructor
  · intro col hc hb
    exact (query_tile_output_other ops input t key (globalAddress u qi col) old s
      (by simpa only [global_address_owner u qi col hi hb] using hne)).trans ((ho qi hq hi).1 col hc hb)
  · intro hj
    exact ⟨(query_tile_private_other ops input t key u 0 qi old s hne).trans ((ho qi hq hi).2 hj).1,
      (query_tile_private_other ops input t key u 1 qi old s hne).trans ((ho qi hq hi).2 hj).2⟩

theorem query_tile_native (ops : Ops α) (input : Nat → Nat → α) (t key : Nat) (old : Nat → QueryValue α)
    (s : State α) (hn : NativeIndices t s) : NativeIndices t (queryTile ops input t key old s) :=
  Eq.mpr (congrArg (NativeIndices t) (query_tile_state ops input t key old s))
    (query_rows_native ops input t key old 0 4 (setIndex s t 7 0 22) (indices_set s t 7 22 0 (by decide) hn))

theorem query_tile_key (ops : Ops α) (input : Nat → Nat → α) (t key : Nat) (old : Nat → QueryValue α) (s : State α) :
    (queryTile ops input t key old s).indices t 5 = s.indices t 5 :=
  (congrArg (fun state : State α => state.indices t 5) (query_tile_state ops input t key old s)).trans
    ((query_rows_index ops input t key old 0 4 5 (setIndex s t 7 0 22)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        (by simp [setIndex, advance]))

structure QueryLaneReady (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (t key : Nat)
    (old : Nat → QueryValue α) (s : State α) : Prop where
  bound : t < p.groups * 32
  native : NativeIndices t s
  tiles : Tiles ops input t key s
  keyIndex : s.indices t 5 = some (key : Int)
  pc : s.pc t = 21
  values : QueriesRange t key old 0 4 s

theorem query_tile_control_other (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (t key u : Nat) (old : Nat → QueryValue α)
    (s : State α) (hne : u ≠ t) (hr : Reads p input s) (ht : QueryLaneReady p ops input t key old s) :
    (queryTile ops input t key old s).pc u = s.pc u ∧ (queryTile ops input t key old s).indices u = s.indices u ∧
    (queryTile ops input t key old s).regs u = s.regs u :=
  run_lane_other ops (layout p) (geometry p) program t u fuel.lane s _ hne
    (query_tile_run p ops input t key old s ht.bound hr ht.native ht.tiles ht.keyIndex ht.values ht.pc)

theorem query_tile_ready_other (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (t key u : Nat) (old other : Nat → QueryValue α)
    (s : State α) (hne : u ≠ t) (hr : Reads p input s) (ht : QueryLaneReady p ops input t key old s)
    (hu : QueryLaneReady p ops input u key other s) : QueryLaneReady p ops input u key other (queryTile ops input t key old s) := by
  have hf := query_tile_control_other p ops input t key u old s hne hr ht
  refine ⟨hu.bound, ?_, query_tile_tiles_other ops input t key u old s hu.tiles,
    (congrArg (fun indices => indices 5) hf.2.1).trans hu.keyIndex, hf.1.trans hu.pc,
    query_tile_old_other ops input t key u old other s hne hu.values⟩
  simpa only [NativeIndices, hf.2.1] using hu.native

#print axioms query_tile_memory_other
#print axioms query_tile_old_other
#print axioms query_tile_control_other
#print axioms query_tile_ready_other
end LarkNativeAttention
