import Lark.NativeAttentionQueryRows

/-! The complete per-lane phase for one key tile, using the unchanged fuel. -/
namespace LarkNativeAttention
open LarkNonlinear
open LarkReduction (setIndex execute_index_of)
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def queryTileFuel (key : Nat) : Nat := (119062 + oldTailFuel key) * 4 + 2
def queryTile (ops : Ops α) (input : Nat → Nat → α) (t key : Nat) (old : Nat → QueryValue α) (s : State α) : State α :=
  queryRows ops input t key old 0 4 (setIndex s t 7 0 22)
theorem query_tile_state (ops : Ops α) (input : Nat → Nat → α) (t key : Nat) (old : Nat → QueryValue α) (s : State α) :
    queryTile ops input t key old s = queryRows ops input t key old 0 4 (setIndex s t 7 0 22) := rfl

theorem query_tile_fuel (key : Nat) : queryTileFuel key = if key = 0 then 476254 else 476262 := by
  by_cases hz : key = 0 <;> simp [queryTileFuel, oldTailFuel, hz]

theorem query_tile_eq (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (t key extra : Nat) (old : Nat → QueryValue α)
    (s : State α) (ht : t < p.groups * 32) (hr : Reads p input s) (hn : NativeIndices t s)
    (hk : Tiles ops input t key s) (hj : s.indices t 5 = some (key : Int)) (ho : QueriesRange t key old 0 4 s)
    (hp : s.pc t = 21) :
    runLane ops (layout p) (geometry p) program t (extra + queryTileFuel key) s =
      runLane ops (layout p) (geometry p) program t extra (queryTile ops input t key old s) := by
  let next := setIndex s t 7 0 22
  have he := execute_index_of ops (layout p) (geometry p) t 7 22 (.const 0) s 0 (by rfl) (by omega)
  have h1 := source_step p ops t 21 (extra + (119062 + oldTailFuel key) * 4 + 1) _ s next (by rfl) hp he
  have h2 := query_rows_eq p ops input t key old 0 4 extra next ht (by decide) hr
    (indices_set s t 7 22 0 (by decide) hn) hk (by simp [next, setIndex, advance])
    (by simpa [next, setIndex, advance] using hj) ho (by simp [next, setIndex, advance])
  have steps : extra + queryTileFuel key = (extra + (119062 + oldTailFuel key) * 4 + 1) + 1 := by
    unfold queryTileFuel
    omega
  exact (congrArg (fun n => runLane ops (layout p) (geometry p) program t n s) steps).trans (h1.trans h2)

theorem query_tile_fields (ops : Ops α) (input : Nat → Nat → α) (t key : Nat) (old : Nat → QueryValue α) (s : State α) :
    (queryTile ops input t key old s).pc t = 87 ∧ (queryTile ops input t key old s).epochs = s.epochs := by
  have hs := query_tile_state ops input t key old s
  have hf := query_rows_fields ops input t key old 0 4 (setIndex s t 7 0 22)
  exact ⟨(congrArg (fun state : State α => state.pc t) hs).trans hf.1,
    (congrArg (fun state : State α => state.epochs) hs).trans hf.2⟩

theorem query_parked_run (p : Shape) (ops : Ops α) (t remaining : Nat) (s : State α)
    (hp : s.pc t = 87) (hn : 0 < remaining) :
    runLane ops (layout p) (geometry p) program t remaining s = some s := by
  cases remaining with
  | zero => omega
  | succ k =>
      have hc : parked program s t = some .block := by
        unfold parked
        rw [hp]
        rfl
      simp only [runLane, hc]

theorem query_tile_run (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (t key : Nat) (old : Nat → QueryValue α)
    (s : State α) (ht : t < p.groups * 32) (hr : Reads p input s) (hn : NativeIndices t s)
    (hk : Tiles ops input t key s) (hj : s.indices t 5 = some (key : Int)) (ho : QueriesRange t key old 0 4 s)
    (hp : s.pc t = 21) :
    runLane ops (layout p) (geometry p) program t fuel.lane s = some (queryTile ops input t key old s) := by
  have bound : queryTileFuel key < 1000000 := by
    rw [query_tile_fuel]
    split <;> omega
  have steps : fuel.lane = (1000000 - queryTileFuel key) + queryTileFuel key := by
    change 1000000 = _
    omega
  exact (congrArg (fun n => runLane ops (layout p) (geometry p) program t n s) steps).trans
    ((query_tile_eq p ops input t key (1000000 - queryTileFuel key) old s ht hr hn hk hj ho hp).trans
      (query_parked_run p ops t _ _ (query_tile_fields ops input t key old s).1 (by omega)))

theorem query_tile_value (ops : Ops α) (input : Nat → Nat → α) (t key qi col : Nat) (old : Nat → QueryValue α)
    (s : State α) (hi : qi < 4) (hc : col < 256) :
    (queryTile ops input t key old s).memory (globalCell 0 (globalAddress t qi col)) =
      some ((nextQueryValue ops input t qi key (old qi)).stored col) :=
  (congrArg (fun state : State α => state.memory (globalCell 0 (globalAddress t qi col))) (query_tile_state ops input t key old s)).trans
    (query_rows_value ops input t key old 0 4 qi col _ (by omega) hi hc)

theorem query_tile_private (ops : Ops α) (input : Nat → Nat → α) (t key qi : Nat) (old : Nat → QueryValue α)
    (s : State α) (hi : qi < 4) :
    (queryTile ops input t key old s).memory (privateCell t 0 qi) = some (nextQueryValue ops input t qi key (old qi)).maximum ∧
    (queryTile ops input t key old s).memory (privateCell t 1 qi) = some (nextQueryValue ops input t qi key (old qi)).mass := by
  have hs := query_tile_state ops input t key old s
  have hf := query_rows_private ops input t key old 0 4 qi (setIndex s t 7 0 22) (by omega) hi
  exact ⟨(congrArg (fun state : State α => state.memory (privateCell t 0 qi)) hs).trans hf.1,
    (congrArg (fun state : State α => state.memory (privateCell t 1 qi)) hs).trans hf.2⟩

theorem query_tile_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (t key : Nat) (old : Nat → QueryValue α)
    (s : State α) (hr : Reads p input s) : Reads p input (queryTile ops input t key old s) :=
  Eq.mpr (congrArg (Reads p input) (query_tile_state ops input t key old s))
    (query_rows_reads p ops input t key old 0 4 (setIndex s t 7 0 22) hr)

theorem query_tile_good (ops : Ops α) (input : Nat → Nat → α) (t key : Nat) (old : Nat → QueryValue α)
    (s : State α) (he : (s.epochs t).block % 2 = 1) (hg : TraceGood s) : TraceGood (queryTile ops input t key old s) :=
  Eq.mpr (congrArg TraceGood (query_tile_state ops input t key old s))
    (query_rows_good ops input t key old 0 4 (setIndex s t 7 0 22) (by decide) he hg)

#print axioms query_tile_fuel
#print axioms query_tile_eq
#print axioms query_tile_run
#print axioms query_tile_value
#print axioms query_tile_private
#print axioms query_tile_reads
#print axioms query_tile_good
end LarkNativeAttention
