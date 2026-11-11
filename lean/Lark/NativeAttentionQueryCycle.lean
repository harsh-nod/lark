import Lark.NativeAttentionQueryCopy

/-! Actual four-instruction native Q-copy cycle, with the source's indices. -/
namespace LarkNativeAttention
open LarkNonlinear
open LarkReduction (setIndex execute_index_of)
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def queryCycle (ops : Ops α) (input : Nat → Nat → α) (t tile col : Nat) (s : State α) : State α :=
  let s := advance s t 25
  let s := tileCopy ops input t tile col 1 26 s
  let s := setIndex s t 8 ((col + 1 : Nat) : Int) 27
  advance s t 24

theorem query_cycle_eq (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t tile col extra : Nat) (s : State α) (ht : t < p.groups * 32) (hi : tile < 4) (hc : col < 256)
    (hr : Reads p input s) (hn : NativeIndices t s)
    (hrow : s.indices t 7 = some (tile : Int)) (hcol : s.indices t 8 = some (col : Int))
    (hp : s.pc t = 24) :
    runLane ops (layout p) (geometry p) program t (extra + 4) s =
      runLane ops (layout p) (geometry p) program t extra (queryCycle ops input t tile col s) := by
  let s1 := advance s t 25
  let s2 := tileCopy ops input t tile col 1 26 s1
  let s3 := setIndex s2 t 8 ((col + 1 : Nat) : Int) 27
  have hg := LarkReduction.predicate_lt_of (geometry p) t s (.ivar 8) (.const 256)
    (col : Int) 256 hcol (by rfl) (by omega)
  have h1 := execute_branch_of ops (layout p) (geometry p) t 25 28 _ s true hg (by omega)
  have h2 := query_copy_eq p ops input t tile col s1 ht hi hc hr hn hrow hcol (by simp [s1, advance])
  have he3 := eval_counter (geometry p) t 8 col s2 hcol (by omega)
  have h3 := execute_index_of ops (layout p) (geometry p) t 8 27
    (.add (.ivar 8) (.const 1)) s2 ((col + 1 : Nat) : Int) he3
    (by simp [s2, tileCopy, storeState, advance])
  have e1 := source_step p ops t 24 (extra + 3) _ s s1 (by rfl) hp h1
  have e2 := source_step p ops t 25 (extra + 2) _ s1 s2 query_store_code (by simp [s1, advance]) h2
  have e3 := source_step p ops t 26 (extra + 1) _ s2 s3 (by rfl)
    (by simp [s2, tileCopy, storeState, advance]) h3
  have e4 := source_step p ops t 27 extra (.jump 24) s3 (queryCycle ops input t tile col s)
    (by rfl) (by simp [s3, setIndex, advance]) (by rfl)
  exact e1.trans (e2.trans (e3.trans e4))

theorem query_cycle_fields (ops : Ops α) (input : Nat → Nat → α) (t tile col : Nat) (s : State α) :
    (queryCycle ops input t tile col s).pc t = 24 ∧
    (queryCycle ops input t tile col s).indices t 8 = some ((col + 1 : Nat) : Int) ∧
    (queryCycle ops input t tile col s).epochs = s.epochs ∧
    (queryCycle ops input t tile col s).regs = s.regs := by
  simp [queryCycle, tileCopy, storeState, setIndex, advance, record]

theorem query_cycle_index (ops : Ops α) (input : Nat → Nat → α) (t tile col r : Nat)
    (s : State α) (hr : r ≠ 8) : (queryCycle ops input t tile col s).indices t r = s.indices t r := by
  simp [queryCycle, tileCopy, storeState, setIndex, advance, record, hr]

theorem query_cycle_native (ops : Ops α) (input : Nat → Nat → α) (t tile col : Nat)
    (s : State α) (hn : NativeIndices t s) : NativeIndices t (queryCycle ops input t tile col s) :=
  ⟨(query_cycle_index ops input t tile col 0 s (by decide)).trans hn.1,
   (query_cycle_index ops input t tile col 1 s (by decide)).trans hn.2.1,
   (query_cycle_index ops input t tile col 2 s (by decide)).trans hn.2.2⟩

theorem query_cycle_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t tile col : Nat) (s : State α) (hr : Reads p input s) :
    Reads p input (queryCycle ops input t tile col s) :=
  tile_copy_reads p ops input t tile col 1 26 (advance s t 25) hr

theorem query_cycle_good (ops : Ops α) (input : Nat → Nat → α) (t tile col : Nat)
    (s : State α) (hc : col < 256) (hg : TraceGood s) : TraceGood (queryCycle ops input t tile col s) :=
  query_copy_good ops input t tile col (advance s t 25) hc hg

theorem query_cycle_memory (ops : Ops α) (input : Nat → Nat → α) (t tile col : Nat)
    (s : State α) (l : Location) :
    (queryCycle ops input t tile col s).memory l = if l = sharedCell t 0 (sharedAddress t col)
      then some (ops.fromHalf (input 1 (globalAddress t tile col))) else s.memory l := rfl

theorem query_cycle_other (ops : Ops α) (input : Nat → Nat → α) (t u tile col : Nat)
    (s : State α) (hne : u ≠ t) :
    (queryCycle ops input t tile col s).pc u = s.pc u ∧
    (queryCycle ops input t tile col s).indices u = s.indices u ∧
    (queryCycle ops input t tile col s).regs u = s.regs u := by
  simp [queryCycle, tileCopy, storeState, setIndex, advance, record, hne]

#print axioms query_cycle_eq
#print axioms query_cycle_good
end LarkNativeAttention
