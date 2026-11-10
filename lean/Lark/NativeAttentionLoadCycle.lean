import Lark.NativeAttentionTileCopy

/-! Actual five-instruction K/V copy cycle of the pinned native source. -/
namespace LarkNativeAttention
open LarkNonlinear
open LarkReduction (setIndex execute_index_of)
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def loadCycle (ops : Ops α) (input : Nat → Nat → α) (t tile col : Nat) (s : State α) : State α :=
  let s := advance s t 16
  let s := tileCopy ops input t tile col 2 17 s
  let s := tileCopy ops input t tile col 3 18 s
  let s := setIndex s t 6 ((col + 1 : Nat) : Int) 19
  advance s t 15

theorem load_cycle_eq (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t tile col extra : Nat) (s : State α)
    (ht : t < p.groups * 32) (hi : tile < 4) (hc : col < 256)
    (hr : Reads p input s) (hn : NativeIndices t s)
    (hrow : s.indices t 5 = some (tile : Int)) (hcol : s.indices t 6 = some (col : Int))
    (hp : s.pc t = 15) :
    runLane ops (layout p) (geometry p) program t (extra + 5) s =
      runLane ops (layout p) (geometry p) program t extra (loadCycle ops input t tile col s) := by
  let s1 := advance s t 16
  let s2 := tileCopy ops input t tile col 2 17 s1
  let s3 := tileCopy ops input t tile col 3 18 s2
  let s4 := setIndex s3 t 6 ((col + 1 : Nat) : Int) 19
  have hg := LarkReduction.predicate_lt_of (geometry p) t s (.ivar 6) (.const 256)
    (col : Int) 256 hcol (by rfl) (by omega)
  have h1 := execute_branch_of ops (layout p) (geometry p) t 16 20 _ s true hg (by omega)
  have h2 := tile_copy_eq p ops input t tile col 2 17 s1 ht hi hc (Or.inl rfl) hr hn hrow hcol
    (by simp [s1, advance])
  have h3 := tile_copy_eq p ops input t tile col 3 18 s2 ht hi hc (Or.inr rfl)
    (tile_copy_reads p ops input t tile col 2 17 s1 hr)
    (tile_copy_native ops input t tile col 2 17 s1 hn) hrow hcol
    (by simp [s2, tileCopy, storeState, advance])
  have he4 := eval_counter (geometry p) t 6 col s3 hcol (by omega)
  have h4 := execute_index_of ops (layout p) (geometry p) t 6 19
    (.add (.ivar 6) (.const 1)) s3 ((col + 1 : Nat) : Int) he4
    (by simp [s3, tileCopy, storeState, advance])
  have e1 := source_step p ops t 15 (extra + 4) _ s s1 (by rfl) hp h1
  have e2 := source_step p ops t 16 (extra + 3) _ s1 s2 key_store_code
    (by simp [s1, advance]) h2
  have e3 := source_step p ops t 17 (extra + 2) _ s2 s3 value_store_code
    (by simp [s2, tileCopy, storeState, advance]) h3
  have e4 := source_step p ops t 18 (extra + 1) _ s3 s4 (by rfl)
    (by simp [s3, tileCopy, storeState, advance]) h4
  have e5 := source_step p ops t 19 extra (.jump 15) s4 (loadCycle ops input t tile col s) (by rfl)
    (by simp [s4, setIndex, advance]) (by rfl)
  exact e1.trans (e2.trans (e3.trans (e4.trans e5)))

theorem load_cycle_fields (ops : Ops α) (input : Nat → Nat → α) (t tile col : Nat) (s : State α) :
    (loadCycle ops input t tile col s).pc t = 15 ∧
    (loadCycle ops input t tile col s).indices t 5 = s.indices t 5 ∧
    (loadCycle ops input t tile col s).indices t 6 = some ((col + 1 : Nat) : Int) ∧
    (loadCycle ops input t tile col s).epochs = s.epochs := by
  simp [loadCycle, tileCopy, storeState, setIndex, advance, record]

theorem load_cycle_native (ops : Ops α) (input : Nat → Nat → α) (t tile col : Nat)
    (s : State α) (hn : NativeIndices t s) : NativeIndices t (loadCycle ops input t tile col s) := by
  simpa [NativeIndices, loadCycle, tileCopy, storeState, setIndex, advance, record] using hn

theorem load_cycle_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t tile col : Nat) (s : State α) (hr : Reads p input s) :
    Reads p input (loadCycle ops input t tile col s) :=
  tile_copy_reads p ops input t tile col 3 18 _ (tile_copy_reads p ops input t tile col 2 17 (advance s t 16) hr)

theorem load_cycle_good (ops : Ops α) (input : Nat → Nat → α) (t tile col : Nat)
    (s : State α) (hc : col < 256) (he : (s.epochs t).block % 2 = 0) (hg : TraceGood s) :
    TraceGood (loadCycle ops input t tile col s) :=
  tile_copy_good ops input t tile col 3 18 _ (Or.inr rfl) hc he
    (tile_copy_good ops input t tile col 2 17 (advance s t 16) (Or.inl rfl) hc he hg)

theorem load_cycle_memory (ops : Ops α) (input : Nat → Nat → α) (t tile col : Nat)
    (s : State α) (l : Location) :
    (loadCycle ops input t tile col s).memory l =
      if l = sharedCell t 2 (sharedAddress t col) then
        some (ops.fromHalf (input 3 (globalAddress t tile col)))
      else if l = sharedCell t 1 (sharedAddress t col) then
        some (ops.fromHalf (input 2 (globalAddress t tile col))) else s.memory l := rfl

theorem load_cycle_global (ops : Ops α) (input : Nat → Nat → α) (t tile col b i : Nat)
    (s : State α) : (loadCycle ops input t tile col s).memory (globalCell b i) = s.memory (globalCell b i) := by
  rw [load_cycle_memory]
  simp [globalCell, sharedCell]

theorem load_cycle_other (ops : Ops α) (input : Nat → Nat → α) (t u tile col : Nat)
    (s : State α) (hne : u ≠ t) :
    (loadCycle ops input t tile col s).pc u = s.pc u ∧
    (loadCycle ops input t tile col s).indices u = s.indices u ∧
    (loadCycle ops input t tile col s).regs u = s.regs u := by
  simp [loadCycle, tileCopy, storeState, setIndex, advance, record, hne]

#print axioms load_cycle_eq
#print axioms load_cycle_good
end LarkNativeAttention
