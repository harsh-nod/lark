import Lark.NativeAttentionInit

/-! Exact global-half to shared-float tile stores, including both trace events. -/
namespace LarkNativeAttention
open LarkNonlinear
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem eval_from_half_load_of (ops : Ops α) (l : Layout) (g : Geometry) (t b : Nat)
    (ix : Index) (s : State α) (index : Int) (cell : Location) (v : α)
    (hi : evalIndex g t s ix = some index)
    (hl : location l g t .global b index false = some cell) (hv : s.memory cell = some v) :
    evalExpr ops l g t (.un .fromHalf (.load .global b ix)) s =
      some (ops.fromHalf v, record s t cell false) := by
  simp only [evalExpr, hi, hl, hv, bind, pure, Option.bind]
  rfl

def tileCopy (ops : Ops α) (input : Nat → Nat → α) (t tile col buffer pc : Nat)
    (s : State α) : State α :=
  storeState (record s t (globalCell buffer (globalAddress t tile col)) false) t
    (sharedCell t (buffer - 1) (sharedAddress t col))
    (ops.fromHalf (input buffer (globalAddress t tile col))) pc

theorem tile_copy_eq (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t tile col buffer pc : Nat) (s : State α)
    (ht : t < p.groups * 32) (hi : tile < 4) (hc : col < 256)
    (hb : buffer = 2 ∨ buffer = 3) (hr : Reads p input s) (hn : NativeIndices t s)
    (hrow : s.indices t 5 = some (tile : Int)) (hcol : s.indices t 6 = some (col : Int))
    (hp : s.pc t + 1 = pc) :
    execute ops (layout p) (geometry p) t
      (.store .shared (buffer - 1) (sharedIndex 6)
        (.un .fromHalf (.load .global buffer (globalIndex 5 6)))) s =
      some (tileCopy ops input t tile col buffer pc s) := by
  have hb' : buffer = 1 ∨ buffer = 2 ∨ buffer = 3 := by omega
  have hg := global_address_bound p t tile col ht hi hc
  have he := eval_from_half_load_of ops (layout p) (geometry p) t buffer (globalIndex 5 6)
    s (globalAddress t tile col) (globalCell buffer (globalAddress t tile col))
    (input buffer (globalAddress t tile col))
    (eval_global_index p t tile col 5 6 s ht hi hc hn hrow hcol)
    (input_location p t buffer _ hb' hg) (hr buffer hb' _ hg)
  exact execute_store_of ops (layout p) (geometry p) t pc .shared (buffer - 1)
    (sharedIndex 6) _ s _ (sharedAddress t col) _ _
    (eval_shared_index (geometry p) t 6 col s hc hn.2.1 hcol)
    (shared_location p t (buffer - 1) _ true (by omega) (shared_address_bound t col hc)) he hp

theorem tile_copy_fields (ops : Ops α) (input : Nat → Nat → α) (t tile col buffer pc : Nat)
    (s : State α) :
    (tileCopy ops input t tile col buffer pc s).pc t = pc ∧
    (tileCopy ops input t tile col buffer pc s).indices = s.indices ∧
    (tileCopy ops input t tile col buffer pc s).epochs = s.epochs := by
  simp [tileCopy, storeState, advance, record]

theorem tile_copy_native (ops : Ops α) (input : Nat → Nat → α) (t tile col buffer pc : Nat)
    (s : State α) (hn : NativeIndices t s) :
    NativeIndices t (tileCopy ops input t tile col buffer pc s) := hn

theorem tile_copy_memory (ops : Ops α) (input : Nat → Nat → α) (t tile col buffer pc : Nat)
    (s : State α) (l : Location) :
    (tileCopy ops input t tile col buffer pc s).memory l =
      if l = sharedCell t (buffer - 1) (sharedAddress t col) then
        some (ops.fromHalf (input buffer (globalAddress t tile col))) else s.memory l := rfl

theorem tile_copy_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t tile col buffer pc : Nat) (s : State α) (hr : Reads p input s) :
    Reads p input (tileCopy ops input t tile col buffer pc s) := by
  intro b hb i hi
  rw [tile_copy_memory, if_neg (by simp [globalCell, sharedCell])]
  exact hr b hb i hi

theorem tile_copy_good (ops : Ops α) (input : Nat → Nat → α) (t tile col buffer pc : Nat)
    (s : State α) (hb : buffer = 2 ∨ buffer = 3) (hc : col < 256)
    (he : (s.epochs t).block % 2 = 0) (hg : TraceGood s) :
    TraceGood (tileCopy ops input t tile col buffer pc s) := by
  apply store_good
  · intro a ha
    rcases List.mem_cons.mp ha with heq | hm
    · subst a
      exact Good.input rfl rfl (by dsimp [globalCell]; omega) rfl
    · exact hg a hm
  · exact tile_store_access_good t (buffer - 1) col (s.epochs t) (by omega) hc he

theorem tile_copy_other (ops : Ops α) (input : Nat → Nat → α) (t u tile col buffer pc : Nat)
    (s : State α) (hne : u ≠ t) :
    (tileCopy ops input t tile col buffer pc s).pc u = s.pc u ∧
    (tileCopy ops input t tile col buffer pc s).indices u = s.indices u ∧
    (tileCopy ops input t tile col buffer pc s).regs u = s.regs u := by
  simp [tileCopy, storeState, record, advance, hne]

#print axioms tile_copy_eq
#print axioms tile_copy_good
end LarkNativeAttention
