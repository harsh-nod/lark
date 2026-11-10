import Lark.NativeAttentionStep

/-! The actual four-instruction zero-initialization component cycle. -/
namespace LarkNativeAttention
open LarkNonlinear
open LarkReduction (setIndex execute_index_of)
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def zeroValue (ops : Ops α) : α := ops.toHalf (ops.literal 0 1)

def zeroCycle (ops : Ops α) (t tile col : Nat) (s : State α) : State α :=
  let s := advance s t 7
  let s := storeState s t (globalCell 0 (globalAddress t tile col)) (zeroValue ops) 8
  let s := setIndex s t 4 ((col + 1 : Nat) : Int) 9
  advance s t 6

theorem zero_cycle_eq (p : Shape) (ops : Ops α) (t tile col extra : Nat) (s : State α)
    (ht : t < p.groups * 32) (hi : tile < 4) (hc : col < 256)
    (hn : NativeIndices t s) (hrow : s.indices t 3 = some (tile : Int))
    (hcol : s.indices t 4 = some (col : Int)) (hp : s.pc t = 6) :
    runLane ops (layout p) (geometry p) program t (extra + 4) s =
      runLane ops (layout p) (geometry p) program t extra (zeroCycle ops t tile col s) := by
  let s1 := advance s t 7
  let s2 := storeState s1 t (globalCell 0 (globalAddress t tile col)) (zeroValue ops) 8
  let s3 := setIndex s2 t 4 ((col + 1 : Nat) : Int) 9
  have hg := LarkReduction.predicate_lt_of (geometry p) t s (.ivar 4) (.const 256)
    (col : Int) 256 hcol (by rfl) (by omega)
  have h1 : execute ops (layout p) (geometry p) t (.branch (.lt (.ivar 4) (.const 256)) 10) s =
      some s1 := by
    simp only [execute, hg, hp, bind, pure, Option.bind]
    rfl
  have h2 := zero_store_eq p ops t tile col s1 ht hi hc hn hrow hcol
    (by simp [s1, advance])
  have he3 := eval_counter (geometry p) t 4 col s2 hcol (by omega)
  have h3 := execute_index_of ops (layout p) (geometry p) t 4 9
    (.add (.ivar 4) (.const 1)) s2 ((col + 1 : Nat) : Int) he3
    (by simp [s2, storeState, advance])
  have h4 : execute ops (layout p) (geometry p) t (.jump 6) s3 =
      some (zeroCycle ops t tile col s) := rfl
  have e1 := source_step p ops t 6 (extra + 3) _ s s1 (by rfl) hp h1
  have e2 := source_step p ops t 7 (extra + 2) _ s1 s2 init_store_code (by simp [s1, advance]) h2
  have e3 := source_step p ops t 8 (extra + 1) _ s2 s3 (by rfl)
    (by simp [s2, storeState, advance]) h3
  have e4 := source_step p ops t 9 extra _ s3 (zeroCycle ops t tile col s) (by rfl)
    (by simp [s3, setIndex, advance]) h4
  exact e1.trans (e2.trans (e3.trans e4))

theorem zero_cycle_fields (ops : Ops α) (t tile col : Nat) (s : State α) :
    (zeroCycle ops t tile col s).pc t = 6 ∧
    (zeroCycle ops t tile col s).indices t 3 = s.indices t 3 ∧
    (zeroCycle ops t tile col s).indices t 4 = some ((col + 1 : Nat) : Int) ∧
    (zeroCycle ops t tile col s).epochs = s.epochs := by
  simp [zeroCycle, setIndex, storeState, advance, record]

theorem zero_cycle_native (ops : Ops α) (t tile col : Nat) (s : State α)
    (hn : NativeIndices t s) : NativeIndices t (zeroCycle ops t tile col s) := by
  simpa [NativeIndices, zeroCycle, setIndex, storeState, advance, record] using hn

theorem zero_cycle_memory (ops : Ops α) (t tile col : Nat) (s : State α) (l : Location) :
    (zeroCycle ops t tile col s).memory l =
      if l = globalCell 0 (globalAddress t tile col) then some (zeroValue ops) else s.memory l := rfl

theorem zero_cycle_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t tile col : Nat) (s : State α) (hr : Reads p input s) :
    Reads p input (zeroCycle ops t tile col s) := by
  intro b hb i hi
  rw [zero_cycle_memory]
  have hn : b ≠ 0 := by rcases hb with rfl | rfl | rfl <;> decide
  simp only [show globalCell b i ≠ globalCell 0 (globalAddress t tile col) by simp [globalCell, hn], ↓reduceIte]
  exact hr b hb i hi

theorem zero_cycle_good (ops : Ops α) (t tile col : Nat) (s : State α)
    (hi : tile < 4) (hc : col < 256) (hg : TraceGood s) : TraceGood (zeroCycle ops t tile col s) := by
  change TraceGood (storeState (advance s t 7) t (globalCell 0 (globalAddress t tile col)) (zeroValue ops) 8)
  exact store_good (advance s t 7) t (globalCell 0 (globalAddress t tile col)) (zeroValue ops) 8 hg
    (output_access_good t tile col true (s.epochs t) hi hc)

theorem zero_cycle_other (ops : Ops α) (t u tile col : Nat) (s : State α) (hne : u ≠ t) :
    (zeroCycle ops t tile col s).pc u = s.pc u ∧
    (zeroCycle ops t tile col s).indices u = s.indices u ∧
    (zeroCycle ops t tile col s).regs u = s.regs u := by
  simp [zeroCycle, storeState, setIndex, advance, record, hne]

#print axioms zero_cycle_eq
#print axioms zero_cycle_good
end LarkNativeAttention
