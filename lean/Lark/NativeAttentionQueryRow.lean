import Lark.NativeAttentionQueryOutput
import Lark.NativeAttentionQueryTail

/-! A full source query-row iteration, including persistent private state. -/
namespace LarkNativeAttention
open LarkNonlinear
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def queryRow (ops : Ops α) (input : Nat → Nat → α) (t qi key : Nat) (old : QueryValue α) (s : State α) : State α :=
  queryTail t qi (queryScales ops input t qi key old) (rowOutput ops input t qi key old s)
theorem query_row_state (ops : Ops α) (input : Nat → Nat → α) (t qi key : Nat) (old : QueryValue α) (s : State α) :
    queryRow ops input t qi key old s =
      queryTail t qi (queryScales ops input t qi key old) (rowOutput ops input t qi key old s) := rfl

theorem query_row_eq (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (t qi key extra : Nat) (old : QueryValue α)
    (s : State α) (ht : t < p.groups * 32) (hi : qi < 4) (hr : Reads p input s) (hn : NativeIndices t s)
    (hk : Tiles ops input t key s) (hq : s.indices t 7 = some (qi : Int)) (hj : s.indices t 5 = some (key : Int))
    (ho : OldQuery t qi key old s) (hp : s.pc t = 22) :
    runLane ops (layout p) (geometry p) program t (extra + (119062 + oldTailFuel key)) s =
      runLane ops (layout p) (geometry p) program t extra (queryRow ops input t qi key old s) := by
  have h1 := row_output_eq p ops input t qi key (extra + 4) old s ht hi hr hn hk hq hj ho hp
  have h2 := query_tail_eq p ops t qi extra (queryScales ops input t qi key old) (selectedMass ops key old.mass)
    (rowOutput ops input t qi key old s) hi
    ((row_output_index ops input t qi key 7 old s (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hq)
    (row_output_scales ops input t qi key old s) (row_output_fields ops input t qi key old s).1
  have steps : extra + (119062 + oldTailFuel key) = (extra + 4) + (119058 + oldTailFuel key) := by omega
  exact (congrArg (fun n => runLane ops (layout p) (geometry p) program t n s) steps).trans (h1.trans h2)

theorem query_row_fields (ops : Ops α) (input : Nat → Nat → α) (t qi key : Nat) (old : QueryValue α) (s : State α) :
    (queryRow ops input t qi key old s).pc t = 22 ∧
    (queryRow ops input t qi key old s).indices t 7 = some ((qi + 1 : Nat) : Int) ∧
    (queryRow ops input t qi key old s).epochs = s.epochs := by
  have hs := query_row_state ops input t qi key old s
  have hf := query_tail_fields t qi (queryScales ops input t qi key old) (rowOutput ops input t qi key old s)
  exact ⟨(congrArg (fun state : State α => state.pc t) hs).trans hf.1,
    (congrArg (fun state : State α => state.indices t 7) hs).trans hf.2.1,
    (congrArg (fun state : State α => state.epochs) hs).trans (hf.2.2.1.trans (row_output_fields ops input t qi key old s).2)⟩

theorem query_row_value (ops : Ops α) (input : Nat → Nat → α) (t qi key col : Nat) (old : QueryValue α) (s : State α) (hc : col < 256) :
    (queryRow ops input t qi key old s).memory (globalCell 0 (globalAddress t qi col)) =
      some ((nextQueryValue ops input t qi key old).stored col) :=
  (congrArg (fun state : State α => state.memory (globalCell 0 (globalAddress t qi col))) (query_row_state ops input t qi key old s)).trans
    ((query_tail_global t qi 0 (globalAddress t qi col) (queryScales ops input t qi key old) _).trans
      (row_output_value ops input t qi key col old s hc))

theorem query_row_private (ops : Ops α) (input : Nat → Nat → α) (t qi key : Nat) (old : QueryValue α) (s : State α) :
    (queryRow ops input t qi key old s).memory (privateCell t 0 qi) = some (nextQueryValue ops input t qi key old).maximum ∧
    (queryRow ops input t qi key old s).memory (privateCell t 1 qi) = some (nextQueryValue ops input t qi key old).mass := by
  have hs := query_row_state ops input t qi key old s
  have hf := query_tail_values t qi (queryScales ops input t qi key old) (rowOutput ops input t qi key old s)
  exact ⟨(congrArg (fun state : State α => state.memory (privateCell t 0 qi)) hs).trans hf.1,
    (congrArg (fun state : State α => state.memory (privateCell t 1 qi)) hs).trans hf.2⟩

theorem query_row_index (ops : Ops α) (input : Nat → Nat → α) (t qi key r : Nat) (old : QueryValue α) (s : State α)
    (h7 : r ≠ 7) (h8 : r ≠ 8) (h9 : r ≠ 9) (h10 : r ≠ 10) (h11 : r ≠ 11) (h12 : r ≠ 12) (h13 : r ≠ 13) :
    (queryRow ops input t qi key old s).indices t r = s.indices t r :=
  (congrArg (fun state : State α => state.indices t r) (query_row_state ops input t qi key old s)).trans
    ((query_tail_index t qi r (queryScales ops input t qi key old) _ h7).trans
      (row_output_index ops input t qi key r old s h8 h9 h10 h11 h12 h13))

theorem query_row_native (ops : Ops α) (input : Nat → Nat → α) (t qi key : Nat) (old : QueryValue α)
    (s : State α) (hn : NativeIndices t s) : NativeIndices t (queryRow ops input t qi key old s) :=
  ⟨(query_row_index ops input t qi key 0 old s (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hn.1,
   (query_row_index ops input t qi key 1 old s (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hn.2.1,
   (query_row_index ops input t qi key 2 old s (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hn.2.2⟩

theorem query_row_memory_other (ops : Ops α) (input : Nat → Nat → α) (t qi key : Nat) (old : QueryValue α) (s : State α) (l : Location)
    (hq : ∀ c, c < 256 → l ≠ sharedCell t 0 (sharedAddress t c))
    (hs : ∀ r, r < 32 → l ≠ sharedCell t 3 (scoreAddress t r))
    (ho : ∀ c, c < 256 → l ≠ globalCell 0 (globalAddress t qi c))
    (hm : l ≠ privateCell t 0 qi) (hl : l ≠ privateCell t 1 qi) :
    (queryRow ops input t qi key old s).memory l = s.memory l := by
  have hf := query_tail_memory t qi (queryScales ops input t qi key old) (rowOutput ops input t qi key old s) l
  rw [if_neg hl, if_neg hm] at hf
  exact (congrArg (fun state : State α => state.memory l) (query_row_state ops input t qi key old s)).trans
    (hf.trans (row_output_memory_other ops input t qi key old s l hq hs ho))

theorem query_row_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (t qi key : Nat) (old : QueryValue α)
    (s : State α) (hr : Reads p input s) : Reads p input (queryRow ops input t qi key old s) := by
  intro buffer hb i hi
  have hb0 : buffer ≠ 0 := by omega
  exact (query_row_memory_other ops input t qi key old s (globalCell buffer i)
    (by intro c hc; simp [globalCell, sharedCell]) (by intro r hr; simp [globalCell, sharedCell])
    (by intro c hc; simp [globalCell, hb0]) (by simp [globalCell, privateCell]) (by simp [globalCell, privateCell])).trans (hr buffer hb i hi)

theorem query_row_tiles (ops : Ops α) (input : Nat → Nat → α) (t qi key : Nat) (old : QueryValue α)
    (s : State α) (hk : Tiles ops input t key s) : Tiles ops input t key (queryRow ops input t qi key old s) := by
  intro buffer hb row hr col hc
  exact (query_row_memory_other ops input t qi key old s (sharedCell t buffer (row * 256 + col))
    (by intro c hc; rcases hb with rfl | rfl <;> simp [sharedCell])
    (by intro r hr; rcases hb with rfl | rfl <;> simp [sharedCell])
    (by intro c hc; simp [sharedCell, globalCell])
    (by simp [sharedCell, privateCell]) (by simp [sharedCell, privateCell])).trans (hk buffer hb row hr col hc)

theorem query_row_good (ops : Ops α) (input : Nat → Nat → α) (t qi key : Nat) (old : QueryValue α)
    (s : State α) (hi : qi < 4) (he : (s.epochs t).block % 2 = 1) (hg : TraceGood s) : TraceGood (queryRow ops input t qi key old s) :=
  Eq.mpr (congrArg TraceGood (query_row_state ops input t qi key old s))
    (query_tail_good t qi (queryScales ops input t qi key old) _ (row_output_good ops input t qi key old s hi he hg))

#print axioms query_row_eq
#print axioms query_row_fields
#print axioms query_row_value
#print axioms query_row_private
#print axioms query_row_memory_other
#print axioms query_row_reads
#print axioms query_row_tiles
#print axioms query_row_good
end LarkNativeAttention
