import Lark.NativeAttentionFirstKeyBlock

/-! Actual key increment and native K/V row copies between query phases. -/
namespace LarkNativeAttention
open LarkNonlinear
open LarkReduction (setIndex execute_index_of)
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def nextEntry (t key : Nat) (s : State α) : State α :=
  let s := setIndex s t 5 ((key + 1 : Nat) : Int) 89
  let s := advance s t 13
  let s := advance s t 14
  setIndex s t 6 0 15
def nextLoad (ops : Ops α) (input : Nat → Nat → α) (t key : Nat) (s : State α) : State α :=
  loadColumns ops input t (key + 1) 0 256 (nextEntry t key s)
theorem next_load_state (ops : Ops α) (input : Nat → Nat → α) (t key : Nat) (s : State α) :
    nextLoad ops input t key s = loadColumns ops input t (key + 1) 0 256 (nextEntry t key s) := rfl

theorem next_entry_fields (t key : Nat) (s : State α) :
    (nextEntry t key s).pc t = 15 ∧ (nextEntry t key s).indices t 5 = some ((key + 1 : Nat) : Int) ∧
    (nextEntry t key s).indices t 6 = some 0 ∧ (nextEntry t key s).epochs = s.epochs := by
  simp [nextEntry, setIndex, advance]

theorem next_entry_native (t key : Nat) (s : State α) (hn : NativeIndices t s) : NativeIndices t (nextEntry t key s) :=
  indices_set _ t 6 15 0 (by decide) (indices_set s t 5 89 ((key + 1 : Nat) : Int) (by decide) hn)

theorem next_entry_eq (p : Shape) (ops : Ops α) (t key extra : Nat) (s : State α)
    (hk : key + 1 < 4) (hj : s.indices t 5 = some (key : Int)) (hp : s.pc t = 88) :
    runLane ops (layout p) (geometry p) program t (extra + 4) s =
      runLane ops (layout p) (geometry p) program t extra (nextEntry t key s) := by
  let s1 := setIndex s t 5 ((key + 1 : Nat) : Int) 89
  let s2 := advance s1 t 13
  let s3 := advance s2 t 14
  have h1 := execute_index_of ops (layout p) (geometry p) t 5 89 (.add (.ivar 5) (.const 1)) s ((key + 1 : Nat) : Int)
    (eval_counter (geometry p) t 5 key s hj (by omega)) (by omega)
  have hg := LarkReduction.predicate_lt_of (geometry p) t s2 (.ivar 5) (.const 4) ((key + 1 : Nat) : Int) 4
    (by simp [evalIndex, s2, s1, setIndex, advance]) (by rfl) (by omega)
  have h3 := execute_branch_of ops (layout p) (geometry p) t 14 90 _ s2 true hg (by simp [s2, advance])
  have h4 := execute_index_of ops (layout p) (geometry p) t 6 15 (.const 0) s3 0 (by rfl) (by simp [s3, advance])
  exact (source_step p ops t 88 (extra + 3) _ s s1 (by rfl) hp h1).trans
    ((source_step p ops t 89 (extra + 2) (.jump 13) s1 s2 (by rfl) (by simp [s1, setIndex, advance]) (by rfl)).trans
      ((source_step p ops t 13 (extra + 1) _ s2 s3 (by rfl) (by simp [s2, advance]) h3).trans
        (source_step p ops t 14 extra _ s3 (nextEntry t key s) (by rfl) (by simp [s3, advance]) h4)))

theorem next_load_eq (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (t key extra : Nat) (s : State α)
    (ht : t < p.groups * 32) (hk : key + 1 < 4) (hr : Reads p input s) (hn : NativeIndices t s)
    (hj : s.indices t 5 = some (key : Int)) (hp : s.pc t = 88) :
    runLane ops (layout p) (geometry p) program t (extra + 1285) s =
      runLane ops (layout p) (geometry p) program t extra (nextLoad ops input t key s) := by
  have hf := next_entry_fields t key s
  have h1 := next_entry_eq p ops t key (extra + 1281) s hk hj hp
  have h2 := load_columns_eq p ops input t (key + 1) 0 256 extra (nextEntry t key s) ht hk (by decide)
    hr (next_entry_native t key s hn) hf.2.1 hf.2.2.1 hf.1
  have steps : extra + 1285 = (extra + 1281) + 4 := by omega
  have columnSteps : extra + 1281 = extra + 5 * 256 + 1 := by omega
  have h2' := (congrArg (fun n => runLane ops (layout p) (geometry p) program t n (nextEntry t key s)) columnSteps).trans h2
  exact (congrArg (fun n => runLane ops (layout p) (geometry p) program t n s) steps).trans (h1.trans h2')

theorem next_load_fields (ops : Ops α) (input : Nat → Nat → α) (t key : Nat) (s : State α) :
    (nextLoad ops input t key s).pc t = 20 ∧ (nextLoad ops input t key s).indices t 5 = some ((key + 1 : Nat) : Int) ∧
    (nextLoad ops input t key s).epochs = s.epochs := by
  have hs := next_load_state ops input t key s
  have hf := load_columns_fields ops input t (key + 1) 0 256 (nextEntry t key s)
  have he := next_entry_fields t key s
  exact ⟨(congrArg (fun state : State α => state.pc t) hs).trans hf.1,
    (congrArg (fun state : State α => state.indices t 5) hs).trans (hf.2.1.trans he.2.1),
    (congrArg (fun state : State α => state.epochs) hs).trans hf.2.2⟩

theorem next_load_run (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (t key : Nat) (s : State α)
    (ht : t < p.groups * 32) (hk : key + 1 < 4) (hr : Reads p input s) (hn : NativeIndices t s)
    (hj : s.indices t 5 = some (key : Int)) (hp : s.pc t = 88) :
    runLane ops (layout p) (geometry p) program t fuel.lane s = some (nextLoad ops input t key s) := by
  exact (next_load_eq p ops input t key 998715 s ht hk hr hn hj hp).trans
    (block_parked_run p ops t 998715 _ (next_load_fields ops input t key s).1 (by decide))

theorem next_load_native (ops : Ops α) (input : Nat → Nat → α) (t key : Nat) (s : State α) (hn : NativeIndices t s) :
    NativeIndices t (nextLoad ops input t key s) :=
  Eq.mpr (congrArg (NativeIndices t) (next_load_state ops input t key s))
    (load_columns_native ops input t (key + 1) 0 256 _ (next_entry_native t key s hn))

theorem next_load_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (t key : Nat) (s : State α) (hr : Reads p input s) :
    Reads p input (nextLoad ops input t key s) :=
  Eq.mpr (congrArg (Reads p input) (next_load_state ops input t key s))
    (load_columns_reads p ops input t (key + 1) 0 256 (nextEntry t key s) hr)

theorem next_load_good (ops : Ops α) (input : Nat → Nat → α) (t key : Nat) (s : State α)
    (he : (s.epochs t).block % 2 = 0) (hg : TraceGood s) : TraceGood (nextLoad ops input t key s) :=
  Eq.mpr (congrArg TraceGood (next_load_state ops input t key s))
    (load_columns_good ops input t (key + 1) 0 256 (nextEntry t key s) (by decide) he hg)

theorem next_load_value (ops : Ops α) (input : Nat → Nat → α) (t key buffer col : Nat) (s : State α)
    (hb : buffer = 1 ∨ buffer = 2) (hc : col < 256) :
    (nextLoad ops input t key s).memory (sharedCell t buffer (sharedAddress t col)) =
      some (ops.fromHalf (input (buffer + 1) (globalAddress t (key + 1) col))) :=
  (congrArg (fun state : State α => state.memory (sharedCell t buffer (sharedAddress t col))) (next_load_state ops input t key s)).trans
    (load_columns_value ops input t (key + 1) 0 256 col buffer (nextEntry t key s) (by omega) hc hb)

theorem next_load_memory_other (ops : Ops α) (input : Nat → Nat → α) (t key : Nat) (s : State α) (l : Location)
    (hl : ∀ c, c < 256 → l ≠ sharedCell t 1 (sharedAddress t c) ∧ l ≠ sharedCell t 2 (sharedAddress t c)) :
    (nextLoad ops input t key s).memory l = s.memory l :=
  (congrArg (fun state : State α => state.memory l) (next_load_state ops input t key s)).trans
    (load_columns_memory_other ops input t (key + 1) 0 256 (nextEntry t key s) l (by intro c hc hb; exact hl c hb))

theorem next_load_other (ops : Ops α) (input : Nat → Nat → α) (t key u : Nat) (s : State α) (hne : u ≠ t) :
    (nextLoad ops input t key s).pc u = s.pc u ∧ (nextLoad ops input t key s).indices u = s.indices u ∧
    (nextLoad ops input t key s).regs u = s.regs u := by
  have hf := load_columns_other ops input t u (key + 1) 0 256 (nextEntry t key s) hne
  have he : (nextEntry t key s).pc u = s.pc u ∧ (nextEntry t key s).indices u = s.indices u ∧
      (nextEntry t key s).regs u = s.regs u := by simp [nextEntry, setIndex, advance, hne]
  have hs := next_load_state ops input t key s
  exact ⟨(congrArg (fun state : State α => state.pc u) hs).trans (hf.1.trans he.1),
    (congrArg (fun state : State α => state.indices u) hs).trans (hf.2.1.trans he.2.1),
    (congrArg (fun state : State α => state.regs u) hs).trans (hf.2.2.trans he.2.2)⟩

#print axioms next_entry_eq
#print axioms next_load_eq
#print axioms next_load_run
#print axioms next_load_value
#print axioms next_load_good
#print axioms next_load_memory_other
end LarkNativeAttention
