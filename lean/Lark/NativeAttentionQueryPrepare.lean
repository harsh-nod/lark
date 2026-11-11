import Lark.NativeAttentionQueryColumns

/-! Actual query-row preparation through PC 30, before the score loop. -/
namespace LarkNativeAttention
open LarkNonlinear
open LarkReduction (setIndex setReg execute_index_of execute_pure_of)
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def queryEntry (t : Nat) (s : State α) : State α := setIndex (advance s t 23) t 8 0 24
def queryFinish (ops : Ops α) (t : Nat) (s : State α) : State α :=
  setIndex (setReg s t 0 (ops.literal 0 1) 29) t 9 0 30
def queryPrepared (ops : Ops α) (input : Nat → Nat → α) (t tile : Nat) (s : State α) : State α :=
  queryFinish ops t (queryColumns ops input t tile 0 256 (queryEntry t s))

theorem query_finish_fields (ops : Ops α) (t : Nat) (s : State α) :
    (queryFinish ops t s).pc t = 30 ∧ (queryFinish ops t s).indices t 9 = some 0 ∧
    (queryFinish ops t s).regs t 0 = some (ops.literal 0 1) ∧
    (queryFinish ops t s).epochs = s.epochs := by
  simp [queryFinish, setIndex, setReg, advance]

theorem query_finish_native (ops : Ops α) (t : Nat) (s : State α) (hn : NativeIndices t s) :
    NativeIndices t (queryFinish ops t s) :=
  indices_set (setReg s t 0 (ops.literal 0 1) 29) t 9 30 0 (by decide) hn

theorem query_finish_index (ops : Ops α) (t r : Nat) (s : State α) (hr : r ≠ 9) :
    (queryFinish ops t s).indices t r = s.indices t r := by
  simp [queryFinish, setReg, setIndex, advance, hr]

theorem query_finish_memory (ops : Ops α) (t : Nat) (s : State α) (l : Location) :
    (queryFinish ops t s).memory l = s.memory l := rfl

theorem query_finish_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t : Nat) (s : State α) (hr : Reads p input s) : Reads p input (queryFinish ops t s) := hr

theorem query_finish_good (ops : Ops α) (t : Nat) (s : State α) (hg : TraceGood s) :
    TraceGood (queryFinish ops t s) := hg

theorem query_prepare_eq (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t tile extra : Nat) (s : State α) (ht : t < p.groups * 32) (hi : tile < 4)
    (hr : Reads p input s) (hn : NativeIndices t s)
    (hrow : s.indices t 7 = some (tile : Int)) (hp : s.pc t = 22) :
    runLane ops (layout p) (geometry p) program t (extra + 1029) s =
      runLane ops (layout p) (geometry p) program t extra (queryPrepared ops input t tile s) := by
  let s1 := advance s t 23
  let s2 := queryEntry t s
  let s3 := queryColumns ops input t tile 0 256 s2
  let s4 := setReg s3 t 0 (ops.literal 0 1) 29
  have hg := LarkReduction.predicate_lt_of (geometry p) t s (.ivar 7) (.const 4)
    (tile : Int) 4 hrow (by rfl) (by omega)
  have h1 := execute_branch_of ops (layout p) (geometry p) t 23 87 _ s true hg (by omega)
  have h2 := execute_index_of ops (layout p) (geometry p) t 8 24 (.const 0) s1 0
    (by rfl) (by simp [s1, advance])
  have hn2 : NativeIndices t s2 := indices_set s1 t 8 24 0 (by decide) hn
  have hi2 : s2.indices t 7 = some (tile : Int) := by
    simpa [s2, queryEntry, setIndex, advance] using hrow
  have hf := query_columns_fields ops input t tile 0 256 s2
  have hpc : s3.pc t = 28 := hf.1
  have h4 := execute_pure_of ops (layout p) (geometry p) t 0 29 (.lit 0 1) s3 (ops.literal 0 1)
    (by rfl) (by omega)
  have h5 := execute_index_of ops (layout p) (geometry p) t 9 30 (.const 0) s4 0
    (by rfl) (by simp [s4, setReg, advance])
  have e1 := source_step p ops t 22 (extra + 1028) _ s s1 (by rfl) hp h1
  have e2 := source_step p ops t 23 (extra + 1027) _ s1 s2 (by rfl) (by simp [s1, advance]) h2
  have e3 := query_columns_eq p ops input t tile 0 256 (extra + 2) s2 ht hi (by decide) hr hn2 hi2
    (by simp [s2, queryEntry, setIndex, advance]) (by simp [s2, queryEntry, setIndex, advance])
  have e4 := source_step p ops t 28 (extra + 1) _ s3 s4 (by rfl) hpc h4
  have e5 := source_step p ops t 29 extra _ s4 (queryPrepared ops input t tile s) (by rfl)
    (by simp [s4, setReg, advance]) h5
  exact e1.trans (e2.trans (e3.trans (e4.trans e5)))

theorem query_prepared_fields (ops : Ops α) (input : Nat → Nat → α) (t tile : Nat) (s : State α) :
    (queryPrepared ops input t tile s).pc t = 30 ∧
    (queryPrepared ops input t tile s).indices t 9 = some 0 ∧
    (queryPrepared ops input t tile s).regs t 0 = some (ops.literal 0 1) ∧
    (queryPrepared ops input t tile s).epochs = s.epochs := by
  have h := query_finish_fields ops t (queryColumns ops input t tile 0 256 (queryEntry t s))
  have hf := query_columns_fields ops input t tile 0 256 (queryEntry t s)
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.trans hf.2.1⟩

theorem query_prepared_index (ops : Ops α) (input : Nat → Nat → α) (t tile r : Nat)
    (s : State α) (h8 : r ≠ 8) (h9 : r ≠ 9) :
    (queryPrepared ops input t tile s).indices t r = s.indices t r := by
  have h1 := query_finish_index ops t r (queryColumns ops input t tile 0 256 (queryEntry t s)) h9
  have h2 := query_columns_index ops input t tile 0 256 r (queryEntry t s) h8
  have h3 : (queryEntry t s).indices t r = s.indices t r := by simp [queryEntry, setIndex, advance, h8]
  exact h1.trans (h2.trans h3)

theorem query_prepared_native (ops : Ops α) (input : Nat → Nat → α) (t tile : Nat)
    (s : State α) (hn : NativeIndices t s) : NativeIndices t (queryPrepared ops input t tile s) :=
  query_finish_native ops t _ (query_columns_native ops input t tile 0 256 _
    (indices_set (advance s t 23) t 8 24 0 (by decide) hn))

theorem query_prepared_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (t tile : Nat)
    (s : State α) (hr : Reads p input s) : Reads p input (queryPrepared ops input t tile s) :=
  query_finish_reads p ops input t _ (query_columns_reads p ops input t tile 0 256 (queryEntry t s) hr)

theorem query_prepared_good (ops : Ops α) (input : Nat → Nat → α) (t tile : Nat)
    (s : State α) (hg : TraceGood s) : TraceGood (queryPrepared ops input t tile s) :=
  query_finish_good ops t _ (query_columns_good ops input t tile 0 256 (queryEntry t s) (by decide) hg)

theorem query_prepared_value (ops : Ops α) (input : Nat → Nat → α) (t tile col : Nat)
    (s : State α) (hc : col < 256) :
    (queryPrepared ops input t tile s).memory (sharedCell t 0 (sharedAddress t col)) =
      some (ops.fromHalf (input 1 (globalAddress t tile col))) :=
  (query_finish_memory ops t _ _).trans (query_columns_value ops input t tile 0 256 col (queryEntry t s) (by omega) hc)

theorem query_prepared_memory_other (ops : Ops α) (input : Nat → Nat → α)
    (t tile : Nat) (s : State α) (l : Location)
    (hl : ∀ col, col < 256 → l ≠ sharedCell t 0 (sharedAddress t col)) :
    (queryPrepared ops input t tile s).memory l = s.memory l :=
  (query_finish_memory ops t _ l).trans
    (query_columns_memory_other ops input t tile 0 256 (queryEntry t s) l (by intro c _ hc; exact hl c hc))

#print axioms query_prepare_eq
#print axioms query_prepared_value
#print axioms query_prepared_good
end LarkNativeAttention
