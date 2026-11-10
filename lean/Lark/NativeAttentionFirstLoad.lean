import Lark.NativeAttentionLoadColumns

/-! Source execution from initialization exit to the first K/V block barrier. -/
namespace LarkNativeAttention
open LarkNonlinear
open LarkReduction (setIndex execute_index_of)
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def loadEntry (t : Nat) (s : State α) : State α :=
  let s := setIndex s t 5 0 13
  let s := advance s t 14
  setIndex s t 6 0 15
def firstLoad (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) : State α :=
  loadColumns ops input t 0 0 256 (loadEntry t s)

theorem load_entry_fields (t : Nat) (s : State α) :
    (loadEntry t s).pc t = 15 ∧ (loadEntry t s).indices t 5 = some 0 ∧
    (loadEntry t s).indices t 6 = some 0 ∧ (loadEntry t s).epochs = s.epochs := by
  simp [loadEntry, setIndex, advance]

theorem load_entry_native (t : Nat) (s : State α) (hn : NativeIndices t s) :
    NativeIndices t (loadEntry t s) :=
  indices_set _ t 6 15 0 (by decide) (indices_set s t 5 13 0 (by decide) hn)

theorem first_load_eq (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t extra : Nat) (s : State α) (ht : t < p.groups * 32)
    (hr : Reads p input s) (hn : NativeIndices t s) (hp : s.pc t = 12) :
    runLane ops (layout p) (geometry p) program t (extra + 1284) s =
      runLane ops (layout p) (geometry p) program t extra (firstLoad ops input t s) := by
  let s1 := setIndex s t 5 0 13
  let s2 := advance s1 t 14
  let s3 := loadEntry t s
  have h1 := execute_index_of ops (layout p) (geometry p) t 5 13 (.const 0) s 0 (by rfl) (by omega)
  have hg := LarkReduction.predicate_lt_of (geometry p) t s1 (.ivar 5) (.const 4) 0 4
    (by simp [evalIndex, s1, setIndex, advance]) (by rfl) (by decide)
  have h2 := execute_branch_of ops (layout p) (geometry p) t 14 90 _ s1 true hg
    (by simp [s1, setIndex, advance])
  have h3 := execute_index_of ops (layout p) (geometry p) t 6 15 (.const 0) s2 0 (by rfl)
    (by simp [s2, advance])
  have hf := load_entry_fields t s
  have e1 := source_step p ops t 12 (extra + 1283) _ s s1 (by rfl) hp h1
  have e2 := source_step p ops t 13 (extra + 1282) _ s1 s2 (by rfl)
    (by simp [s1, setIndex, advance]) h2
  have e3 := source_step p ops t 14 (extra + 1281) _ s2 s3 (by rfl)
    (by simp [s2, advance]) h3
  have e4 := load_columns_eq p ops input t 0 0 256 extra s3 ht (by decide) (by decide)
    hr (load_entry_native t s hn) hf.2.1 hf.2.2.1 hf.1
  exact e1.trans (e2.trans (e3.trans e4))

theorem first_load_fields (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) :
    (firstLoad ops input t s).pc t = 20 ∧ (firstLoad ops input t s).epochs = s.epochs := by
  have h := load_columns_fields ops input t 0 0 256 (loadEntry t s)
  exact ⟨h.1, h.2.2.trans (load_entry_fields t s).2.2.2⟩

theorem first_load_native (ops : Ops α) (input : Nat → Nat → α) (t : Nat)
    (s : State α) (hn : NativeIndices t s) : NativeIndices t (firstLoad ops input t s) :=
  load_columns_native ops input t 0 0 256 _ (load_entry_native t s hn)

theorem first_load_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t : Nat) (s : State α) (hr : Reads p input s) : Reads p input (firstLoad ops input t s) :=
  load_columns_reads p ops input t 0 0 256 (loadEntry t s) hr

theorem first_load_good (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α)
    (he : (s.epochs t).block % 2 = 0) (hg : TraceGood s) : TraceGood (firstLoad ops input t s) :=
  load_columns_good ops input t 0 0 256 (loadEntry t s) (by decide) he hg

theorem first_load_global (ops : Ops α) (input : Nat → Nat → α) (t b i : Nat) (s : State α) :
    (firstLoad ops input t s).memory (globalCell b i) = s.memory (globalCell b i) :=
  load_columns_global ops input t 0 0 256 b i (loadEntry t s)

theorem first_load_value (ops : Ops α) (input : Nat → Nat → α) (t b col : Nat) (s : State α)
    (hb : b = 1 ∨ b = 2) (hc : col < 256) :
    (firstLoad ops input t s).memory (sharedCell t b (sharedAddress t col)) =
      some (ops.fromHalf (input (b + 1) (globalAddress t 0 col))) :=
  load_columns_value ops input t 0 0 256 col b (loadEntry t s) (by omega) hc hb

theorem load_entry_other (t u : Nat) (s : State α) (hne : u ≠ t) :
    (loadEntry t s).pc u = s.pc u ∧ (loadEntry t s).indices u = s.indices u ∧
    (loadEntry t s).regs u = s.regs u := by
  simp [loadEntry, setIndex, advance, hne]

theorem first_load_other (ops : Ops α) (input : Nat → Nat → α) (t u : Nat)
    (s : State α) (hne : u ≠ t) :
    (firstLoad ops input t s).pc u = s.pc u ∧ (firstLoad ops input t s).indices u = s.indices u ∧
    (firstLoad ops input t s).regs u = s.regs u := by
  have h := load_columns_other ops input t u 0 0 256 (loadEntry t s) hne
  have he := load_entry_other t u s hne
  exact ⟨h.1.trans he.1, h.2.1.trans he.2.1, h.2.2.trans he.2.2⟩

#print axioms first_load_eq
#print axioms first_load_value
#print axioms first_load_good
end LarkNativeAttention
