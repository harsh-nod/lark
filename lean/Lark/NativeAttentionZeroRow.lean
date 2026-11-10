import Lark.NativeAttentionZeroColumns

/-! One actual outer zero-initialization iteration: four setup/exit instructions
and the 1025-instruction bounded column loop. -/
namespace LarkNativeAttention
open LarkNonlinear
open LarkReduction (setIndex execute_index_of)
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def zeroRowEntry (t : Nat) (s : State α) : State α :=
  setIndex (advance s t 5) t 4 0 6
def zeroRowFinish (t tile : Nat) (s : State α) : State α :=
  advance (setIndex s t 3 ((tile + 1 : Nat) : Int) 11) t 4
def zeroRow (ops : Ops α) (t tile : Nat) (s : State α) : State α :=
  zeroRowFinish t tile (zeroColumns ops t tile 0 256 (zeroRowEntry t s))

theorem zero_row_finish_fields (t tile : Nat) (s : State α) :
    (zeroRowFinish t tile s).pc t = 4 ∧
    (zeroRowFinish t tile s).indices t 3 = some ((tile + 1 : Nat) : Int) ∧
    (zeroRowFinish t tile s).epochs = s.epochs := by
  simp [zeroRowFinish, setIndex, advance]

theorem zero_row_finish_native (t tile : Nat) (s : State α) (hn : NativeIndices t s) :
    NativeIndices t (zeroRowFinish t tile s) :=
  indices_set s t 3 11 _ (by decide) hn

theorem zero_row_finish_reads (p : Shape) (input : Nat → Nat → α) (t tile : Nat)
    (s : State α) (hr : Reads p input s) : Reads p input (zeroRowFinish t tile s) := hr

theorem zero_row_finish_good (t tile : Nat) (s : State α) (hg : TraceGood s) :
    TraceGood (zeroRowFinish t tile s) := hg

theorem zero_row_finish_memory (t tile : Nat) (s : State α) (l : Location) :
    (zeroRowFinish t tile s).memory l = s.memory l := rfl

theorem zero_row_finish_other (t u tile : Nat) (s : State α) (hne : u ≠ t) :
    (zeroRowFinish t tile s).pc u = s.pc u ∧
    (zeroRowFinish t tile s).indices u = s.indices u ∧
    (zeroRowFinish t tile s).regs u = s.regs u := by
  simp [zeroRowFinish, setIndex, advance, hne]

theorem zero_row_eq (p : Shape) (ops : Ops α) (t tile extra : Nat) (s : State α)
    (ht : t < p.groups * 32) (hi : tile < 4) (hn : NativeIndices t s)
    (hrow : s.indices t 3 = some (tile : Int)) (hp : s.pc t = 4) :
    runLane ops (layout p) (geometry p) program t (extra + 1029) s =
      runLane ops (layout p) (geometry p) program t extra (zeroRow ops t tile s) := by
  let s1 := advance s t 5
  let s2 := zeroRowEntry t s
  let s3 := zeroColumns ops t tile 0 256 s2
  let s4 := setIndex s3 t 3 ((tile + 1 : Nat) : Int) 11
  have hg := LarkReduction.predicate_lt_of (geometry p) t s (.ivar 3) (.const 4)
    (tile : Int) 4 hrow (by rfl) (by omega)
  have h1 := execute_branch_of ops (layout p) (geometry p) t 5 12 _ s true hg (by omega)
  have h2 := execute_index_of ops (layout p) (geometry p) t 4 6 (.const 0) s1 0
    (by rfl) (by simp [s1, advance])
  have hn2 : NativeIndices t s2 := indices_set (advance s t 5) t 4 6 0 (by decide) hn
  have hr2 : s2.indices t 3 = some (tile : Int) := by
    simpa [s2, zeroRowEntry, setIndex, advance] using hrow
  have hf := zero_columns_fields ops t tile 0 256 s2
  have he4 := eval_counter (geometry p) t 3 tile s3 (hf.2.1.trans hr2) (by omega)
  have h4 := execute_index_of ops (layout p) (geometry p) t 3 11
    (.add (.ivar 3) (.const 1)) s3 ((tile + 1 : Nat) : Int) he4
    (by have hpc : s3.pc t = 10 := hf.1; omega)
  have e1 := source_step p ops t 4 (extra + 1028) _ s s1 (by rfl) hp h1
  have e2 := source_step p ops t 5 (extra + 1027) _ s1 s2 (by rfl)
    (by simp [s1, advance]) h2
  have e3 := zero_columns_eq p ops t tile 0 256 (extra + 2) s2 ht hi (by decide)
    hn2 hr2 (by simp [s2, zeroRowEntry, setIndex, advance])
    (by simp [s2, zeroRowEntry, setIndex, advance])
  have e4 := source_step p ops t 10 (extra + 1) _ s3 s4 (by rfl) hf.1 h4
  have e5 := source_step p ops t 11 extra (.jump 4) s4 (zeroRow ops t tile s) (by rfl)
    (by simp [s4, setIndex, advance]) (by rfl)
  exact e1.trans (e2.trans (e3.trans (e4.trans e5)))

theorem zero_row_fields (ops : Ops α) (t tile : Nat) (s : State α) :
    (zeroRow ops t tile s).pc t = 4 ∧
    (zeroRow ops t tile s).indices t 3 = some ((tile + 1 : Nat) : Int) ∧
    (zeroRow ops t tile s).epochs = s.epochs := by
  have hf := zero_columns_fields ops t tile 0 256 (zeroRowEntry t s)
  have h := zero_row_finish_fields t tile (zeroColumns ops t tile 0 256 (zeroRowEntry t s))
  exact ⟨h.1, h.2.1, h.2.2.trans hf.2.2⟩

theorem zero_row_native (ops : Ops α) (t tile : Nat) (s : State α)
    (hn : NativeIndices t s) : NativeIndices t (zeroRow ops t tile s) := by
  have hi : NativeIndices t (zeroRowEntry t s) :=
    indices_set (advance s t 5) t 4 6 0 (by decide) hn
  exact zero_row_finish_native t tile _ (zero_columns_native ops t tile 0 256 _ hi)

theorem zero_row_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t tile : Nat) (s : State α) (hr : Reads p input s) :
    Reads p input (zeroRow ops t tile s) :=
  zero_row_finish_reads p input t tile _ (zero_columns_reads p ops input t tile 0 256 (zeroRowEntry t s) hr)

theorem zero_row_good (ops : Ops α) (t tile : Nat) (s : State α)
    (hi : tile < 4) (hg : TraceGood s) : TraceGood (zeroRow ops t tile s) :=
  zero_row_finish_good t tile _ (zero_columns_good ops t tile 0 256 (zeroRowEntry t s) hi (by decide) hg)

theorem zero_row_memory_other (ops : Ops α) (t tile : Nat) (s : State α) (l : Location)
    (hl : ∀ c, c < 256 → l ≠ globalCell 0 (globalAddress t tile c)) :
    (zeroRow ops t tile s).memory l = s.memory l :=
  (zero_row_finish_memory t tile _ l).trans
    (zero_columns_memory_other ops t tile 0 256 (zeroRowEntry t s) l (by intro c _ hc; exact hl c hc))

theorem zero_row_value (ops : Ops α) (t tile col : Nat) (s : State α) (hc : col < 256) :
    (zeroRow ops t tile s).memory (globalCell 0 (globalAddress t tile col)) = some (zeroValue ops) :=
  (zero_row_finish_memory t tile _ _).trans
    (zero_columns_value ops t tile 0 256 col (zeroRowEntry t s) (by omega) hc)

theorem zero_row_other (ops : Ops α) (t u tile : Nat) (s : State α) (hne : u ≠ t) :
    (zeroRow ops t tile s).pc u = s.pc u ∧
    (zeroRow ops t tile s).indices u = s.indices u ∧
    (zeroRow ops t tile s).regs u = s.regs u := by
  have hf := zero_columns_other ops t u tile 0 256 (zeroRowEntry t s) hne
  have h := zero_row_finish_other t u tile (zeroColumns ops t tile 0 256 (zeroRowEntry t s)) hne
  have he : (zeroRowEntry t s).pc u = s.pc u ∧
      (zeroRowEntry t s).indices u = s.indices u ∧ (zeroRowEntry t s).regs u = s.regs u := by
    simp [zeroRowEntry, setIndex, advance, hne]
  exact ⟨h.1.trans (hf.1.trans he.1), h.2.1.trans (hf.2.1.trans he.2.1),
    h.2.2.trans (hf.2.2.trans he.2.2)⟩

#print axioms zero_row_eq
#print axioms zero_row_value
#print axioms zero_row_good
end LarkNativeAttention
