import Lark.NativeAttentionZeroRows

/-! Source execution through all 1024 scalar zero stores per native lane. -/
namespace LarkNativeAttention
open LarkNonlinear
open LarkReduction (setIndex execute_index_of)
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def zeroInit (ops : Ops α) (t : Nat) (s : State α) : State α :=
  zeroRows ops t 0 4 (setIndex s t 3 0 4)

theorem zero_init_eq (p : Shape) (ops : Ops α) (t extra : Nat) (s : State α)
    (ht : t < p.groups * 32) (hn : NativeIndices t s) (hp : s.pc t = 3) :
    runLane ops (layout p) (geometry p) program t (extra + 4118) s =
      runLane ops (layout p) (geometry p) program t extra (zeroInit ops t s) := by
  let s1 := setIndex s t 3 0 4
  have he := execute_index_of ops (layout p) (geometry p) t 3 4 (.const 0) s 0 (by rfl) (by omega)
  have h1 := source_step p ops t 3 (extra + 4117) _ s s1 (by rfl) hp he
  have h2 := zero_rows_eq p ops t 0 4 extra s1 ht (by decide)
    (indices_set s t 3 4 0 (by decide) hn) (by simp [s1, setIndex, advance])
    (by simp [s1, setIndex, advance])
  exact h1.trans h2

theorem zero_init_fields (ops : Ops α) (t : Nat) (s : State α) :
    (zeroInit ops t s).pc t = 12 ∧ (zeroInit ops t s).epochs = s.epochs :=
  zero_rows_fields ops t 0 4 (setIndex s t 3 0 4)

theorem zero_init_native (ops : Ops α) (t : Nat) (s : State α) (hn : NativeIndices t s) :
    NativeIndices t (zeroInit ops t s) :=
  zero_rows_native ops t 0 4 _ (indices_set s t 3 4 0 (by decide) hn)

theorem zero_init_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t : Nat) (s : State α) (hr : Reads p input s) : Reads p input (zeroInit ops t s) :=
  zero_rows_reads p ops input t 0 4 (setIndex s t 3 0 4) hr

theorem zero_init_good (ops : Ops α) (t : Nat) (s : State α) (hg : TraceGood s) :
    TraceGood (zeroInit ops t s) := zero_rows_good ops t 0 4 (setIndex s t 3 0 4) (by decide) hg

theorem zero_init_value (ops : Ops α) (t tile col : Nat) (s : State α)
    (hi : tile < 4) (hc : col < 256) :
    (zeroInit ops t s).memory (globalCell 0 (globalAddress t tile col)) = some (zeroValue ops) :=
  zero_rows_value ops t 0 4 tile col (setIndex s t 3 0 4) (by omega) hi hc

theorem zero_init_memory_other (ops : Ops α) (t : Nat) (s : State α) (l : Location)
    (hl : ∀ r, r < 4 → ∀ c, c < 256 → l ≠ globalCell 0 (globalAddress t r c)) :
    (zeroInit ops t s).memory l = s.memory l :=
  zero_rows_memory_other ops t 0 4 (setIndex s t 3 0 4) l (by intro r _ hr c hc; exact hl r hr c hc)

theorem zero_init_other (ops : Ops α) (t u : Nat) (s : State α) (hne : u ≠ t) :
    (zeroInit ops t s).pc u = s.pc u ∧ (zeroInit ops t s).indices u = s.indices u ∧
    (zeroInit ops t s).regs u = s.regs u := by
  have h := zero_rows_other ops t u 0 4 (setIndex s t 3 0 4) hne
  have he : (setIndex s t 3 0 4).pc u = s.pc u ∧
      (setIndex s t 3 0 4).indices u = s.indices u ∧ (setIndex s t 3 0 4).regs u = s.regs u := by
    simp [setIndex, advance, hne]
  exact ⟨h.1.trans he.1, h.2.1.trans he.2.1, h.2.2.trans he.2.2⟩

#print axioms zero_init_eq
#print axioms zero_init_value
#print axioms zero_init_good
end LarkNativeAttention
