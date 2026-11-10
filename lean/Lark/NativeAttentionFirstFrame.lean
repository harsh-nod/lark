import Lark.NativeAttentionFirstLane

/-! Frames needed to schedule all native lanes without disturbing their peers. -/
namespace LarkNativeAttention
open LarkNonlinear
open LarkReduction (setIndex)
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem header_other (t u : Nat) (s : State α) (hne : u ≠ t) :
    (headerState t s).pc u = s.pc u ∧ (headerState t s).indices u = s.indices u ∧
    (headerState t s).regs u = s.regs u := by
  simp [headerState, setIndex, advance, hne]

theorem first_lane_other (ops : Ops α) (input : Nat → Nat → α) (t u : Nat)
    (s : State α) (hne : u ≠ t) :
    (firstLane ops input t s).pc u = s.pc u ∧ (firstLane ops input t s).indices u = s.indices u ∧
    (firstLane ops input t s).regs u = s.regs u := by
  have h1 := header_other t u s hne
  have h2 := zero_init_other ops t u (headerState t s) hne
  have h3 := first_load_other ops input t u (zeroInit ops t (headerState t s)) hne
  exact ⟨h3.1.trans (h2.1.trans h1.1), h3.2.1.trans (h2.2.1.trans h1.2.1),
    h3.2.2.trans (h2.2.2.trans h1.2.2)⟩

theorem first_lane_native (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) :
    NativeIndices t (firstLane ops input t s) :=
  first_load_native ops input t _ (zero_init_native ops t _ (header_fields t s).1)

theorem first_lane_memory_other (ops : Ops α) (input : Nat → Nat → α) (t : Nat)
    (s : State α) (l : Location)
    (hout : ∀ r, r < 4 → ∀ c, c < 256 → l ≠ globalCell 0 (globalAddress t r c))
    (hshared : ∀ c, c < 256 → l ≠ sharedCell t 1 (sharedAddress t c) ∧
      l ≠ sharedCell t 2 (sharedAddress t c)) :
    (firstLane ops input t s).memory l = s.memory l := by
  have h1 := load_columns_memory_other ops input t 0 0 256
    (loadEntry t (zeroInit ops t (headerState t s))) l (by intro c _ hc; exact hshared c hc)
  have h2 := zero_init_memory_other ops t (headerState t s) l hout
  exact h1.trans (h2.trans (congrFun (header_fields t s).2.2.1 l))

theorem first_lane_output_other (ops : Ops α) (input : Nat → Nat → α) (t offset : Nat)
    (s : State α) (hne : writer offset ≠ t) :
    (firstLane ops input t s).memory (globalCell 0 offset) = s.memory (globalCell 0 offset) := by
  apply first_lane_memory_other
  · intro r hr c hc he
    have he := congrArg Location.offset he
    change offset = globalAddress t r c at he
    exact hne ((congrArg writer he).trans (global_address_owner t r c hr hc))
  · intro c hc
    simp [globalCell, sharedCell]

theorem shared_thread_ne (t u b d x y : Nat) (hne : u ≠ t) (hx : x < 256) (hy : y < 256) :
    sharedCell u b (sharedAddress u x) ≠ sharedCell t d (sharedAddress t y) := by
  intro he
  have ho := congrArg Location.owner he
  have hi := congrArg Location.offset he
  simp only [sharedCell, sharedAddress] at ho hi
  omega

theorem first_lane_tile_other (ops : Ops α) (input : Nat → Nat → α) (t u b col : Nat)
    (s : State α) (hne : u ≠ t) (hc : col < 256) :
    (firstLane ops input t s).memory (sharedCell u b (sharedAddress u col)) =
      s.memory (sharedCell u b (sharedAddress u col)) := by
  apply first_lane_memory_other
  · intro r hr c hc
    simp [sharedCell, globalCell]
  · intro c hbound
    exact ⟨shared_thread_ne t u b 1 col c hne hc hbound, shared_thread_ne t u b 2 col c hne hc hbound⟩

#print axioms first_lane_other
#print axioms first_lane_memory_other
#print axioms first_lane_output_other
#print axioms first_lane_tile_other
end LarkNativeAttention
