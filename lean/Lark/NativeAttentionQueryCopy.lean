import Lark.NativeAttentionFirstResume

/-! The source's Q tile copy uses a lane-owned shared row, at PC 25. -/
namespace LarkNativeAttention
open LarkNonlinear
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem query_store_code : program[25]? = some
    (.store .shared 0 (sharedIndex 8) (.un .fromHalf (.load .global 1 (globalIndex 7 8)))) := rfl

theorem query_copy_eq (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t tile col : Nat) (s : State α) (ht : t < p.groups * 32) (hi : tile < 4) (hc : col < 256)
    (hr : Reads p input s) (hn : NativeIndices t s)
    (hrow : s.indices t 7 = some (tile : Int)) (hcol : s.indices t 8 = some (col : Int))
    (hp : s.pc t = 25) :
    execute ops (layout p) (geometry p) t
      (.store .shared 0 (sharedIndex 8) (.un .fromHalf (.load .global 1 (globalIndex 7 8)))) s =
      some (tileCopy ops input t tile col 1 26 s) := by
  have hb : 1 = 1 ∨ 1 = 2 ∨ 1 = 3 := Or.inl rfl
  have hg := global_address_bound p t tile col ht hi hc
  have he := eval_from_half_load_of ops (layout p) (geometry p) t 1 (globalIndex 7 8)
    s (globalAddress t tile col) (globalCell 1 (globalAddress t tile col))
    (input 1 (globalAddress t tile col))
    (eval_global_index p t tile col 7 8 s ht hi hc hn hrow hcol)
    (input_location p t 1 _ hb hg) (hr 1 hb _ hg)
  exact execute_store_of ops (layout p) (geometry p) t 26 .shared 0 (sharedIndex 8) _ s _
    (sharedAddress t col) _ _ (eval_shared_index (geometry p) t 8 col s hc hn.2.1 hcol)
    (shared_location p t 0 _ true (by decide) (shared_address_bound t col hc)) he (by omega)

theorem query_copy_good (ops : Ops α) (input : Nat → Nat → α) (t tile col : Nat)
    (s : State α) (hc : col < 256) (hg : TraceGood s) :
    TraceGood (tileCopy ops input t tile col 1 26 s) := by
  apply store_good
  · intro a ha
    rcases List.mem_cons.mp ha with he | hm
    · subst a
      exact Good.input rfl rfl (by change 1 ≠ 0; decide) rfl
    · exact hg a hm
  · exact qi_access_good t col true (s.epochs t) hc

#print axioms query_copy_eq
#print axioms query_copy_good
end LarkNativeAttention
