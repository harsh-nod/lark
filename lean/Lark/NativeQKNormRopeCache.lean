import Lark.NativeQKNormRopeNormalLane

/-! Checked gathered-cache addresses and the actual four-instruction cache
header for either interleaved pair. The cache is a read-only input buffer. -/
namespace LarkNativeQKNormRope
open LarkNonlinear
open LarkReduction (setIndex setReg int32_cast execute_index_of)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def pairCosAddress (t pair : Nat) : Nat := row t * 128 + t % 32 * 2 + pair
def pairSinAddress (t pair : Nat) : Nat := pairCosAddress t pair + 64

theorem pair_cache_bounds (p : Shape) (t pair : Nat) (ht : t < p.rows * 1280) (hp : pair < 2) :
    pairCosAddress t pair < p.rows * 128 ∧ pairSinAddress t pair < p.rows * 128 := by
  have hr := row_bound p t ht
  have hl := Nat.mod_lt t (by decide : 0 < 32)
  simp only [pairCosAddress, pairSinAddress]
  omega

theorem pair_cache_signed (p : Shape) (t pair : Nat) (ht : t < p.rows * 1280) (hp : pair < 2) :
    pairCosAddress t pair < 2147483648 ∧ pairSinAddress t pair < 2147483648 := by
  have hb := pair_cache_bounds p t pair ht hp
  have hs := p.bound
  omega

def pairCacheIndex (pair : Nat) : Index :=
  .add (.add (.mul (.ivar 1) (.const 128)) (.mul (.ivar 3) (.const 2))) (.const (pair : Int))

theorem eval_pair_cache (p : Shape) (t pair : Nat) (s : State α)
    (ht : t < p.rows * 1280) (hp : pair < 2)
    (hr : s.indices t 1 = some ((row t : Nat) : Int))
    (hl : s.indices t 3 = some ((t % 32 : Nat) : Int)) :
    evalIndex (geometry p) t s (pairCacheIndex pair) = some ((pairCosAddress t pair : Nat) : Int) := by
  have bound := (pair_cache_signed p t pair ht hp).1
  have er := eval_nat_mul (geometry p) t s (.ivar 1) (.const 128) (row t) 128 hr rfl
    (by unfold pairCosAddress at bound; omega)
  have el := eval_nat_mul (geometry p) t s (.ivar 3) (.const 2) (t % 32) 2 hl rfl
    (by have := Nat.mod_lt t (by decide : 0 < 32); omega)
  have ea := eval_nat_add (geometry p) t s _ _ (row t * 128) (t % 32 * 2) er el
    (by unfold pairCosAddress at bound; omega)
  exact eval_nat_add (geometry p) t s _ (.const (pair : Int)) _ pair ea
    (int32_cast pair (by omega)) bound

theorem cache_location (p : Shape) (t offset : Nat) (hi : offset < p.rows * 128) :
    location (layout p) (geometry p) t .global 4 (offset : Int) false = some (globalCell 4 offset) := by
  simp [location, layout, globalCell, hi]

theorem execute_cache_load (p : Shape) (ops : Ops α) (t r pc offset index : Nat)
    (s : State α) (value : α) (hi : offset < p.rows * 128)
    (hindex : s.indices t index = some (offset : Int))
    (hm : s.memory (globalCell 4 offset) = some value) (hp : s.pc t + 1 = pc) :
    execute ops (layout p) (geometry p) t (.assign r (.un .fromHalf (.load .global 4 (.ivar index)))) s =
      some (loaded ops t r pc 4 offset value s) := by
  simp only [execute, evalExpr, evalIndex, hindex, cache_location p t offset hi,
    hm, applyUnary, bind, pure, Option.bind]
  simp only [loaded, setReg, advance, record, hp]

def pairCacheAfter (ops : Ops α) (input : Nat → Nat → α) (t pair : Nat) (s : State α) : State α :=
  let s := setIndex s t (15 + 2 * pair) ((pairCosAddress t pair : Nat) : Int) (60 + 10 * pair)
  let s := setIndex s t (16 + 2 * pair) ((pairSinAddress t pair : Nat) : Int) (61 + 10 * pair)
  let s := loaded ops t (25 + 8 * pair) (62 + 10 * pair) 4 (pairCosAddress t pair)
    (input 4 (pairCosAddress t pair)) s
  loaded ops t (26 + 8 * pair) (63 + 10 * pair) 4 (pairSinAddress t pair)
    (input 4 (pairSinAddress t pair)) s

theorem pair_cache_eq (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (t pair extra : Nat)
    (s : State α) (ht : t < p.rows * 1280) (hj : pair < 2) (hp : s.pc t = 59 + 10 * pair)
    (hrow : s.indices t 1 = some ((row t : Nat) : Int))
    (hlane : s.indices t 3 = some ((t % 32 : Nat) : Int)) (hr : Reads p input s) :
    LarkCollective.runLane ops (layout p) (geometry p) (program false) t (extra + 4) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program false) t extra (pairCacheAfter ops input t pair s) := by
  let s1 := setIndex s t (15 + 2 * pair) ((pairCosAddress t pair : Nat) : Int) (60 + 10 * pair)
  let s2 := setIndex s1 t (16 + 2 * pair) ((pairSinAddress t pair : Nat) : Int) (61 + 10 * pair)
  let s3 := loaded ops t (25 + 8 * pair) (62 + 10 * pair) 4 (pairCosAddress t pair) (input 4 (pairCosAddress t pair)) s2
  let s4 := loaded ops t (26 + 8 * pair) (63 + 10 * pair) 4 (pairSinAddress t pair) (input 4 (pairSinAddress t pair)) s3
  have bounds := pair_cache_bounds p t pair ht hj
  have signed := pair_cache_signed p t pair ht hj
  have e1 := execute_index_of ops (layout p) (geometry p) t (15 + 2 * pair) (60 + 10 * pair)
    (pairCacheIndex pair) s _ (eval_pair_cache p t pair s ht hj hrow hlane) (by omega)
  change execute _ _ _ _ _ s = some s1 at e1
  have hc : s1.indices t (15 + 2 * pair) = some ((pairCosAddress t pair : Nat) : Int) := by simp [s1, setIndex, advance]
  have es := eval_nat_add (geometry p) t s1 (.ivar (15 + 2 * pair)) (.const 64)
    (pairCosAddress t pair) 64 hc rfl signed.2
  have e2 := execute_index_of ops (layout p) (geometry p) t (16 + 2 * pair) (61 + 10 * pair)
    (.add (.ivar (15 + 2 * pair)) (.const 64)) s1 _ es (by simp [s1, setIndex, advance] <;> omega)
  change execute _ _ _ _ _ s1 = some s2 at e2
  have e3 := execute_cache_load p ops t (25 + 8 * pair) (62 + 10 * pair) (pairCosAddress t pair) (15 + 2 * pair)
    s2 (input 4 (pairCosAddress t pair)) bounds.1
    (by
      have hn : 15 + 2 * pair ≠ 16 + 2 * pair := by omega
      simp [s2, s1, setIndex, advance, hn])
    (hr.2.2.2 _ bounds.1) (by simp [s2, setIndex, advance] <;> omega)
  change execute _ _ _ _ _ s2 = some s3 at e3
  have e4 := execute_cache_load p ops t (26 + 8 * pair) (63 + 10 * pair) (pairSinAddress t pair) (16 + 2 * pair)
    s3 (input 4 (pairSinAddress t pair)) bounds.2 (by simp [s3, s2, loaded, setReg, setIndex, record, advance])
    (hr.2.2.2 _ bounds.2) (by simp [s3, loaded, setReg, advance] <;> omega)
  change execute _ _ _ _ _ s3 = some s4 at e4
  have choices : pair = 0 ∨ pair = 1 := by omega
  have code1 : (program false)[59 + 10 * pair]? =
      some (.scalar (.index (15 + 2 * pair) (pairCacheIndex pair))) := by
    rcases choices with rfl | rfl <;> decide
  have code2 : (program false)[60 + 10 * pair]? =
      some (.scalar (.index (16 + 2 * pair) (.add (.ivar (15 + 2 * pair)) (.const 64)))) := by
    rcases choices with rfl | rfl <;> decide
  have code3 : (program false)[61 + 10 * pair]? =
      some (.scalar (.assign (25 + 8 * pair) (.un .fromHalf (.load .global 4 (.ivar (15 + 2 * pair)))))) := by
    rcases choices with rfl | rfl <;> decide
  have code4 : (program false)[62 + 10 * pair]? =
      some (.scalar (.assign (26 + 8 * pair) (.un .fromHalf (.load .global 4 (.ivar (16 + 2 * pair)))))) := by
    rcases choices with rfl | rfl <;> decide
  rewrite [scalar_step p false ops t (59 + 10 * pair) (extra + 3) _ s s1 code1 hp e1]
  rewrite [scalar_step p false ops t (60 + 10 * pair) (extra + 2) _ s1 s2
    code2
    (by simp [s1, setIndex, advance]) e2]
  rewrite [scalar_step p false ops t (61 + 10 * pair) (extra + 1) _ s2 s3
    code3
    (by simp [s2, setIndex, advance]) e3]
  rewrite [scalar_step p false ops t (62 + 10 * pair) extra _ s3 s4
    code4
    (by simp [s3, loaded, setReg, advance]) e4]
  rfl

theorem pair_cache_pc (ops : Ops α) (input : Nat → Nat → α) (t pair : Nat) (s : State α) :
    (pairCacheAfter ops input t pair s).pc t = 63 + 10 * pair := by simp [pairCacheAfter, loaded, setReg, advance]

theorem pair_cache_values (ops : Ops α) (input : Nat → Nat → α) (t pair : Nat) (s : State α) :
    (pairCacheAfter ops input t pair s).regs t (25 + 8 * pair) = some (ops.fromHalf (input 4 (pairCosAddress t pair))) ∧
    (pairCacheAfter ops input t pair s).regs t (26 + 8 * pair) = some (ops.fromHalf (input 4 (pairSinAddress t pair))) := by
  have hn : 25 + 8 * pair ≠ 26 + 8 * pair := by omega
  simp [pairCacheAfter, loaded, setReg, record, advance, hn]

theorem pair_cache_low_reg (ops : Ops α) (input : Nat → Nat → α) (t pair r : Nat)
    (s : State α) (hr : r < 25) : (pairCacheAfter ops input t pair s).regs t r = s.regs t r := by
  have hc : r ≠ 25 + 8 * pair := by omega
  have hs : r ≠ 26 + 8 * pair := by omega
  simp [pairCacheAfter, loaded, setReg, record, advance, hc, hs, setIndex]

theorem pair_cache_reg_before (ops : Ops α) (input : Nat → Nat → α) (t pair r : Nat)
    (s : State α) (hr : r < 25 + 8 * pair) : (pairCacheAfter ops input t pair s).regs t r = s.regs t r := by
  have hc : r ≠ 25 + 8 * pair := by omega
  have hs : r ≠ 26 + 8 * pair := by omega
  simp [pairCacheAfter, loaded, setReg, record, advance, hc, hs, setIndex]

theorem pair_cache_low_index (ops : Ops α) (input : Nat → Nat → α) (t pair r : Nat)
    (s : State α) (hr : r < 15) : (pairCacheAfter ops input t pair s).indices t r = s.indices t r := by
  have hc : r ≠ 15 + 2 * pair := by omega
  have hs : r ≠ 16 + 2 * pair := by omega
  simp [pairCacheAfter, loaded, setReg, record, advance, hc, hs, setIndex]

theorem pair_cache_preserves (ops : Ops α) (input : Nat → Nat → α) (t pair : Nat) (s : State α) :
    (pairCacheAfter ops input t pair s).memory = s.memory ∧ (pairCacheAfter ops input t pair s).epochs = s.epochs := ⟨rfl, rfl⟩

theorem pair_cache_trace (ops : Ops α) (input : Nat → Nat → α) (t pair : Nat) (s : State α) :
    (pairCacheAfter ops input t pair s).trace = [
      ⟨t, globalCell 4 (pairSinAddress t pair), false, s.epochs t⟩,
      ⟨t, globalCell 4 (pairCosAddress t pair), false, s.epochs t⟩] ++ s.trace := rfl

theorem pair_cache_good (ops : Ops α) (input : Nat → Nat → α) (t pair : Nat) (s : State α)
    (good : ∀ access ∈ s.trace, Good access) : ∀ access ∈ (pairCacheAfter ops input t pair s).trace, Good access := by
  intro access ha
  rw [pair_cache_trace] at ha
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with (rfl | rfl) | ha
  · exact input_access_good t 4 _ _ ⟨by decide, by decide⟩
  · exact input_access_good t 4 _ _ ⟨by decide, by decide⟩
  · exact good access ha

theorem pair_cache_other (ops : Ops α) (input : Nat → Nat → α) (t pair u : Nat)
    (s : State α) (hu : u ≠ t) :
    (pairCacheAfter ops input t pair s).pc u = s.pc u ∧
    (pairCacheAfter ops input t pair s).indices u = s.indices u ∧
    (pairCacheAfter ops input t pair s).regs u = s.regs u := by
  refine ⟨?_, ?_, ?_⟩
  · simp [pairCacheAfter, loaded, setReg, setIndex, record, advance, hu]
  · funext r; simp [pairCacheAfter, loaded, setReg, setIndex, record, advance, hu]
  · funext r; simp [pairCacheAfter, loaded, setReg, setIndex, record, advance, hu]

#print axioms pair_cache_bounds
#print axioms pair_cache_signed
#print axioms eval_pair_cache
#print axioms cache_location
#print axioms execute_cache_load
#print axioms pair_cache_eq
#print axioms pair_cache_pc
#print axioms pair_cache_values
#print axioms pair_cache_low_reg
#print axioms pair_cache_reg_before
#print axioms pair_cache_low_index
#print axioms pair_cache_preserves
#print axioms pair_cache_trace
#print axioms pair_cache_good
#print axioms pair_cache_other
end LarkNativeQKNormRope
