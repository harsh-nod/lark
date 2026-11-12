import Lark.NativeQKNormRopeCache
import Lark.NativeQKNormRopeSplitSign

/-! Actual gathered cosine/sine cache headers for all four split-half outputs.
Addresses retain the source's column-mod64 rule and signed index checks. -/
namespace LarkNativeQKNormRope
open LarkNonlinear
open LarkReduction (setIndex setReg int32_cast execute_index_of)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def splitCosAddress (t e : Nat) : Nat := row t * 128 + column t e % 64
def splitSinAddress (t e : Nat) : Nat := splitCosAddress t e + 64

theorem split_cache_bounds (p : Shape) (t e : Nat) (ht : t < p.rows * 1280) :
    splitCosAddress t e < p.rows * 128 ∧ splitSinAddress t e < p.rows * 128 := by
  have hr := row_bound p t ht
  have hc := Nat.mod_lt (column t e) (by decide : 0 < 64)
  simp only [splitCosAddress, splitSinAddress]
  omega

theorem split_cache_signed (p : Shape) (t e : Nat) (ht : t < p.rows * 1280) :
    splitCosAddress t e < 2147483648 ∧ splitSinAddress t e < 2147483648 := by
  have hb := split_cache_bounds p t e ht
  have hs := p.bound
  omega

def splitCacheIndex (e : Nat) : Index :=
  .add (.mul (.ivar 1) (.const 128)) (.mod (.add (.ivar 4) (.const (e : Int))) (.const 64))

theorem eval_split_cache (p : Shape) (t e : Nat) (s : State α)
    (ht : t < p.rows * 1280) (he : e < 4)
    (hr : s.indices t 1 = some ((row t : Nat) : Int))
    (hcol : s.indices t 4 = some ((column t 0 : Nat) : Int)) :
    evalIndex (geometry p) t s (splitCacheIndex e) = some ((splitCosAddress t e : Nat) : Int) := by
  have bound := (split_cache_signed p t e ht).1
  have er := eval_nat_mul (geometry p) t s (.ivar 1) (.const 128) (row t) 128 hr rfl
    (by unfold splitCosAddress at bound; omega)
  have col : column t 0 + e < 128 := by
    unfold column
    have hl := Nat.mod_lt t (by decide : 0 < 32)
    omega
  have ea := eval_nat_add (geometry p) t s (.ivar 4) (.const (e : Int)) (column t 0) e
    hcol (int32_cast e (by omega)) (by omega)
  have ceq : column t 0 + e = column t e := by unfold column; omega
  rw [ceq] at ea
  have em := eval_nat_mod_of (geometry p) t s _ (column t e) 64 ea (by decide) (by decide)
  exact eval_nat_add (geometry p) t s _ _ _ _ er em bound

def splitCacheAfter (ops : Ops α) (input : Nat → Nat → α) (t e : Nat) (s : State α) : State α :=
  let s := setIndex s t (15 + 2 * e) ((splitCosAddress t e : Nat) : Int) (70 + 7 * e)
  let s := setIndex s t (16 + 2 * e) ((splitSinAddress t e : Nat) : Int) (71 + 7 * e)
  let s := loaded ops t (29 + 5 * e) (72 + 7 * e) 4 (splitCosAddress t e)
    (input 4 (splitCosAddress t e)) s
  loaded ops t (30 + 5 * e) (73 + 7 * e) 4 (splitSinAddress t e)
    (input 4 (splitSinAddress t e)) s

theorem split_cache_eq (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (t e extra : Nat)
    (s : State α) (ht : t < p.rows * 1280) (hj : e < 4) (hp : s.pc t = 69 + 7 * e)
    (hrow : s.indices t 1 = some ((row t : Nat) : Int))
    (hcol : s.indices t 4 = some ((column t 0 : Nat) : Int)) (hr : Reads p input s) :
    LarkCollective.runLane ops (layout p) (geometry p) (program true) t (extra + 4) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program true) t extra (splitCacheAfter ops input t e s) := by
  let s1 := setIndex s t (15 + 2 * e) ((splitCosAddress t e : Nat) : Int) (70 + 7 * e)
  let s2 := setIndex s1 t (16 + 2 * e) ((splitSinAddress t e : Nat) : Int) (71 + 7 * e)
  let s3 := loaded ops t (29 + 5 * e) (72 + 7 * e) 4 (splitCosAddress t e) (input 4 (splitCosAddress t e)) s2
  let s4 := loaded ops t (30 + 5 * e) (73 + 7 * e) 4 (splitSinAddress t e) (input 4 (splitSinAddress t e)) s3
  have bounds := split_cache_bounds p t e ht
  have signed := split_cache_signed p t e ht
  have e1 := execute_index_of ops (layout p) (geometry p) t (15 + 2 * e) (70 + 7 * e)
    (splitCacheIndex e) s _ (eval_split_cache p t e s ht hj hrow hcol) (by omega)
  change execute _ _ _ _ _ s = some s1 at e1
  have hc : s1.indices t (15 + 2 * e) = some ((splitCosAddress t e : Nat) : Int) := by simp [s1, setIndex, advance]
  have es := eval_nat_add (geometry p) t s1 (.ivar (15 + 2 * e)) (.const 64)
    (splitCosAddress t e) 64 hc rfl signed.2
  have e2 := execute_index_of ops (layout p) (geometry p) t (16 + 2 * e) (71 + 7 * e)
    (.add (.ivar (15 + 2 * e)) (.const 64)) s1 _ es (by simp [s1, setIndex, advance] <;> omega)
  change execute _ _ _ _ _ s1 = some s2 at e2
  have e3 := execute_cache_load p ops t (29 + 5 * e) (72 + 7 * e) (splitCosAddress t e) (15 + 2 * e)
    s2 (input 4 (splitCosAddress t e)) bounds.1
    (by
      have hn : 15 + 2 * e ≠ 16 + 2 * e := by omega
      simp [s2, s1, setIndex, advance, hn])
    (hr.2.2.2 _ bounds.1) (by simp [s2, setIndex, advance] <;> omega)
  change execute _ _ _ _ _ s2 = some s3 at e3
  have e4 := execute_cache_load p ops t (30 + 5 * e) (73 + 7 * e) (splitSinAddress t e) (16 + 2 * e)
    s3 (input 4 (splitSinAddress t e)) bounds.2 (by simp [s3, s2, loaded, setReg, setIndex, record, advance])
    (hr.2.2.2 _ bounds.2) (by simp [s3, loaded, setReg, advance] <;> omega)
  change execute _ _ _ _ _ s3 = some s4 at e4
  have choices : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 := by omega
  have code1 : (program true)[69 + 7 * e]? =
      some (.scalar (.index (15 + 2 * e) (splitCacheIndex e))) := by
    rcases choices with rfl | rfl | rfl | rfl <;> decide
  have code2 : (program true)[70 + 7 * e]? =
      some (.scalar (.index (16 + 2 * e) (.add (.ivar (15 + 2 * e)) (.const 64)))) := by
    rcases choices with rfl | rfl | rfl | rfl <;> decide
  have code3 : (program true)[71 + 7 * e]? =
      some (.scalar (.assign (29 + 5 * e) (.un .fromHalf (.load .global 4 (.ivar (15 + 2 * e)))))) := by
    rcases choices with rfl | rfl | rfl | rfl <;> decide
  have code4 : (program true)[72 + 7 * e]? =
      some (.scalar (.assign (30 + 5 * e) (.un .fromHalf (.load .global 4 (.ivar (16 + 2 * e)))))) := by
    rcases choices with rfl | rfl | rfl | rfl <;> decide
  rewrite [scalar_step p true ops t (69 + 7 * e) (extra + 3) _ s s1 code1 hp e1]
  rewrite [scalar_step p true ops t (70 + 7 * e) (extra + 2) _ s1 s2
    code2
    (by simp [s1, setIndex, advance]) e2]
  rewrite [scalar_step p true ops t (71 + 7 * e) (extra + 1) _ s2 s3
    code3
    (by simp [s2, setIndex, advance]) e3]
  rewrite [scalar_step p true ops t (72 + 7 * e) extra _ s3 s4
    code4
    (by simp [s3, loaded, setReg, advance]) e4]
  rfl

theorem split_cache_pc (ops : Ops α) (input : Nat → Nat → α) (t e : Nat) (s : State α) :
    (splitCacheAfter ops input t e s).pc t = 73 + 7 * e := by simp [splitCacheAfter, loaded, setReg, advance]

theorem split_cache_values (ops : Ops α) (input : Nat → Nat → α) (t e : Nat) (s : State α) :
    (splitCacheAfter ops input t e s).regs t (29 + 5 * e) = some (ops.fromHalf (input 4 (splitCosAddress t e))) ∧
    (splitCacheAfter ops input t e s).regs t (30 + 5 * e) = some (ops.fromHalf (input 4 (splitSinAddress t e))) := by
  have hn : 29 + 5 * e ≠ 30 + 5 * e := by omega
  simp [splitCacheAfter, loaded, setReg, record, advance, hn]

theorem split_cache_low_reg (ops : Ops α) (input : Nat → Nat → α) (t e r : Nat)
    (s : State α) (hr : r < 29) : (splitCacheAfter ops input t e s).regs t r = s.regs t r := by
  have hc : r ≠ 29 + 5 * e := by omega
  have hs : r ≠ 30 + 5 * e := by omega
  simp [splitCacheAfter, loaded, setReg, record, advance, hc, hs, setIndex]

theorem split_cache_reg_before (ops : Ops α) (input : Nat → Nat → α) (t e r : Nat)
    (s : State α) (hr : r < 29 + 5 * e) : (splitCacheAfter ops input t e s).regs t r = s.regs t r := by
  have hc : r ≠ 29 + 5 * e := by omega
  have hs : r ≠ 30 + 5 * e := by omega
  simp [splitCacheAfter, loaded, setReg, record, advance, hc, hs, setIndex]

theorem split_cache_low_index (ops : Ops α) (input : Nat → Nat → α) (t e r : Nat)
    (s : State α) (hr : r < 15) : (splitCacheAfter ops input t e s).indices t r = s.indices t r := by
  have hc : r ≠ 15 + 2 * e := by omega
  have hs : r ≠ 16 + 2 * e := by omega
  simp [splitCacheAfter, loaded, setReg, record, advance, hc, hs, setIndex]

theorem split_cache_preserves (ops : Ops α) (input : Nat → Nat → α) (t e : Nat) (s : State α) :
    (splitCacheAfter ops input t e s).memory = s.memory ∧ (splitCacheAfter ops input t e s).epochs = s.epochs := ⟨rfl, rfl⟩

theorem split_cache_trace (ops : Ops α) (input : Nat → Nat → α) (t e : Nat) (s : State α) :
    (splitCacheAfter ops input t e s).trace = [
      ⟨t, globalCell 4 (splitSinAddress t e), false, s.epochs t⟩,
      ⟨t, globalCell 4 (splitCosAddress t e), false, s.epochs t⟩] ++ s.trace := rfl

theorem split_cache_good (ops : Ops α) (input : Nat → Nat → α) (t e : Nat) (s : State α)
    (good : ∀ access ∈ s.trace, Good access) : ∀ access ∈ (splitCacheAfter ops input t e s).trace, Good access := by
  intro access ha
  rw [split_cache_trace] at ha
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with (rfl | rfl) | ha
  · exact input_access_good t 4 _ _ ⟨by decide, by decide⟩
  · exact input_access_good t 4 _ _ ⟨by decide, by decide⟩
  · exact good access ha

theorem split_cache_other (ops : Ops α) (input : Nat → Nat → α) (t e u : Nat)
    (s : State α) (hu : u ≠ t) :
    (splitCacheAfter ops input t e s).pc u = s.pc u ∧
    (splitCacheAfter ops input t e s).indices u = s.indices u ∧
    (splitCacheAfter ops input t e s).regs u = s.regs u := by
  refine ⟨?_, ?_, ?_⟩
  · simp [splitCacheAfter, loaded, setReg, setIndex, record, advance, hu]
  · funext r; simp [splitCacheAfter, loaded, setReg, setIndex, record, advance, hu]
  · funext r; simp [splitCacheAfter, loaded, setReg, setIndex, record, advance, hu]

#print axioms split_cache_bounds
#print axioms split_cache_signed
#print axioms eval_split_cache
#print axioms split_cache_eq
#print axioms split_cache_pc
#print axioms split_cache_values
#print axioms split_cache_low_reg
#print axioms split_cache_reg_before
#print axioms split_cache_low_index
#print axioms split_cache_preserves
#print axioms split_cache_trace
#print axioms split_cache_good
#print axioms split_cache_other
end LarkNativeQKNormRope
