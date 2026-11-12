import Lark.NativeQKNormRopeInit

/-! Actual index/load pairs for the four native per-lane input elements. -/
namespace LarkNativeQKNormRope
open LarkNonlinear
open LarkReduction (setIndex setReg int32_cast execute_index_of)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def inputValue (ops : Ops α) (input : Nat → Nat → α) (t e : Nat) : α :=
  ops.fromHalf (input 1 (inputAddress t e))

def loadAt (ops : Ops α) (input : Nat → Nat → α) (t e : Nat) (s : State α) : State α :=
  let s := setIndex s t (7 + e) ((inputAddress t e : Nat) : Int) (8 + 2 * e)
  loaded ops t e (9 + 2 * e) 1 (inputAddress t e) (input 1 (inputAddress t e)) s

theorem input_address_add (t e : Nat) : inputAddress t 0 + e = inputAddress t e := by
  simp only [inputAddress, column]
  omega

theorem load_at_eq (p : Shape) (neox : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (t e extra : Nat) (s : State α) (ht : t < p.rows * 1280) (he : e < 4)
    (hp : s.pc t = 7 + 2 * e)
    (h5 : s.indices t 5 = some ((inputAddress t 0 : Nat) : Int)) (hr : Reads p input s) :
    LarkCollective.runLane ops (layout p) (geometry p) (program neox) t (extra + 2) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program neox) t extra (loadAt ops input t e s) := by
  have hb := input_bound p t e ht he
  have hs := (signed_bounds p t e ht he).1
  let s1 := setIndex s t (7 + e) ((inputAddress t e : Nat) : Int) (8 + 2 * e)
  let s2 := loaded ops t e (9 + 2 * e) 1 (inputAddress t e) (input 1 (inputAddress t e)) s1
  have ea := eval_nat_add (geometry p) t s (.ivar 5) (.const (e : Int)) (inputAddress t 0) e
    h5 (int32_cast e (by omega)) (by rw [input_address_add]; exact hs)
  rw [input_address_add] at ea
  have e1 := execute_index_of ops (layout p) (geometry p) t (7 + e) (8 + 2 * e)
    (.add (.ivar 5) (.const (e : Int))) s _ ea (by omega)
  change execute _ _ _ _ _ s = some s1 at e1
  have e2 := execute_qkv_load p ops t e (9 + 2 * e) (inputAddress t e) (7 + e) s1
    (input 1 (inputAddress t e)) hb (by simp [s1, setIndex, advance])
    (by simpa only [s1, setIndex, advance] using hr.1 _ hb)
    (by simp [s1, setIndex, advance] <;> omega)
  change execute _ _ _ _ _ s1 = some s2 at e2
  have code1 : (program neox)[7 + 2 * e]? =
      some (.scalar (.index (7 + e) (.add (.ivar 5) (.const (e : Int))))) := by
    have hc : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 := by omega
    rcases hc with rfl | rfl | rfl | rfl <;> cases neox <;> decide
  have code2 : (program neox)[8 + 2 * e]? =
      some (.scalar (.assign e (.un .fromHalf (.load .global 1 (.ivar (7 + e)))))) := by
    have hc : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 := by omega
    rcases hc with rfl | rfl | rfl | rfl <;> cases neox <;> decide
  rewrite [scalar_step p neox ops t (7 + 2 * e) (extra + 1) _ s s1 code1 hp e1]
  rewrite [scalar_step p neox ops t (8 + 2 * e) extra _ s1 s2 code2
    (by simp [s1, setIndex, advance]) e2]
  rfl

theorem load_at_pc (ops : Ops α) (input : Nat → Nat → α) (t e : Nat) (s : State α) :
    (loadAt ops input t e s).pc t = 9 + 2 * e := by
  simp [loadAt, loaded, setReg, advance]

theorem load_at_value (ops : Ops α) (input : Nat → Nat → α) (t e : Nat) (s : State α) :
    (loadAt ops input t e s).regs t e = some (inputValue ops input t e) := by
  simp [loadAt, loaded, setReg, advance, inputValue]

theorem load_at_base (ops : Ops α) (input : Nat → Nat → α) (t e : Nat) (s : State α) :
    (loadAt ops input t e s).indices t 5 = s.indices t 5 := by
  have h5 : ¬ (5 : Nat) = 7 + e := by omega
  simp [loadAt, loaded, setIndex, setReg, record, advance, h5]

theorem load_at_memory (ops : Ops α) (input : Nat → Nat → α) (t e : Nat) (s : State α) :
    (loadAt ops input t e s).memory = s.memory := rfl

theorem load_at_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (t e : Nat)
    (s : State α) (hr : Reads p input s) : Reads p input (loadAt ops input t e s) := hr

theorem load_at_trace (ops : Ops α) (input : Nat → Nat → α) (t e : Nat) (s : State α) :
    (loadAt ops input t e s).trace = ⟨t, globalCell 1 (inputAddress t e), false, s.epochs t⟩ :: s.trace := rfl

theorem load_at_good (ops : Ops α) (input : Nat → Nat → α) (t e : Nat) (s : State α)
    (good : ∀ a ∈ s.trace, Good a) : ∀ a ∈ (loadAt ops input t e s).trace, Good a := by
  intro a ha
  rw [load_at_trace] at ha
  rcases List.mem_cons.mp ha with rfl | ha
  · exact input_access_good t 1 (inputAddress t e) (s.epochs t) ⟨by decide, by decide⟩
  · exact good a ha

#print axioms input_address_add
#print axioms load_at_eq
#print axioms load_at_pc
#print axioms load_at_value
#print axioms load_at_base
#print axioms load_at_memory
#print axioms load_at_reads
#print axioms load_at_trace
#print axioms load_at_good
end LarkNativeQKNormRope
