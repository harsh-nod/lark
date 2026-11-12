import Lark.NativeQKNormRopeInterleaved

/-! Actual out-of-place FP16 stores for both native source layouts. -/
namespace LarkNativeQKNormRope
open LarkNonlinear
open LarkReduction (setIndex execute_index_of int32_cast)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def storeStart (neox : Bool) : Nat := if neox then 98 else 79
def storeIndexBase (neox : Bool) : Nat := if neox then 23 else 19
def outputRegister (neox : Bool) (e : Nat) : Nat :=
  if neox then 33 + 5 * e else 31 + 8 * (e / 2) + e % 2

def outputWritten (t pc offset : Nat) (value : α) (s : State α) : State α :=
  let s := record s t (globalCell 0 offset) true
  advance { s with memory := fun loc => if loc = globalCell 0 offset then some value else s.memory loc } t pc

theorem output_written_memory (t pc offset : Nat) (value : α) (s : State α) (loc : Location) :
    (outputWritten t pc offset value s).memory loc =
      if loc = globalCell 0 offset then some value else s.memory loc := rfl

theorem output_written_reads (p : Shape) (input : Nat → Nat → α) (t pc offset : Nat)
    (value : α) (s : State α) (hr : Reads p input s) : Reads p input (outputWritten t pc offset value s) := by
  have frame : ∀ buffer i, buffer ≠ 0 →
      (outputWritten t pc offset value s).memory (globalCell buffer i) = s.memory (globalCell buffer i) := by
    intro buffer i hb
    rw [output_written_memory]
    have hn : globalCell buffer i ≠ globalCell 0 offset := by
      intro he
      exact hb (congrArg Location.buffer he)
    simp only [hn, if_false]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi; exact (frame 1 i (by decide)).trans (hr.1 i hi)
  · intro i hi; exact (frame 2 i (by decide)).trans (hr.2.1 i hi)
  · intro i hi; exact (frame 3 i (by decide)).trans (hr.2.2.1 i hi)
  · intro i hi; exact (frame 4 i (by decide)).trans (hr.2.2.2 i hi)

def storeAt (ops : Ops α) (neox : Bool) (t e : Nat) (value : α) (s : State α) : State α :=
  let s := setIndex s t (storeIndexBase neox + e) ((outputAddress t e : Nat) : Int) (storeStart neox + 2 * e + 1)
  outputWritten t (storeStart neox + 2 * e + 2) (outputAddress t e) (ops.toHalf value) s

theorem output_address_add (t e : Nat) : outputAddress t 0 + e = outputAddress t e := by
  rw [output_linear, output_linear]
  omega

theorem store_at_eq (p : Shape) (neox : Bool) (ops : Ops α) (t e extra : Nat) (value : α)
    (s : State α) (ht : t < p.rows * 1280) (he : e < 4) (hp : s.pc t = storeStart neox + 2 * e)
    (hi : s.indices t 6 = some ((outputAddress t 0 : Nat) : Int))
    (hv : s.regs t (outputRegister neox e) = some value) :
    LarkCollective.runLane ops (layout p) (geometry p) (program neox) t (extra + 2) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program neox) t extra (storeAt ops neox t e value s) := by
  have hb := output_bound p t e ht he
  have hs := (signed_bounds p t e ht he).2
  let s1 := setIndex s t (storeIndexBase neox + e) ((outputAddress t e : Nat) : Int) (storeStart neox + 2 * e + 1)
  let s2 := outputWritten t (storeStart neox + 2 * e + 2) (outputAddress t e) (ops.toHalf value) s1
  have ix := eval_nat_add (geometry p) t s (.ivar 6) (.const (e : Int)) (outputAddress t 0) e
    hi (int32_cast e (by omega)) (by rw [output_address_add]; exact hs)
  rw [output_address_add] at ix
  have e1 := execute_index_of ops (layout p) (geometry p) t (storeIndexBase neox + e)
    (storeStart neox + 2 * e + 1) (.add (.ivar 6) (.const (e : Int))) s _ ix (by omega)
  change execute _ _ _ _ _ s = some s1 at e1
  have addr : s1.indices t (storeIndexBase neox + e) = some ((outputAddress t e : Nat) : Int) := by
    simp [s1, setIndex, advance]
  have val : s1.regs t (outputRegister neox e) = some value := hv
  have ex : evalExpr ops (layout p) (geometry p) t (.un .toHalf (.reg (outputRegister neox e))) s1 =
      some (ops.toHalf value, s1) := by simp [evalExpr, applyUnary, val]
  have e2 : execute ops (layout p) (geometry p) t
      (.store .global 0 (.ivar (storeIndexBase neox + e)) (.un .toHalf (.reg (outputRegister neox e)))) s1 = some s2 := by
    simp only [execute, evalIndex, addr, output_location p t (outputAddress t e) true hb, ex, bind, pure, Option.bind]
    rw [show s1.pc t + 1 = storeStart neox + 2 * e + 2 by simp [s1, setIndex, advance] <;> omega]
    rfl
  have choices : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 := by omega
  have code1 : (program neox)[storeStart neox + 2 * e]? =
      some (.scalar (.index (storeIndexBase neox + e) (.add (.ivar 6) (.const (e : Int))))) := by
    rcases choices with rfl | rfl | rfl | rfl <;> cases neox <;> decide
  have code2 : (program neox)[storeStart neox + 2 * e + 1]? = some (.scalar
      (.store .global 0 (.ivar (storeIndexBase neox + e)) (.un .toHalf (.reg (outputRegister neox e))))) := by
    rcases choices with rfl | rfl | rfl | rfl <;> cases neox <;> decide
  rewrite [scalar_step p neox ops t (storeStart neox + 2 * e) (extra + 1) _ s s1 code1 hp e1]
  rewrite [scalar_step p neox ops t (storeStart neox + 2 * e + 1) extra _ s1 s2 code2
    (by simp [s1, setIndex, advance]) e2]
  rfl

theorem store_at_pc (ops : Ops α) (neox : Bool) (t e : Nat) (value : α) (s : State α) :
    (storeAt ops neox t e value s).pc t = storeStart neox + 2 * e + 2 := by
  simp [storeAt, outputWritten, advance]

theorem store_at_preserves (ops : Ops α) (neox : Bool) (t e : Nat) (value : α) (s : State α) :
    (storeAt ops neox t e value s).regs = s.regs ∧ (storeAt ops neox t e value s).epochs = s.epochs := ⟨rfl, rfl⟩

theorem store_at_low_index (ops : Ops α) (neox : Bool) (t e r : Nat) (value : α)
    (s : State α) (hr : r < 19) : (storeAt ops neox t e value s).indices t r = s.indices t r := by
  have hn : r ≠ storeIndexBase neox + e := by cases neox <;> simp only [storeIndexBase, Bool.false_eq_true, if_false, if_true] <;> omega
  simp [storeAt, outputWritten, setIndex, record, advance, hn]

theorem store_at_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (neox : Bool)
    (t e : Nat) (value : α) (s : State α) (hr : Reads p input s) : Reads p input (storeAt ops neox t e value s) :=
  output_written_reads p input t _ _ _ _ hr

theorem store_at_trace (ops : Ops α) (neox : Bool) (t e : Nat) (value : α) (s : State α) :
    (storeAt ops neox t e value s).trace = ⟨t, globalCell 0 (outputAddress t e), true, s.epochs t⟩ :: s.trace := rfl

theorem store_at_good (ops : Ops α) (neox : Bool) (t e : Nat) (value : α) (s : State α)
    (he : e < 4) (good : ∀ access ∈ s.trace, Good access) :
    ∀ access ∈ (storeAt ops neox t e value s).trace, Good access := by
  intro access ha
  rw [store_at_trace] at ha
  rcases List.mem_cons.mp ha with rfl | ha
  · exact .output rfl rfl rfl (output_owner t e he).symm
  · exact good access ha

theorem store_at_memory (ops : Ops α) (neox : Bool) (t e : Nat) (value : α) (s : State α) (loc : Location) :
    (storeAt ops neox t e value s).memory loc =
      if loc = globalCell 0 (outputAddress t e) then some (ops.toHalf value) else s.memory loc := rfl

theorem store_at_other (ops : Ops α) (neox : Bool) (t e u : Nat) (value : α)
    (s : State α) (hu : u ≠ t) :
    (storeAt ops neox t e value s).pc u = s.pc u ∧ (storeAt ops neox t e value s).indices u = s.indices u := by
  constructor
  · simp [storeAt, outputWritten, setIndex, record, advance, hu]
  · funext r; simp [storeAt, outputWritten, setIndex, record, advance, hu]

#print axioms output_written_memory
#print axioms output_written_reads
#print axioms output_address_add
#print axioms store_at_eq
#print axioms store_at_pc
#print axioms store_at_preserves
#print axioms store_at_low_index
#print axioms store_at_reads
#print axioms store_at_trace
#print axioms store_at_good
#print axioms store_at_memory
#print axioms store_at_other
end LarkNativeQKNormRope
