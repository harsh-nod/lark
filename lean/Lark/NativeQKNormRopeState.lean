import Lark.NativeQKNormRopeAddress
import Lark.Reduction

/-! Scalar operational helpers for the actual out-of-place fused program.
The pinned machine and its signed-index checks are unchanged. -/
namespace LarkNativeQKNormRope
open LarkNonlinear
open LarkReduction (setIndex setReg int32_cast)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def globalCell (buffer offset : Nat) : Location := ⟨.global, 0, buffer, offset⟩

def Reads (p : Shape) (input : Nat → Nat → α) (s : State α) : Prop :=
  (∀ i, i < p.rows * 6144 → s.memory (globalCell 1 i) = some (input 1 i)) ∧
  (∀ i, i < 128 → s.memory (globalCell 2 i) = some (input 2 i)) ∧
  (∀ i, i < 128 → s.memory (globalCell 3 i) = some (input 3 i)) ∧
  (∀ i, i < p.rows * 128 → s.memory (globalCell 4 i) = some (input 4 i))

theorem initial_reads (p : Shape) (input : Nat → Nat → α) (outside : Location → Option α) :
    Reads p input (initial (layout p) input outside) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro i hi <;> simp [initial, layout, globalCell, hi]

theorem scalar_step (p : Shape) (neox : Bool) (ops : Ops α) (t pc extra : Nat)
    (i : LarkNonlinear.Instr) (s next : State α)
    (hi : (program neox)[pc]? = some (.scalar i)) (hp : s.pc t = pc)
    (he : execute ops (layout p) (geometry p) t i s = some next) :
    LarkCollective.runLane ops (layout p) (geometry p) (program neox) t (extra + 1) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program neox) t extra next := by
  have parked : LarkCollective.parked (program neox) s t = none := by
    cases i <;> simp_all [LarkCollective.parked, execute]
  rewrite [LarkCollective.runLane, parked]
  simp only [hp, hi, bind, pure, Option.bind, he]

theorem eval_nat_mul (g : Geometry) (t : Nat) (s : State α) (a b : Index) (x y : Nat)
    (ha : evalIndex g t s a = some (x : Int)) (hb : evalIndex g t s b = some (y : Int))
    (hxy : x * y < 2147483648) :
    evalIndex g t s (.mul a b) = some ((x * y : Nat) : Int) :=
  LarkReduction.eval_mul_of g t s a b (x : Int) (y : Int) _ ha hb
    ((congrArg int32 (Int.natCast_mul x y).symm).trans (int32_cast _ hxy))

theorem eval_nat_add (g : Geometry) (t : Nat) (s : State α) (a b : Index) (x y : Nat)
    (ha : evalIndex g t s a = some (x : Int)) (hb : evalIndex g t s b = some (y : Int))
    (hxy : x + y < 2147483648) :
    evalIndex g t s (.add a b) = some ((x + y : Nat) : Int) :=
  LarkReduction.eval_add_of g t s a b (x : Int) (y : Int) _ ha hb
    ((congrArg int32 (Int.natCast_add x y).symm).trans (int32_cast _ hxy))

theorem eval_nat_div (g : Geometry) (t r x d : Nat) (s : State α)
    (hr : s.indices t r = some (x : Int)) (hd : 0 < d) (hb : d < 2147483648) :
    evalIndex g t s (.div (.ivar r) (.const (d : Int))) = some ((x / d : Nat) : Int) := by
  have hn : ¬ (x : Int) < 0 := by omega
  have hz : ¬ (d : Int) ≤ 0 := by omega
  simp [evalIndex, hr, int32_cast d hb, hn, hz, Int.ofNat_ediv] <;> omega

theorem eval_nat_mod (g : Geometry) (t r x d : Nat) (s : State α)
    (hr : s.indices t r = some (x : Int)) (hd : 0 < d) (hb : d < 2147483648) :
    evalIndex g t s (.mod (.ivar r) (.const (d : Int))) = some ((x % d : Nat) : Int) := by
  have hn : ¬ (x : Int) < 0 := by omega
  have hz : ¬ (d : Int) ≤ 0 := by omega
  simp [evalIndex, hr, int32_cast d hb, hn, hz] <;> omega

theorem eval_nat_div_of (g : Geometry) (t : Nat) (s : State α) (a : Index) (x d : Nat)
    (ha : evalIndex g t s a = some (x : Int)) (hd : 0 < d) (hb : d < 2147483648) :
    evalIndex g t s (.div a (.const (d : Int))) = some ((x / d : Nat) : Int) := by
  have hn : ¬ (x : Int) < 0 := by omega
  have hz : ¬ (d : Int) ≤ 0 := by omega
  simp [evalIndex, ha, int32_cast d hb, hn, hz, Int.ofNat_ediv] <;> omega

theorem eval_nat_mod_of (g : Geometry) (t : Nat) (s : State α) (a : Index) (x d : Nat)
    (ha : evalIndex g t s a = some (x : Int)) (hd : 0 < d) (hb : d < 2147483648) :
    evalIndex g t s (.mod a (.const (d : Int))) = some ((x % d : Nat) : Int) := by
  have hn : ¬ (x : Int) < 0 := by omega
  have hz : ¬ (d : Int) ≤ 0 := by omega
  simp [evalIndex, ha, int32_cast d hb, hn, hz] <;> omega

theorem qkv_location (p : Shape) (t offset : Nat) (hi : offset < p.rows * 6144) :
    location (layout p) (geometry p) t .global 1 (offset : Int) false =
      some (globalCell 1 offset) := by
  simp [location, layout, globalCell, hi]

theorem output_location (p : Shape) (t offset : Nat) (write : Bool) (hi : offset < p.rows * 5120) :
    location (layout p) (geometry p) t .global 0 (offset : Int) write =
      some (globalCell 0 offset) := by
  cases write <;> simp [location, layout, globalCell, hi,
    show (Role.output == Role.input) = false from rfl]

def loaded (ops : Ops α) (t r pc buffer offset : Nat) (value : α) (s : State α) : State α :=
  setReg (record s t (globalCell buffer offset) false) t r (ops.fromHalf value) pc

theorem execute_qkv_load (p : Shape) (ops : Ops α) (t r pc offset index : Nat)
    (s : State α) (value : α) (hi : offset < p.rows * 6144)
    (hindex : s.indices t index = some (offset : Int))
    (hm : s.memory (globalCell 1 offset) = some value) (hp : s.pc t + 1 = pc) :
    execute ops (layout p) (geometry p) t (.assign r (.un .fromHalf (.load .global 1 (.ivar index)))) s =
      some (loaded ops t r pc 1 offset value s) := by
  simp only [execute, evalExpr, evalIndex, hindex, qkv_location p t offset hi,
    hm, applyUnary, bind, pure, Option.bind]
  simp only [loaded, setReg, advance, record, hp]

theorem input_access_good (t buffer offset : Nat) (epoch : Epoch)
    (hb : 1 ≤ buffer ∧ buffer ≤ 4) : Good ⟨t, globalCell buffer offset, false, epoch⟩ :=
  .input rfl rfl hb rfl

#print axioms initial_reads
#print axioms scalar_step
#print axioms eval_nat_mul
#print axioms eval_nat_add
#print axioms eval_nat_div
#print axioms eval_nat_mod
#print axioms eval_nat_div_of
#print axioms eval_nat_mod_of
#print axioms qkv_location
#print axioms output_location
#print axioms execute_qkv_load
#print axioms input_access_good
end LarkNativeQKNormRope
