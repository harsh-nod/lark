import Lark.NativeSoftmaxFootprint
import Lark.Reduction

/-! Scalar helpers for the actual full native softmax source. The source,
machine definitions and declared execution fuel are unchanged. -/
namespace LarkNativeSoftmax
open LarkNonlinear
open LarkReduction (int32_cast eval_mul_of eval_add_of)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def Reads (p : Shape) (input : Nat → Nat → α) (s : State α) : Prop :=
  ∀ offset, offset < p.rows * 50257 →
    s.memory (globalCell 1 offset) = some (input 1 offset)

theorem initial_reads (p : Shape) (input : Nat → Nat → α)
    (outside : Location → Option α) :
    Reads p input (initial (layout p) input outside) := by
  intro offset hb
  exact initial_places (layout p) input outside 1 offset ⟨.input,p.rows * 50257⟩ rfl rfl hb

theorem scalar_step (p : Shape) (guarded : Bool) (ops : Ops α) (t pc extra : Nat)
    (i : LarkNonlinear.Instr) (s next : State α)
    (hi : (program guarded)[pc]? = some (.scalar i)) (hp : s.pc t = pc)
    (he : execute ops (layout p) (geometry p) t i s = some next) :
    LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t (extra + 1) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t extra next := by
  have parked : LarkCollective.parked (program guarded) s t = none := by
    cases i <;> simp_all [LarkCollective.parked,execute]
  rewrite [LarkCollective.runLane,parked]
  simp only [hp,hi,bind,pure,Option.bind,he]

theorem eval_nat_mul (g : Geometry) (t value factor : Nat) (s : State α) (a : Index)
    (ha : evalIndex g t s a = some (value : Int))
    (hf : factor < 2147483648) (hp : value * factor < 2147483648) :
    evalIndex g t s (.mul a (.const (factor : Int))) = some ((value * factor : Nat) : Int) :=
  eval_mul_of g t s _ _ (value : Int) (factor : Int) _ ha (int32_cast factor hf)
    ((congrArg int32 (Int.natCast_mul value factor).symm).trans (int32_cast _ hp))

theorem eval_nat_sum (g : Geometry) (t x y : Nat) (s : State α) (a b : Index)
    (ha : evalIndex g t s a = some (x : Int)) (hb : evalIndex g t s b = some (y : Int))
    (hs : x + y < 2147483648) :
    evalIndex g t s (.add a b) = some ((x + y : Nat) : Int) :=
  eval_add_of g t s _ _ (x : Int) (y : Int) _ ha hb
    ((congrArg int32 (Int.natCast_add x y).symm).trans (int32_cast _ hs))

theorem eval_address (p : Shape) (t row col : Nat) (s : State α)
    (hr : row < p.rows) (hc : col < 50257)
    (h0 : s.indices t 0 = some (row : Int)) (h6 : s.indices t 6 = some (col : Int)) :
    evalIndex (geometry p) t s (.add (.mul (.ivar 0) (.const 50257)) (.ivar 6)) =
      some ((address row col : Nat) : Int) := by
  have hb := p.bound
  have hmul := eval_nat_mul (geometry p) t row 50257 s (.ivar 0) h0 (by decide) (by omega)
  exact eval_nat_sum (geometry p) t (row * 50257) col s _ _ hmul h6 (by omega)

theorem input_location_of (l : Layout) (g : Geometry) (t buffer offset size : Nat)
    (hl : l.global[buffer]? = some ⟨.input,size⟩) (hi : offset < size) :
    location l g t .global buffer (offset : Int) false = some (globalCell buffer offset) := by
  simp [location,hl,globalCell,hi]

theorem input_location (p : Shape) (t offset : Nat) (hi : offset < p.rows * 50257) :
    location (layout p) (geometry p) t .global 1 (offset : Int) false =
      some (globalCell 1 offset) :=
  input_location_of (layout p) (geometry p) t 1 offset (p.rows * 50257) rfl hi

#print axioms initial_reads
#print axioms scalar_step
#print axioms eval_nat_mul
#print axioms eval_nat_sum
#print axioms eval_address
#print axioms input_location_of
#print axioms input_location
end LarkNativeSoftmax
